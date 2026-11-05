/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.StableTailDependence
import ExtremeValueTheory.Statistics.OrderStatistics
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Nonparametric estimation of the stable tail dependence function

Let `X_0, X_1, …` be iid random vectors in `ℝ^ι` with law `μ` and continuous marginals
`F_j`, and let `R_i^j = #{m < n | X_m^j ≤ X_i^j}` be the rank of `X_i^j` among
`X_0^j, …, X_{n-1}^j`. The **empirical stable tail dependence function** is

  `ℓ̂_n(x) = (1/k) ∑_{i<n} 1{R_i^1 > n - k x_1 or … or R_i^d > n - k x_d}`

([Huang 1992]; [Drees–Huang 1998]; [dHF, §7.2]; [BGST04, §9.4.1]). It is built from the ranks
only: it estimates the marginals by their empirical distribution functions, so no knowledge of the
`F_j` is needed. Other conventions in the literature replace `n - k x_j` by `n + 1/2 - k x_j`, or
use the order statistics, `X_i^j ≥ X^j_{n-⌊k x_j⌋+1,n}`. All of them are `ℓ̂_n` at a point
`y_n → x`, so `tendstoInMeasure_empiricalStableTailDependence_of_tendsto` covers them, and the
order-statistics form has its own definition and theorem.

## Main results

* `tendstoInMeasure_empiricalStableTailDependence`: **weak consistency** ([dHF, §7.2];
  [Huang 1992]; [Drees–Huang 1998]): if `μ` has continuous marginals and stable tail dependence
  function `ℓ`, and `k = k(n) → ∞`, `k / n → 0`, then `ℓ̂_n(x) → ℓ(x)` in probability for every
  `x ∈ (0, ∞)^ι`. Any finite dimension `d = |ι|` is allowed.
* `tendsto_measure_exists_abs_empiricalStableTailDependence_sub`: **uniform** weak consistency on
  the boxes `(0, T]^ι`.
* `tendstoInMeasure_empiricalStableTailDependence_of_tendsto`: consistency along `y_n → x`.
* `empiricalStableTailDependenceOrderStat_eq`,
  `tendstoInMeasure_empiricalStableTailDependenceOrderStat`:
  the form with order statistics (`orderStat`, through `exceedCount`: `card_lt_eq_exceedCount`).
* `IsMDAWith.tendstoInMeasure_empiricalStableTailDependence`,
  `IsMDAWith.tendsto_measure_exists_abs_empiricalStableTailDependence_sub`: the same under the
  multivariate domain of attraction condition, with `ℓ(x) = V₀(1/x)`.
* `IsMDAWith.tendstoInMeasure_tailDependenceEstimator`: the estimator `χ̂ = 2 - ℓ̂_n(1, 1)` of the
  upper tail dependence coefficient `χ = 2 - ℓ(1, 1)` is consistent.
* `IsMDAWith.tendstoInMeasure_pickandsRankEstimator`: the rank-based estimator
  `Â_n(t) = ℓ̂_n(t, 1 - t)` of the Pickands dependence function is consistent.

## Proof

1. *Known margins.* With the uniform variables `U_i^j = F_j(X_i^j)`, the count
   `T_n(x) = (1/k) #{i < n | ∃ j, U_i^j > 1 - (k/n) x_j}` is a binomial count with mean
   `(n/k) P(∃ j, F_j(X_j) > 1 - (k/n) x_j) → ℓ(x)` and variance `≤ (1/k) × mean → 0`, so
   `T_n(x) → ℓ(x)` in probability by Chebyshev (`tendsto_measure_abs_card_div_sub`).
   In dimension one this is the consistency of the uniform tail empirical distribution function,
   `(1/k) #{i < n | U_i^j > 1 - (k/n) s} → s`.
2. *Estimated margins.* Deterministically (`card_le_empiricalTailCount`,
   `empiricalTailCount_le_card`), if the marginal tail counts satisfy
   `#{m | U_m^j > 1 - (k/n)(x_j - δ)} ≤ k x_j ≤ #{m | U_m^j > 1 - (k/n)(x_j + δ)}` for all `j`,
   then `T_n(x - δ) ≤ ℓ̂_n(x) ≤ T_n(x + δ)`. Only the monotonicity of the `F_j` is used, so
   ties are harmless. By step 1 these conditions hold with probability tending to one, and by
   the Lipschitz continuity of `ℓ` (`HasStableTailDependence.abs_sub_le`) the bounds are within
   `|ι| δ` of `ℓ(x)`.

## References

* [L. de Haan, A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006), §7.2]
  [dHF]
* [X. Huang, *Statistics of bivariate extreme values*, PhD thesis, Erasmus University Rotterdam
  (1992)]
* [H. Drees, X. Huang, *Best attainable rates of convergence for estimators of the stable tail
  dependence function*, J. Multivariate Anal. 64 (1998)]
* [J. Beirlant, Y. Goegebeur, J. Segers, J. Teugels, *Statistics of Extremes*, Wiley (2004),
  §9.4] [BGST04]

## Not in this file

Asymptotic normality of `ℓ̂_n` needs a second-order condition and is not proved here. Pickands'
1981 estimator with known margins is `pickandsDependenceEstimator` in
`Multivariate/PickandsEstimator.lean`, a different estimator from `pickandsRankEstimator` here.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open Set (Ioi Ioo mem_setOf_eq mem_iUnion)

namespace ExtremeValueTheory

/-! ### Deterministic part -/

section Deterministic

variable {ι : Type*} [Fintype ι]

/-- The rank `#{m < n | x_m ≤ x_i}` of `x_i` among `x_0, …, x_{n-1}`. -/
noncomputable def sampleRank (x : ℕ → ℝ) (n i : ℕ) : ℕ := #{m ∈ range n | x m ≤ x i}

open scoped Classical in
/-- The number of observations `i < n` with `R_i^j > n - k x_j` for some coordinate `j`, where
`R_i^j` is the rank of `X_i^j` in the `j`-th coordinate sample. -/
noncomputable def empiricalTailCount (X : ℕ → ι → ℝ) (n k : ℕ) (x : ι → ℝ) : ℕ :=
  #{i ∈ range n | ∃ j, (n : ℝ) - k * x j < sampleRank (fun m ↦ X m j) n i}

/-- The **empirical stable tail dependence function**
`ℓ̂_n(x) = (1/k) ∑_{i<n} 1{∃ j, R_i^j > n - k x_j}` ([Huang 1992]; [Drees–Huang 1998];
[dHF, §7.2]; [BGST04, §9.4.1]), where `R_i^j = #{m < n | X_m^j ≤ X_i^j}`. -/
noncomputable def empiricalStableTailDependence (X : ℕ → ι → ℝ) (n k : ℕ) (x : ι → ℝ) : ℝ :=
  (k : ℝ)⁻¹ * empiricalTailCount X n k x

/-- `R_i > n - c` iff fewer than `c` of the observations are strictly larger than `x_i`. -/
lemma sub_lt_sampleRank_iff (x : ℕ → ℝ) (n i : ℕ) (c : ℝ) :
    (n : ℝ) - c < sampleRank x n i ↔ (#{m ∈ range n | x i < x m} : ℝ) < c := by
  have h := card_filter_add_card_filter_not (s := range n) (fun m ↦ x m ≤ x i)
  simp only [not_le, card_range] at h
  have h' : (sampleRank x n i : ℝ) + #{m ∈ range n | x i < x m} = n := by
    rw [sampleRank]; exact_mod_cast h
  constructor <;> intro hc <;> linarith

open scoped Classical in
lemma empiricalTailCount_eq (X : ℕ → ι → ℝ) (n k : ℕ) (x : ι → ℝ) :
    empiricalTailCount X n k x =
      #{i ∈ range n | ∃ j, (#{m ∈ range n | X i j < X m j} : ℝ) < k * x j} := by
  rw [empiricalTailCount]
  congr 1
  ext i
  simp only [mem_filter]
  constructor <;> rintro ⟨hi, j, hj⟩ <;> refine ⟨hi, j, ?_⟩
  · exact (sub_lt_sampleRank_iff (fun m ↦ X m j) n i _).1 hj
  · exact (sub_lt_sampleRank_iff (fun m ↦ X m j) n i _).2 hj

open scoped Classical in
/-- **Lower sandwich**: if the marginal exceedance counts of the levels `a_j` (on the scale of
the monotone transforms `F_j`) are at most `k x_j`, then every joint exceedance of the levels
`a` is counted by `ℓ̂_n(x)`. -/
theorem card_le_empiricalTailCount {F : ι → ℝ → ℝ} (hF : ∀ j, Monotone (F j))
    (X : ℕ → ι → ℝ) (n k : ℕ) (x a : ι → ℝ)
    (ha : ∀ j, (#{m ∈ range n | a j < F j (X m j)} : ℝ) ≤ k * x j) :
    #{i ∈ range n | ∃ j, a j < F j (X i j)} ≤ empiricalTailCount X n k x := by
  rw [empiricalTailCount_eq]
  refine card_le_card fun i hi ↦ ?_
  simp only [mem_filter] at hi ⊢
  obtain ⟨hin, j, hj⟩ := hi
  refine ⟨hin, j, lt_of_lt_of_le ?_ (ha j)⟩
  have hsub : {m ∈ range n | X i j < X m j} ⊆ {m ∈ range n | a j < F j (X m j)} := by
    intro m hm
    simp only [mem_filter] at hm ⊢
    exact ⟨hm.1, hj.trans_le (hF j hm.2.le)⟩
  have hss : {m ∈ range n | X i j < X m j} ⊂ {m ∈ range n | a j < F j (X m j)} :=
    (ssubset_iff_of_subset hsub).2 ⟨i, by simp [hin, hj], by simp⟩
  exact_mod_cast card_lt_card hss

/-- If at least `c` observations exceed the level `b` on the scale of the monotone `F`, then an
observation with fewer than `c` strictly larger observations exceeds `b` too. -/
lemma lt_apply_of_card_lt_of_le_card {F : ℝ → ℝ} (hF : Monotone F) (x : ℕ → ℝ) (n i : ℕ) {b c : ℝ}
    (hb : c ≤ #{m ∈ range n | b < F (x m)}) (hi : (#{m ∈ range n | x i < x m} : ℝ) < c) :
    b < F (x i) := by
  by_contra hcon
  have hsub : {m ∈ range n | b < F (x m)} ⊆ {m ∈ range n | x i < x m} := by
    intro m hm
    simp only [mem_filter] at hm ⊢
    refine ⟨hm.1, ?_⟩
    by_contra h
    exact hcon (hm.2.trans_le (hF (not_lt.1 h)))
  have hle : (#{m ∈ range n | b < F (x m)} : ℝ) ≤ #{m ∈ range n | x i < x m} :=
    Nat.cast_le.2 (card_le_card hsub)
  linarith

open scoped Classical in
/-- **Upper sandwich**: if the marginal exceedance counts of the levels `b_j` are at least
`k x_j`, then every observation counted by `ℓ̂_n(x)` exceeds the level `b_j` in some
coordinate. -/
theorem empiricalTailCount_le_card {F : ι → ℝ → ℝ} (hF : ∀ j, Monotone (F j))
    (X : ℕ → ι → ℝ) (n k : ℕ) (x b : ι → ℝ)
    (hb : ∀ j, (k : ℝ) * x j ≤ #{m ∈ range n | b j < F j (X m j)}) :
    empiricalTailCount X n k x ≤ #{i ∈ range n | ∃ j, b j < F j (X i j)} := by
  rw [empiricalTailCount_eq]
  refine card_le_card fun i hi ↦ ?_
  simp only [mem_filter] at hi ⊢
  obtain ⟨hin, j, hj⟩ := hi
  exact ⟨hin, j, lt_apply_of_card_lt_of_le_card (hF j) (fun m ↦ X m j) n i (hb j) hj⟩

/-- `ℓ̂_n` is coordinatewise nondecreasing. -/
lemma empiricalStableTailDependence_mono (X : ℕ → ι → ℝ) (n k : ℕ) {x y : ι → ℝ}
    (hxy : ∀ j, x j ≤ y j) :
    empiricalStableTailDependence X n k x ≤ empiricalStableTailDependence X n k y := by
  classical
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [empiricalTailCount_eq, empiricalTailCount_eq]
  refine Nat.cast_le.2 (card_le_card fun i hi ↦ ?_)
  simp only [mem_filter] at hi ⊢
  obtain ⟨hin, j, hj⟩ := hi
  exact ⟨hin, j, hj.trans_le (mul_le_mul_of_nonneg_left (hxy j) (by positivity))⟩

/-- The number of observations with fewer than `c` strictly larger observations in coordinate
`j`, that is, with `R_i^j > n - c`. -/
noncomputable def marginalRankCount (X : ℕ → ι → ℝ) (n : ℕ) (j : ι) (c : ℝ) : ℕ :=
  #{i ∈ range n | (#{m ∈ range n | X i j < X m j} : ℝ) < c}

/-- If each `y_j` is at most `x_j` or at most `δ`, then the tail count at `y` exceeds the one at
`x` by at most the marginal rank counts at level `k δ`. This is what controls `ℓ̂_n` near the
boundary of the orthant, and it needs no assumption on ties. -/
lemma empiricalTailCount_le_add_marginalRankCount (X : ℕ → ι → ℝ) (n k : ℕ) {x y : ι → ℝ} {δ : ℝ}
    (h : ∀ j, y j ≤ x j ∨ y j ≤ δ) :
    empiricalTailCount X n k y ≤
      empiricalTailCount X n k x + ∑ j, marginalRankCount X n j (k * δ) := by
  classical
  rw [empiricalTailCount_eq, empiricalTailCount_eq]
  refine (card_le_card (t := {i ∈ range n | ∃ j, (#{m ∈ range n | X i j < X m j} : ℝ) < k * x j} ∪
    univ.biUnion fun j ↦ {i ∈ range n | (#{m ∈ range n | X i j < X m j} : ℝ) < k * δ}) ?_).trans
    ((card_union_le _ _).trans (add_le_add le_rfl card_biUnion_le))
  intro i hi
  simp only [mem_filter, mem_union, mem_biUnion, mem_univ, true_and] at hi ⊢
  obtain ⟨hin, j, hj⟩ := hi
  have hk : (0 : ℝ) ≤ k := by positivity
  rcases h j with hl | hl
  · exact Or.inl ⟨hin, j, hj.trans_le (mul_le_mul_of_nonneg_left hl hk)⟩
  · exact Or.inr ⟨j, hin, hj.trans_le (mul_le_mul_of_nonneg_left hl hk)⟩

/-- The per-coordinate form of the upper sandwich. -/
lemma marginalRankCount_le_card {F : ℝ → ℝ} (hF : Monotone F) (X : ℕ → ι → ℝ) (n : ℕ) (j : ι)
    {b c : ℝ} (hb : c ≤ #{m ∈ range n | b < F (X m j)}) :
    marginalRankCount X n j c ≤ #{i ∈ range n | b < F (X i j)} := by
  refine card_le_card fun i hi ↦ ?_
  simp only [mem_filter] at hi ⊢
  exact ⟨hi.1, lt_apply_of_card_lt_of_le_card hF (fun m ↦ X m j) n i hb hi.2⟩

/-! ### Ranks and order statistics -/

/-- The bridge to `Statistics/OrderStatistics.lean`: the number of observations strictly larger
than `x_i` is `exceedCount` at the level `x_i`. -/
lemma card_lt_eq_exceedCount (x : ℕ → ℝ) (n i : ℕ) :
    #{m ∈ range n | x i < x m} = exceedCount (fun m : Fin n ↦ x m) (x i) := by
  rw [exceedCount]
  symm
  refine card_bij (fun m _ ↦ (m : ℕ)) ?_ (fun a _ b _ h ↦ Fin.ext h) ?_
  · intro m hm
    simp only [mem_filter, mem_univ, true_and] at hm
    simp [hm]
  · intro b hb
    simp only [mem_filter, mem_range] at hb
    exact ⟨⟨b, hb.1⟩, by simpa using hb.2, rfl⟩

/-- `R_i = n - #{m | x_m > x_i}`: the rank is the complement of the exceedance count. -/
lemma sampleRank_add_exceedCount (x : ℕ → ℝ) (n i : ℕ) :
    sampleRank x n i + exceedCount (fun m : Fin n ↦ x m) (x i) = n := by
  rw [← card_lt_eq_exceedCount, sampleRank]
  simpa using card_filter_add_card_filter_not (s := range n) (fun m ↦ x m ≤ x i)

open scoped Classical in
/-- The order-statistics form of the estimator,
`(1/k) ∑_{i<n} 1{∃ j, X_i^j ≥ X^j_{n-⌊k x_j⌋+1,n}}` ([Huang 1992]; [Drees–Huang 1998];
[dHF, §7.2]), where `X^j_{n-r+1,n}` is the `r`-th largest of `X_0^j, …, X_{n-1}^j`, in the library
`orderStat (fun m : Fin n ↦ X m j) (r - 1)`. -/
noncomputable def empiricalStableTailDependenceOrderStat (X : ℕ → ι → ℝ) (n k : ℕ) (x : ι → ℝ) :
    ℝ :=
  (k : ℝ)⁻¹ * #{i ∈ range n | ∃ j,
    orderStat (fun m : Fin n ↦ X m j) (⌊(k : ℝ) * x j⌋₊ - 1) ≤ X i j}

/-- **The order-statistics form is the rank form at the rounded point**: as soon as
`1 ≤ ⌊k x_j⌋ ≤ n` for all `j` (so that the order statistics exist), the estimator with order
statistics at `x` is `ℓ̂_n` at `⌊k x⌋ / k`. There is no condition on ties. -/
theorem empiricalStableTailDependenceOrderStat_eq (X : ℕ → ι → ℝ) {n k : ℕ} (hk : 0 < k)
    {x : ι → ℝ} (hx : ∀ j, 1 ≤ ⌊(k : ℝ) * x j⌋₊ ∧ ⌊(k : ℝ) * x j⌋₊ ≤ n) :
    empiricalStableTailDependenceOrderStat X n k x =
      empiricalStableTailDependence X n k fun j ↦ (⌊(k : ℝ) * x j⌋₊ : ℝ) / k := by
  classical
  have hk' : (k : ℝ) ≠ 0 := by positivity
  rw [empiricalStableTailDependenceOrderStat, empiricalStableTailDependence, empiricalTailCount_eq]
  congr 3
  ext i
  simp only [mem_filter, and_congr_right_iff]
  refine fun _ ↦ exists_congr fun j ↦ ?_
  rw [orderStat_le_iff _ (by have := hx j; omega), ← card_lt_eq_exceedCount (fun m ↦ X m j),
    mul_div_cancel₀ _ hk', Nat.cast_lt]
  have := (hx j).1
  omega

end Deterministic

/-! ### A weak law of large numbers for binomial counts -/

section WLLN

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace E]

open scoped Classical in
/-- **Weak law of large numbers for exceedance counts**, by Chebyshev's inequality: if
`X_0, X_1, …` are iid, `S_n` are measurable sets, `b_n → ∞` and `n P(X ∈ S_n) / b_n → m`, then
`#{i < n | X_i ∈ S_n} / b_n → m` in probability. -/
theorem tendsto_measure_abs_card_div_sub {X : ℕ → Ω → E} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {S : ℕ → Set E}
    (hS : ∀ n, MeasurableSet (S n)) {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) {m : ℝ}
    (hmean : Tendsto (fun n : ℕ ↦ n * P.real (X 0 ⁻¹' S n) / b n) atTop (𝓝 m))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ε ≤ |(#{i ∈ range n | X i ω ∈ S n} : ℝ) / b n - m|}) atTop
      (𝓝 0) := by
  set g : ℕ → E → ℝ := fun n y ↦ (S n).indicator 1 y with hg_def
  have hg : ∀ n, Measurable (g n) := fun n ↦ measurable_one.indicator (hS n)
  have hg_sq : ∀ n y, g n y ^ 2 = g n y := fun n y ↦ by
    simp only [g, Set.indicator_apply]; split_ifs <;> simp
  have hEg : ∀ n, P[fun ω ↦ g n (X 0 ω)] = P.real (X 0 ⁻¹' S n) := fun n ↦ by
    have : (fun ω ↦ g n (X 0 ω)) = (X 0 ⁻¹' S n).indicator 1 := by
      ext ω; simp [g, Set.indicator_apply]
    rw [this, integral_indicator_one ((hX 0) (hS n))]
  have hbpos : ∀ᶠ n in atTop, 0 < b n := hb.eventually_gt_atTop 0
  have hvar : Tendsto (fun n : ℕ ↦ n * P[fun ω ↦ g n (X 0 ω) ^ 2] / b n ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n ↦ (n * P.real (X 0 ⁻¹' S n) / b n) * (b n)⁻¹) atTop (𝓝 (m * 0)) :=
      hmean.mul (tendsto_inv_atTop_zero.comp hb)
    rw [mul_zero] at h0
    refine h0.congr' ?_
    filter_upwards [hbpos] with n hn
    simp only [hg_sq, hEg]
    field_simp
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (4 / ε ^ 2 *
      (n * P[fun ω ↦ g n (X 0 ω) ^ 2] / b n ^ 2))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa using hvar.const_mul (4 / ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  have hmean' := (Metric.tendsto_nhds.1 hmean) (ε / 2) (half_pos hε)
  filter_upwards [hbpos, hmean'] with n hbn hmn
  set Y : ℕ → Ω → ℝ := fun i ω ↦ g n (X i ω) with hY
  have hYId : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i ↦ by
    have := (hident i).comp (hg n)
    simpa [hY, Function.comp_def] using this
  have hL2 : MemLp (fun ω ↦ g n (X 0 ω)) 2 P := by
    refine MemLp.of_bound ((hg n).comp (hX 0)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω ↦ ?_)
    simp only [g, Set.indicator_apply]
    split_ifs <;> simp
  have hYL2 : ∀ i, MemLp (Y i) 2 P := fun i ↦ (hYId i).memLp_iff.2 hL2
  have hYind : ∀ i j, i ≠ j → IndepFun (Y i) (Y j) P := fun i j hij ↦
    (hindep.indepFun hij).comp (hg n) (hg n)
  set T : Ω → ℝ := ∑ i ∈ range n, Y i with hT
  have hTfun : ∀ ω, T ω = #{i ∈ range n | X i ω ∈ S n} := fun ω ↦ by
    simp only [hT, hY, Finset.sum_apply, g, Set.indicator_apply, Pi.one_apply]
    rw [sum_boole]
  have hTL2 : MemLp T 2 P := memLp_finsetSum' _ fun i _ ↦ hYL2 i
  have hET : P[T] = (n : ℝ) * P.real (X 0 ⁻¹' S n) := by
    have : ∫ ω, T ω ∂P = ∑ i ∈ range n, ∫ ω, Y i ω ∂P := by
      simp only [hT, Finset.sum_apply]
      exact integral_finsetSum _ fun i _ ↦ (hYL2 i).integrable one_le_two
    rw [this, Finset.sum_congr rfl fun i _ ↦ (hYId i).integral_eq, sum_const, card_range,
      nsmul_eq_mul]
    simp only [hY]
    rw [hEg]
  have hVT : variance T P ≤ n * P[fun ω ↦ g n (X 0 ω) ^ 2] := by
    rw [hT, IndepFun.variance_sum (fun i _ ↦ hYL2 i) (fun i _ j _ hij ↦ hYind i j hij)]
    rw [Finset.sum_congr rfl fun i _ ↦ (hYId i).variance_eq, sum_const, card_range,
      nsmul_eq_mul]
    gcongr
    exact variance_le_expectation_sq (hYL2 0).aestronglyMeasurable
  rw [Real.dist_eq] at hmn
  have hsub : {ω | ε ≤ |(#{i ∈ range n | X i ω ∈ S n} : ℝ) / b n - m|} ⊆
      {ω | ε * b n / 2 ≤ |T ω - P[T]|} := by
    intro ω hω
    simp only [mem_setOf_eq] at hω ⊢
    rw [hTfun, hET]
    have h1 : (#{i ∈ range n | X i ω ∈ S n} : ℝ) / b n - m =
        ((#{i ∈ range n | X i ω ∈ S n} : ℝ) - n * P.real (X 0 ⁻¹' S n)) / b n +
          (n * P.real (X 0 ⁻¹' S n) / b n - m) := by
      field_simp; ring
    rw [h1] at hω
    have h2 := (abs_add_le _ _).trans' hω
    rw [abs_div, abs_of_pos hbn] at h2
    have h3 : ε / 2 ≤ |(#{i ∈ range n | X i ω ∈ S n} : ℝ) - n * P.real (X 0 ⁻¹' S n)| / b n := by
      linarith
    rw [le_div_iff₀ hbn] at h3
    linarith
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_variance_div_sq hTL2 (by positivity)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by positivity)]
  calc variance T P ≤ n * P[fun ω ↦ g n (X 0 ω) ^ 2] := hVT
    _ = _ := by field_simp; ring

end WLLN

/-! ### Consistency -/

section Consistency

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ]

/-- `k / n → 0` and `k → ∞` give `k / n → 0` from the right. -/
lemma tendsto_div_nhdsGT_zero {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨hkn, ?_⟩
  filter_upwards [hk.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hk hn
  have h1 : (0 : ℝ) < k n := by exact_mod_cast hk
  have h2 : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos h1 h2

open scoped Classical in
/-- **Consistency with known margins**: for `s ∈ (0, ∞)^ι`,
`(1/k) #{i < n | ∃ j, F_j(X_i^j) > 1 - (k/n) s_j} → ℓ(s)` in probability. -/
theorem tendsto_measure_abs_card_tailUnion_sub {X : ℕ → Ω → ι → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hlaw : P.map (X 0) = μ) {ℓ : (ι → ℝ) → ℝ} (hℓ : HasStableTailDependence μ ℓ)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {s : ι → ℝ} (hs : ∀ j, 0 < s j) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ε ≤ |(#{i ∈ range n | ∃ j,
      1 - (k n : ℝ) / n * s j < marginal μ j (X i ω j)} : ℝ) / k n - ℓ s|}) atTop (𝓝 0) := by
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have := tendsto_measure_abs_card_div_sub hX hindep hident
    (S := fun n ↦ {y : ι → ℝ | ∃ j, 1 - (k n : ℝ) / n * s j < marginal μ j (y j)})
    (fun n ↦ measurableSet_tailUnion _ _) hkR (m := ℓ s) ?_ hε
  · simpa only [Set.mem_setOf_eq] using this
  have hlim := (hℓ s hs).comp (tendsto_div_nhdsGT_zero hk hkn)
  refine hlim.congr' ?_
  filter_upwards [hk.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hk hn
  have hP : P.real (X 0 ⁻¹' {y : ι → ℝ | ∃ j, 1 - (k n : ℝ) / n * s j < marginal μ j (y j)}) =
      tailUnionProb μ ((k n : ℝ) / n) s := by
    have hmap := map_measureReal_apply (μ := P) (hX 0)
      (measurableSet_tailUnion (μ := μ) ((k n : ℝ) / n) s)
    rw [hlaw] at hmap
    exact hmap.symm
  simp only [Function.comp_apply, hP]
  have hk' : (0 : ℝ) < k n := by exact_mod_cast hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

open scoped Classical in
/-- **Consistency of the marginal tail counts**: for a continuous marginal and `s > 0`,
`(1/k) #{i < n | F_j(X_i^j) > 1 - (k/n) s} → s` in probability. -/
theorem tendsto_measure_abs_card_marginal_sub {X : ℕ → Ω → ι → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hlaw : P.map (X 0) = μ) {j : ι} (hc : Continuous (marginal μ j))
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ε ≤ |(#{i ∈ range n |
      1 - (k n : ℝ) / n * s < marginal μ j (X i ω j)} : ℝ) / k n - s|}) atTop (𝓝 0) := by
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  refine tendsto_measure_abs_card_div_sub hX hindep hident
    (S := fun n ↦ {y : ι → ℝ | 1 - (k n : ℝ) / n * s < marginal μ j (y j)})
    (fun n ↦ measurableSet_one_sub_lt_marginal _ _) hkR (m := s) ?_ hε
  refine tendsto_const_nhds.congr' ?_
  have hsmall : ∀ᶠ n in atTop, (k n : ℝ) / n * s < 1 := by
    have : Tendsto (fun n ↦ (k n : ℝ) / n * s) atTop (𝓝 0) := by simpa using hkn.mul_const s
    exact this.eventually (gt_mem_nhds one_pos)
  filter_upwards [hk.eventually_gt_atTop 0, eventually_gt_atTop 0, hsmall] with n hk hn hsm
  have hk' : (0 : ℝ) < k n := by exact_mod_cast hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmap := map_measureReal_apply (μ := P) (hX 0)
    (measurableSet_one_sub_lt_marginal (μ := μ) j (1 - (k n : ℝ) / n * s))
  rw [hlaw, measureReal_one_sub_lt_marginal hc (by positivity) hsm] at hmap
  rw [← hmap]
  field_simp

/-- **Weak consistency of the empirical stable tail dependence function, pointwise**
([dHF, §7.2]; [Huang 1992]; [Drees–Huang 1998]; [BGST04, §9.4.1]): let `X_0, X_1, …` be iid random vectors in `ℝ^ι` (`ι` finite) with law `μ`, whose marginal
distribution functions are continuous, and suppose that `μ` has stable tail dependence function
`ℓ`. If `k = k(n) → ∞` and `k / n → 0`, then for every `x ∈ (0, ∞)^ι` the rank-based estimator
`ℓ̂_n(x) = (1/k) ∑_{i<n} 1{∃ j, R_i^j > n - k x_j}` converges to `ℓ(x)` in probability.

The form uniform in `x` is `tendsto_measure_exists_abs_empiricalStableTailDependence_sub`.
Continuity of the marginals (`hc`) gives the probability integral transform and the Lipschitz
bound. `hℓ` asks only that `ℓ` exists, which follows from a domain of attraction
(`IsMDAWith.hasStableTailDependence`) and is a weaker assumption. -/
theorem tendstoInMeasure_empiricalStableTailDependence {X : ℕ → Ω → ι → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hlaw : P.map (X 0) = μ)
    (hc : ∀ j, Continuous (marginal μ j)) {ℓ : (ι → ℝ) → ℝ} (hℓ : HasStableTailDependence μ ℓ)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {x : ι → ℝ} (hx : ∀ j, 0 < x j) :
    TendstoInMeasure P (fun n ω ↦ empiricalStableTailDependence (fun i ↦ X i ω) n (k n) x)
      atTop (fun _ ↦ ℓ x) := by
  classical
  rw [tendstoInMeasure_iff_dist]
  intro η hη
  -- choose the perturbation `δ`
  obtain ⟨δ, ⟨hδx, hδη⟩, hδ0⟩ : ∃ δ, ((∀ j, δ < x j) ∧ (Fintype.card ι : ℝ) * δ < η / 2) ∧
      0 < δ := by
    have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ j, δ < x j :=
      eventually_all.2 fun j ↦ gt_mem_nhds (hx j)
    have h2 : ∀ᶠ δ in 𝓝 (0 : ℝ), (Fintype.card ι : ℝ) * δ < η / 2 := by
      have hcont : Continuous fun δ : ℝ ↦ (Fintype.card ι : ℝ) * δ := by fun_prop
      have : Tendsto (fun δ : ℝ ↦ (Fintype.card ι : ℝ) * δ) (𝓝 0) (𝓝 0) := by
        simpa using hcont.tendsto (0 : ℝ)
      exact this.eventually (gt_mem_nhds (half_pos hη))
    exact ((h1.and h2).filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  set xl : ι → ℝ := fun j ↦ x j - δ
  set xu : ι → ℝ := fun j ↦ x j + δ
  have hxl : ∀ j, 0 < xl j := fun j ↦ sub_pos.2 (hδx j)
  have hxu : ∀ j, 0 < xu j := fun j ↦ by simp only [xu]; linarith [hx j]
  have hLl : |ℓ xl - ℓ x| ≤ Fintype.card ι * δ := by
    refine (hℓ.abs_sub_le hc hxl hx).trans_eq ?_
    simp [xl, abs_of_pos hδ0]
  have hLu : |ℓ xu - ℓ x| ≤ Fintype.card ι * δ := by
    refine (hℓ.abs_sub_le hc hxu hx).trans_eq ?_
    simp [xu, abs_of_pos hδ0]
  -- the bad events
  set F : ι → ℝ → ℝ := fun j ↦ marginal μ j
  have hF : ∀ j, Monotone (F j) := fun j ↦ marginal_mono j
  set T : ℕ → (ι → ℝ) → Ω → ℝ := fun n s ω ↦
    (#{i ∈ range n | ∃ j, 1 - (k n : ℝ) / n * s j < F j (X i ω j)} : ℝ) / k n
  set C : ℕ → ι → ℝ → Ω → ℝ := fun n j s ω ↦
    (#{i ∈ range n | 1 - (k n : ℝ) / n * s < F j (X i ω j)} : ℝ) / k n
  set E1 : ℕ → Set Ω := fun n ↦ {ω | η / 2 ≤ |T n xl ω - ℓ xl|}
  set E2 : ℕ → Set Ω := fun n ↦ {ω | η / 2 ≤ |T n xu ω - ℓ xu|}
  set E3 : ℕ → ι → Set Ω := fun n j ↦ {ω | δ ≤ |C n j (xl j) ω - xl j|}
  set E4 : ℕ → ι → Set Ω := fun n j ↦ {ω | δ ≤ |C n j (xu j) ω - xu j|}
  have hE1 : Tendsto (fun n ↦ P (E1 n)) atTop (𝓝 0) :=
    tendsto_measure_abs_card_tailUnion_sub hX hindep hident hlaw hℓ hk hkn hxl (half_pos hη)
  have hE2 : Tendsto (fun n ↦ P (E2 n)) atTop (𝓝 0) :=
    tendsto_measure_abs_card_tailUnion_sub hX hindep hident hlaw hℓ hk hkn hxu (half_pos hη)
  have hE3 : ∀ j, Tendsto (fun n ↦ P (E3 n j)) atTop (𝓝 0) := fun j ↦
    tendsto_measure_abs_card_marginal_sub hX hindep hident hlaw (hc j) hk hkn (hxl j) hδ0
  have hE4 : ∀ j, Tendsto (fun n ↦ P (E4 n j)) atTop (𝓝 0) := fun j ↦
    tendsto_measure_abs_card_marginal_sub hX hindep hident hlaw (hc j) hk hkn (hxu j) hδ0
  have hsum : Tendsto (fun n ↦ P (E1 n) + P (E2 n) + (∑ j, P (E3 n j) + ∑ j, P (E4 n j)))
      atTop (𝓝 0) := by
    have h3 := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ ↦ hE3 j
    have h4 := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ ↦ hE4 j
    simp only [Finset.sum_const_zero] at h3 h4
    simpa using (hE1.add hE2).add (h3.add h4)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hk.eventually_gt_atTop 0] with n hkn0
  have hk' : (0 : ℝ) < k n := by exact_mod_cast hkn0
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans le_rfl) ((measure_union_le _ _).trans
      (add_le_add (measure_iUnion_fintype_le _ _) (measure_iUnion_fintype_le _ _)))))
  intro ω hω
  simp only [mem_setOf_eq] at hω
  by_contra hout
  simp only [Set.mem_union, mem_iUnion, not_or, not_exists] at hout
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hout
  simp only [E1, E2, E3, E4, mem_setOf_eq, not_le] at h1 h2 h3 h4
  -- the sandwich
  have hlow : (#{i ∈ range n | ∃ j, 1 - (k n : ℝ) / n * xl j < F j (X i ω j)} : ℝ) ≤
      empiricalTailCount (fun i ↦ X i ω) n (k n) x := by
    refine Nat.cast_le.2 (card_le_empiricalTailCount hF (fun i ↦ X i ω) n (k n) x _ fun j ↦ ?_)
    have := (abs_lt.1 (h3 j)).2
    simp only [C, xl] at this
    rw [div_sub' hk'.ne', div_lt_iff₀ hk'] at this
    nlinarith
  have hup : (empiricalTailCount (fun i ↦ X i ω) n (k n) x : ℝ) ≤
      #{i ∈ range n | ∃ j, 1 - (k n : ℝ) / n * xu j < F j (X i ω j)} := by
    refine Nat.cast_le.2 (empiricalTailCount_le_card hF (fun i ↦ X i ω) n (k n) x _ fun j ↦ ?_)
    have := (abs_lt.1 (h4 j)).1
    simp only [C, xu] at this
    rw [div_sub' hk'.ne', lt_div_iff₀ hk'] at this
    nlinarith
  have hTl : T n xl ω ≤ empiricalStableTailDependence (fun i ↦ X i ω) n (k n) x := by
    simp only [T, empiricalStableTailDependence]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hlow (inv_pos.2 hk').le
  have hTu : empiricalStableTailDependence (fun i ↦ X i ω) n (k n) x ≤ T n xu ω := by
    simp only [T, empiricalStableTailDependence]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hup (inv_pos.2 hk').le
  rw [Real.dist_eq] at hω
  have a1 := abs_lt.1 h1
  have a2 := abs_lt.1 h2
  have a3 := abs_le.1 hLl
  have a4 := abs_le.1 hLu
  rcases le_abs'.1 hω with h | h <;> linarith

/-- **Uniform weak consistency of the empirical stable tail dependence function**
([Huang 1992]; [Drees–Huang 1998]; [dHF, §7.2]): under the hypotheses of
`tendstoInMeasure_empiricalStableTailDependence`, for every `T` and `ε > 0`,

  `P(∃ x ∈ (0, T]^ι, |ℓ̂_n(x) - ℓ(x)| ≥ ε) → 0`,

that is, `sup_{x ∈ (0, T]^ι} |ℓ̂_n(x) - ℓ(x)| → 0` in (outer) probability.

**Deviation from the textbook:** the supremum in the literature runs over the closed box
`[0, T]^ι`. This statement omits the faces `x_j = 0`, because `HasStableTailDependence` says
nothing about `ℓ` there, so `ℓ` is arbitrary on those faces and the closed-box statement would be
false for this `ℓ`. It is uniform all the way up to those faces.

Hypotheses: iid observations with law `μ` (`hX`, `hindep`, `hident`, `hlaw`); continuous marginals
(`hc`), used for the probability integral transform and the Lipschitz bound; existence of `ℓ`
(`hℓ`); and the intermediate sequence (`hk`, `hkn`). No rate on `k` and no second-order condition
is needed.

Proof: `ℓ̂_n` is monotone and `ℓ` is Lipschitz, so consistency on a finite grid of mesh `δ` gives
consistency on the box, as in the proof of the Glivenko–Cantelli theorem. Below the first grid
point, `empiricalTailCount_le_add_marginalRankCount` compares with the marginal rank counts. `P` of the
event is the outer measure of a set whose measurability is not needed. -/
theorem tendsto_measure_exists_abs_empiricalStableTailDependence_sub {X : ℕ → Ω → ι → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hlaw : P.map (X 0) = μ)
    (hc : ∀ j, Continuous (marginal μ j)) {ℓ : (ι → ℝ) → ℝ} (hℓ : HasStableTailDependence μ ℓ)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ∃ x : ι → ℝ, (∀ j, 0 < x j ∧ x j ≤ T) ∧
      ε ≤ |empiricalStableTailDependence (fun i ↦ X i ω) n (k n) x - ℓ x|}) atTop (𝓝 0) := by
  classical
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  set δ : ℝ := ε / (8 * (d + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hdδ : 4 * (d * δ) ≤ ε / 2 := by
    have : d * δ = ε / 8 * (d / (d + 1)) := by rw [hδ]; field_simp
    have h1 : d / (d + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    have h2 : ε / 8 * (d / (d + 1)) ≤ ε / 8 * 1 := by gcongr
    rw [this]
    linarith
  -- the grid
  set M : ℕ := ⌊T / δ⌋₊ with hM
  set g : (ι → Fin (M + 1)) → ι → ℝ := fun m j ↦ ((m j : ℕ) + 1) * δ with hg
  have hgpos : ∀ m j, 0 < g m j := fun m j ↦ by simp only [hg]; positivity
  -- the bad events
  set A : ℕ → (ι → Fin (M + 1)) → Set Ω := fun n m ↦
    {ω | ε / 4 ≤ dist (empiricalStableTailDependence (fun i ↦ X i ω) n (k n) (g m)) (ℓ (g m))}
  set C : ℕ → ι → Ω → ℝ := fun n j ω ↦
    (#{i ∈ range n | 1 - (k n : ℝ) / n * (2 * δ) < marginal μ j (X i ω j)} : ℝ) / k n
  set B : ℕ → ι → Set Ω := fun n j ↦ {ω | δ ≤ |C n j ω - 2 * δ|}
  have hA : ∀ m, Tendsto (fun n ↦ P (A n m)) atTop (𝓝 0) := fun m ↦
    (tendstoInMeasure_iff_dist.1 (tendstoInMeasure_empiricalStableTailDependence hX hindep hident
      hlaw hc hℓ hk hkn (hgpos m))) _ (by positivity)
  have hB : ∀ j, Tendsto (fun n ↦ P (B n j)) atTop (𝓝 0) := fun j ↦
    tendsto_measure_abs_card_marginal_sub hX hindep hident hlaw (hc j) hk hkn (by positivity) hδ0
  have hsum : Tendsto (fun n ↦ ∑ m, P (A n m) + ∑ j, P (B n j)) atTop (𝓝 0) := by
    have h1 := tendsto_finsetSum (Finset.univ : Finset (ι → Fin (M + 1))) fun m _ ↦ hA m
    have h2 := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ ↦ hB j
    simp only [Finset.sum_const_zero] at h1 h2
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hk.eventually_gt_atTop 0] with n hkn0
  have hk' : (0 : ℝ) < k n := by exact_mod_cast hkn0
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add
    (measure_iUnion_fintype_le _ _) (measure_iUnion_fintype_le _ _)))
  rintro ω ⟨x, hxT, hω⟩
  by_contra hout
  simp only [Set.mem_union, mem_iUnion, not_or, not_exists] at hout
  obtain ⟨hAω, hBω⟩ := hout
  simp only [A, B, mem_setOf_eq, not_le, Real.dist_eq] at hAω hBω
  set L : ((ι → ℝ)) → ℝ := fun y ↦ empiricalStableTailDependence (fun i ↦ X i ω) n (k n) y with hL
  -- the floor of `x_j / δ`
  have hq : ∀ j, ⌊x j / δ⌋₊ < M + 1 := fun j ↦ by
    refine Nat.lt_succ_of_le (Nat.floor_le_floor ?_)
    exact div_le_div_of_nonneg_right (hxT j).2 hδ0.le
  have hq1 : ∀ j, (⌊x j / δ⌋₊ : ℝ) * δ ≤ x j := fun j ↦ by
    have := Nat.floor_le (div_nonneg (hxT j).1.le hδ0.le)
    rwa [le_div_iff₀ hδ0] at this
  have hq2 : ∀ j, x j < ((⌊x j / δ⌋₊ : ℝ) + 1) * δ := fun j ↦ by
    have := Nat.lt_floor_add_one (x j / δ)
    rwa [div_lt_iff₀ hδ0] at this
  -- the upper grid point
  set mU : ι → Fin (M + 1) := fun j ↦ ⟨⌊x j / δ⌋₊, hq j⟩
  have hU : ∀ j, g mU j = ((⌊x j / δ⌋₊ : ℝ) + 1) * δ := fun _ ↦ rfl
  have hUx : ∀ j, x j ≤ g mU j := fun j ↦ by rw [hU]; exact (hq2 j).le
  have hUd : ∀ j, |x j - g mU j| ≤ δ := fun j ↦ by
    rw [abs_le, hU]
    constructor <;> nlinarith [hq1 j, hq2 j]
  -- the lower grid point
  set mL : ι → Fin (M + 1) := fun j ↦ ⟨⌊x j / δ⌋₊ - 1, by have := hq j; omega⟩
  have hLo : ∀ j, g mL j ≤ x j ∨ g mL j ≤ δ := fun j ↦ by
    rcases Nat.eq_zero_or_pos ⌊x j / δ⌋₊ with h0 | h0
    · right
      simp [hg, mL, h0]
    · left
      have : ((⌊x j / δ⌋₊ - 1 : ℕ) : ℝ) + 1 = (⌊x j / δ⌋₊ : ℝ) := by
        rw [Nat.cast_sub h0]; simp
      simp only [hg, mL]
      rw [this]
      exact hq1 j
  have hLd : ∀ j, |x j - g mL j| ≤ δ := fun j ↦ by
    rcases Nat.eq_zero_or_pos ⌊x j / δ⌋₊ with h0 | h0
    · have h2 := hq2 j
      rw [h0] at h2
      have hv : g mL j = δ := by simp [hg, mL, h0]
      rw [hv, abs_le]
      have := (hxT j).1
      constructor <;> simp at h2 <;> linarith
    · have : ((⌊x j / δ⌋₊ - 1 : ℕ) : ℝ) + 1 = (⌊x j / δ⌋₊ : ℝ) := by
        rw [Nat.cast_sub h0]; simp
      have hv : g mL j = (⌊x j / δ⌋₊ : ℝ) * δ := by simp only [hg, mL]; rw [this]
      rw [hv, abs_le]
      constructor <;> nlinarith [hq1 j, hq2 j]
  have hLip : ∀ m : ι → Fin (M + 1), (∀ j, |x j - g m j| ≤ δ) → |ℓ x - ℓ (g m)| ≤ d * δ := by
    intro m hm
    refine (hℓ.abs_sub_le hc (fun j ↦ (hxT j).1) (hgpos m)).trans ?_
    calc ∑ j, |x j - g m j| ≤ ∑ _j : ι, δ := Finset.sum_le_sum fun j _ ↦ hm j
      _ = d * δ := by simp [hd]
  -- the marginal rank counts near the boundary are at most `3 k δ`
  have hmarg : ∀ j, (k n : ℝ)⁻¹ * marginalRankCount (fun i ↦ X i ω) n j (k n * δ) ≤ 3 * δ := by
    intro j
    obtain ⟨hC1, hC2⟩ := abs_lt.1 (hBω j)
    have hb : (k n : ℝ) * δ ≤
        #{m ∈ range n | 1 - (k n : ℝ) / n * (2 * δ) < marginal μ j (X m ω j)} := by
      have : δ ≤ C n j ω := by linarith
      simp only [C] at this
      rwa [le_div_iff₀ hk', mul_comm] at this
    have hcard := marginalRankCount_le_card (marginal_mono (μ := μ) j) (fun i ↦ X i ω) n j hb
    have hcard' : (marginalRankCount (fun i ↦ X i ω) n j (k n * δ) : ℝ) ≤
        #{m ∈ range n | 1 - (k n : ℝ) / n * (2 * δ) < marginal μ j (X m ω j)} := by
      exact_mod_cast hcard
    have hC3 : C n j ω ≤ 3 * δ := by linarith
    calc (k n : ℝ)⁻¹ * marginalRankCount (fun i ↦ X i ω) n j (k n * δ)
        ≤ (k n : ℝ)⁻¹ * #{m ∈ range n | 1 - (k n : ℝ) / n * (2 * δ) < marginal μ j (X m ω j)} :=
          mul_le_mul_of_nonneg_left hcard' (by positivity)
      _ = C n j ω := (div_eq_inv_mul _ _).symm
      _ ≤ 3 * δ := hC3
  have hlow : L (g mL) ≤ L x + d * (3 * δ) := by
    have hc1 := empiricalTailCount_le_add_marginalRankCount (fun i ↦ X i ω) n (k n) hLo
    have hc1' : (empiricalTailCount (fun i ↦ X i ω) n (k n) (g mL) : ℝ) ≤
        empiricalTailCount (fun i ↦ X i ω) n (k n) x +
          ∑ j, (marginalRankCount (fun i ↦ X i ω) n j (k n * δ) : ℝ) := by
      exact_mod_cast hc1
    calc L (g mL) ≤ (k n : ℝ)⁻¹ * (empiricalTailCount (fun i ↦ X i ω) n (k n) x +
          ∑ j, (marginalRankCount (fun i ↦ X i ω) n j (k n * δ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hc1' (by positivity)
      _ = L x + ∑ j, (k n : ℝ)⁻¹ * marginalRankCount (fun i ↦ X i ω) n j (k n * δ) := by
          rw [mul_add, Finset.mul_sum]; rfl
      _ ≤ L x + ∑ _j : ι, 3 * δ := by
          have := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ hmarg j
          linarith
      _ = L x + d * (3 * δ) := by simp [hd]
  have hup : L x ≤ L (g mU) := empiricalStableTailDependence_mono _ _ _ hUx
  have a1 := abs_lt.1 (hAω mU)
  have a2 := abs_lt.1 (hAω mL)
  have a3 := abs_le.1 (hLip mU hUd)
  have a4 := abs_le.1 (hLip mL hLd)
  have hLgU : L (g mU) - ℓ (g mU) < ε / 4 := a1.2
  have hLgL : -(ε / 4) < L (g mL) - ℓ (g mL) := a2.1
  have hdδ1 : d * (3 * δ) + d * δ ≤ ε / 2 := by nlinarith
  have hdδ2 : 0 ≤ d * δ := by positivity
  rcases le_abs'.1 hω with h | h <;> linarith

/-- **Consistency along a converging sequence of points**: if `y_n → x ∈ (0, ∞)^ι`, with positive
coordinates eventually, then `ℓ̂_n(y_n) → ℓ(x)` in probability. A consequence of the uniform
consistency and the Lipschitz bound. This covers the usual variants of the estimator. For example
`R_i^j > n + 1/2 - k x_j` is `ℓ̂_n` at `y_n = x - 1/(2k)`, and for the order statistics see
`tendstoInMeasure_empiricalStableTailDependenceOrderStat`. -/
theorem tendstoInMeasure_empiricalStableTailDependence_of_tendsto {X : ℕ → Ω → ι → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hlaw : P.map (X 0) = μ)
    (hc : ∀ j, Continuous (marginal μ j)) {ℓ : (ι → ℝ) → ℝ} (hℓ : HasStableTailDependence μ ℓ)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {x : ι → ℝ} (hx : ∀ j, 0 < x j) {y : ℕ → ι → ℝ} (hypos : ∀ᶠ n in atTop, ∀ j, 0 < y n j)
    (hy : ∀ j, Tendsto (fun n ↦ y n j) atTop (𝓝 (x j))) :
    TendstoInMeasure P (fun n ω ↦ empiricalStableTailDependence (fun i ↦ X i ω) n (k n) (y n))
      atTop (fun _ ↦ ℓ x) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set T : ℝ := ∑ j, x j + 1 with hT
  have hxT : ∀ j, x j < T := fun j ↦ by
    have := Finset.single_le_sum (f := x) (fun i _ ↦ (hx i).le) (Finset.mem_univ j)
    simp only [hT]
    linarith
  have hyT : ∀ᶠ n in atTop, ∀ j, y n j ≤ T :=
    eventually_all.2 fun j ↦ ((hy j).eventually (gt_mem_nhds (hxT j))).mono fun _ h ↦ h.le
  have hsum : Tendsto (fun n ↦ ∑ j, |y n j - x j|) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset ι) fun j _ ↦ ((hy j).sub_const (x j)).abs
    simpa using this
  have hsmall := hsum.eventually (gt_mem_nhds (half_pos hε))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_measure_exists_abs_empiricalStableTailDependence_sub hX hindep hident hlaw hc hℓ hk hkn
      T (half_pos hε)) (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hypos, hyT, hsmall] with n hn1 hn2 hn3
  refine measure_mono fun ω hω ↦ ⟨y n, fun j ↦ ⟨hn1 j, hn2 j⟩, ?_⟩
  simp only [mem_setOf_eq, Real.dist_eq] at hω
  have hLip := (hℓ.abs_sub_le hc hn1 hx).trans_lt hn3
  have h1 := abs_lt.1 hLip
  rcases le_abs'.1 hω with h | h
  · exact le_abs'.2 (Or.inl (by linarith))
  · exact le_abs'.2 (Or.inr (by linarith))

/-- **Consistency of the order-statistics form of the estimator**
([Huang 1992]; [Drees–Huang 1998]; [dHF, §7.2]):
`(1/k) ∑_{i<n} 1{∃ j, X_i^j ≥ X^j_{n-⌊k x_j⌋+1,n}} → ℓ(x)` in probability, under the hypotheses of
`tendstoInMeasure_empiricalStableTailDependence`. -/
theorem tendstoInMeasure_empiricalStableTailDependenceOrderStat {X : ℕ → Ω → ι → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hlaw : P.map (X 0) = μ)
    (hc : ∀ j, Continuous (marginal μ j)) {ℓ : (ι → ℝ) → ℝ} (hℓ : HasStableTailDependence μ ℓ)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {x : ι → ℝ} (hx : ∀ j, 0 < x j) :
    TendstoInMeasure P
      (fun n ω ↦ empiricalStableTailDependenceOrderStat (fun i ↦ X i ω) n (k n) x)
      atTop (fun _ ↦ ℓ x) := by
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  set y : ℕ → ι → ℝ := fun n j ↦ (⌊(k n : ℝ) * x j⌋₊ : ℝ) / k n with hy
  have hmulTop : ∀ j, Tendsto (fun n ↦ (k n : ℝ) * x j) atTop atTop := fun j ↦
    hkR.atTop_mul_const (hx j)
  have hfl1 : ∀ᶠ n in atTop, ∀ j, 1 ≤ ⌊(k n : ℝ) * x j⌋₊ := eventually_all.2 fun j ↦ by
    filter_upwards [(hmulTop j).eventually_ge_atTop 1] with n hn
    exact Nat.le_floor (by simpa using hn)
  have hfl2 : ∀ᶠ n in atTop, ∀ j, ⌊(k n : ℝ) * x j⌋₊ ≤ n := eventually_all.2 fun j ↦ by
    have h0 : Tendsto (fun n ↦ (k n : ℝ) / n * x j) atTop (𝓝 0) := by
      simpa using hkn.mul_const (x j)
    filter_upwards [h0.eventually (gt_mem_nhds one_pos), eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    refine Nat.floor_le_of_le ?_
    have : (k n : ℝ) * x j = (k n : ℝ) / n * x j * n := by field_simp
    rw [this]
    nlinarith
  have hytend : ∀ j, Tendsto (fun n ↦ y n j) atTop (𝓝 (x j)) := fun j ↦ by
    have := (tendsto_nat_floor_mul_div_atTop (R := ℝ) (hx j).le).comp hkR
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, hy, mul_comm]
  have hypos : ∀ᶠ n in atTop, ∀ j, 0 < y n j := by
    filter_upwards [hfl1, hk.eventually_gt_atTop 0] with n hn hkpos j
    have h1 : (1 : ℝ) ≤ ⌊(k n : ℝ) * x j⌋₊ := by exact_mod_cast hn j
    have h2 : (0 : ℝ) < k n := by exact_mod_cast hkpos
    simp only [hy]
    positivity
  have hmain := tendstoInMeasure_empiricalStableTailDependence_of_tendsto hX hindep hident hlaw hc
    hℓ hk hkn hx hypos hytend
  rw [tendstoInMeasure_iff_dist] at hmain ⊢
  intro ε hε
  refine (hmain ε hε).congr' ?_
  filter_upwards [hfl1, hfl2, hk.eventually_gt_atTop 0] with n h1 h2 hkpos
  congr 1
  ext ω
  simp only [mem_setOf_eq]
  rw [empiricalStableTailDependenceOrderStat_eq _ hkpos fun j ↦ ⟨h1 j, h2 j⟩]

end Consistency

/-! ### The domain of attraction: `χ` and the Pickands function -/

section DomainOfAttraction

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {μ ν : Measure (ι → ℝ)} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] {a b : ℕ → ι → ℝ}

/-- **Consistency in the domain of attraction**: if the iid observations have law `μ` in the
domain of attraction of `ν`, both with continuous marginals, then
`ℓ̂_n(x) → V₀(1/x_1, …, 1/x_d)` in probability, where `V₀` is the exponent function of the
unit Fréchet standardization of `ν` ([dHF, §7.2]).

Continuity of the marginals of `ν` (`hcν`) is what `IsMDAWith.hasStableTailDependence` uses to
standardize; the marginals of a limit with nondegenerate margins are of extreme value type, hence
continuous, and `IsMDAWith` alone does not exclude degenerate ones. -/
theorem IsMDAWith.tendstoInMeasure_empiricalStableTailDependence (h : IsMDAWith μ ν a b)
    (hcμ : ∀ j, Continuous (marginal μ j)) (hcν : ∀ j, Continuous (marginal ν j))
    {X : ℕ → Ω → ι → ℝ} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hlaw : P.map (X 0) = μ)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {x : ι → ℝ} (hx : ∀ j, 0 < x j) :
    TendstoInMeasure P (fun n ω ↦ empiricalStableTailDependence (fun i ↦ X i ω) n (k n) x)
      atTop (fun _ ↦ maxStableExponent (frechetStandardization ν) fun j ↦ (x j)⁻¹) :=
  ExtremeValueTheory.tendstoInMeasure_empiricalStableTailDependence hX hindep hident hlaw hcμ
    (h.hasStableTailDependence hcμ hcν) hk hkn hx

/-- **Uniform consistency in the domain of attraction**: the conclusion of
`tendsto_measure_exists_abs_empiricalStableTailDependence_sub` with `ℓ(x) = V₀(1/x)`, under the
hypotheses of `IsMDAWith.tendstoInMeasure_empiricalStableTailDependence`; the same deviation from
the closed box applies. -/
theorem IsMDAWith.tendsto_measure_exists_abs_empiricalStableTailDependence_sub
    (h : IsMDAWith μ ν a b) (hcμ : ∀ j, Continuous (marginal μ j))
    (hcν : ∀ j, Continuous (marginal ν j)) {X : ℕ → Ω → ι → ℝ} (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hlaw : P.map (X 0) = μ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P {ω | ∃ x : ι → ℝ, (∀ j, 0 < x j ∧ x j ≤ T) ∧
      ε ≤ |empiricalStableTailDependence (fun i ↦ X i ω) n (k n) x -
        maxStableExponent (frechetStandardization ν) fun j ↦ (x j)⁻¹|}) atTop (𝓝 0) :=
  ExtremeValueTheory.tendsto_measure_exists_abs_empiricalStableTailDependence_sub hX hindep hident
    hlaw hcμ (h.hasStableTailDependence hcμ hcν) hk hkn T hε

lemma tendstoInMeasure_const_sub {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (c : ℝ)
    (h : TendstoInMeasure P f atTop g) :
    TendstoInMeasure P (fun n ω ↦ c - f n ω) atTop (fun ω ↦ c - g ω) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  refine (h ε hε).congr fun n ↦ ?_
  congr 1
  ext ω
  simp only [mem_setOf_eq, Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm]

/-- The rank-based estimator `χ̂_n = 2 - ℓ̂_n(1, 1)` of the upper tail dependence coefficient. -/
noncomputable def tailDependenceEstimator (X : ℕ → Fin 2 → ℝ) (n k : ℕ) : ℝ :=
  2 - empiricalStableTailDependence X n k fun _ ↦ 1

/-- The rank-based estimator `Â_n(t) = ℓ̂_n(t, 1 - t)` of the Pickands dependence function
([dHF, §7.2]; [BGST04, §9.4.1]). -/
noncomputable def pickandsRankEstimator (X : ℕ → Fin 2 → ℝ) (n k : ℕ) (t : ℝ) : ℝ :=
  empiricalStableTailDependence X n k ![t, 1 - t]

variable {μ ν : Measure (Fin 2 → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {a b : ℕ → Fin 2 → ℝ}

/-- **Consistency of the tail dependence coefficient estimator**: if `μ` has continuous marginals
and stable tail dependence function `ℓ`, then `χ̂_n = 2 - ℓ̂_n(1, 1) → 2 - ℓ(1, 1)` in
probability; by `HasStableTailDependence.hasUpperTailDependence`, `2 - ℓ(1, 1)` is the upper tail
dependence coefficient `χ = lim_{u ↑ 1} P(F_2(X_2) > u | F_1(X_1) > u)` of `μ`. -/
theorem tendstoInMeasure_tailDependenceEstimator {X : ℕ → Ω → Fin 2 → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hlaw : P.map (X 0) = μ)
    (hc : ∀ j, Continuous (marginal μ j)) {ℓ : (Fin 2 → ℝ) → ℝ}
    (hℓ : HasStableTailDependence μ ℓ)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ tailDependenceEstimator (fun i ↦ X i ω) n (k n)) atTop
      (fun _ ↦ 2 - ℓ fun _ ↦ 1) :=
  tendstoInMeasure_const_sub 2 (tendstoInMeasure_empiricalStableTailDependence hX hindep hident
    hlaw hc hℓ hk hkn fun _ ↦ one_pos)

/-- **Consistency of `χ̂` in the domain of attraction**: `χ̂_n → 2 - θ` in probability, where `θ`
is the extremal coefficient of the unit Fréchet standardization of the limit `ν`; `2 - θ` is the
upper tail dependence coefficient of `μ` (`IsMDAWith.hasUpperTailDependence`). -/
theorem IsMDAWith.tendstoInMeasure_tailDependenceEstimator (h : IsMDAWith μ ν a b)
    (hcμ : ∀ j, Continuous (marginal μ j)) (hcν : ∀ j, Continuous (marginal ν j))
    {X : ℕ → Ω → Fin 2 → ℝ} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hlaw : P.map (X 0) = μ)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ tailDependenceEstimator (fun i ↦ X i ω) n (k n)) atTop
      (fun _ ↦ 2 - extremalCoefficient (frechetStandardization ν)) := by
  simpa [extremalCoefficient] using ExtremeValueTheory.tendstoInMeasure_tailDependenceEstimator
    hX hindep hident hlaw hcμ (h.hasStableTailDependence hcμ hcν) hk hkn

/-- **Consistency of the rank-based Pickands estimator** ([dHF, §7.2]; [BGST04, §9.4.1]): in the
bivariate domain of attraction (continuous marginals), `Â_n(t) = ℓ̂_n(t, 1 - t) → A(t)` in
probability for every `0 < t < 1`, where `A` is the Pickands dependence function of the unit
Fréchet standardization of the limit `ν`. The margins are estimated through the ranks. -/
theorem IsMDAWith.tendstoInMeasure_pickandsRankEstimator (h : IsMDAWith μ ν a b)
    (hcμ : ∀ j, Continuous (marginal μ j)) (hcν : ∀ j, Continuous (marginal ν j))
    {X : ℕ → Ω → Fin 2 → ℝ} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hlaw : P.map (X 0) = μ)
    {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    TendstoInMeasure P (fun n ω ↦ pickandsRankEstimator (fun i ↦ X i ω) n (k n) t) atTop
      (fun _ ↦ pickandsDependence (frechetStandardization ν) t) := by
  have hpos : ∀ j, 0 < (![t, 1 - t] : Fin 2 → ℝ) j := fun j ↦ by
    fin_cases j
    · simpa using ht.1
    · simpa using ht.2
  rw [← maxStableExponent_inv_pair_eq_pickands ht]
  exact h.tendstoInMeasure_empiricalStableTailDependence hcμ hcν hX hindep hident hlaw hk hkn
    hpos

end DomainOfAttraction

end ExtremeValueTheory
