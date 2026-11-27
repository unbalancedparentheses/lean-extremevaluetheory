/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.ExtremalIndexEstimators

/-!
# Sliding-blocks estimators of cluster functionals and the extremal index under `α`-mixing

Let `X_0, X_1, …` be a stationary sequence, `uₙ` a threshold sequence, `pₙ = P(X_0 > uₙ)` and
`rₙ` a block length. For each `i < n - rₙ + 1`, the `i`-th **sliding block** of length `rₙ` is the
window `W_i = (X_i, X_{i+1}, …, X_{i + rₙ - 1})`. Given a bounded measurable cluster functional
`Hₙ : (Fin rₙ → ℝ) → ℝ` that vanishes on blocks without an exceedance of `uₙ`, the **sliding-blocks
cluster estimator** (Cissokho and Kulik 2021) is

  `θ̂_H^{sb} = (∑_{i < n - rₙ + 1} Hₙ(W_i)) / (rₙ · #{i < n : X_i > uₙ})`.

When `Hₙ(x) = 1{∃ k, x_k > uₙ}`, this is the **sliding-blocks extremal-index estimator**

  `θ̂^{sb} = #{i < n - rₙ + 1 : max_{i ≤ t < i + rₙ} X_t > uₙ} / (rₙ · #{i < n : X_i > uₙ})`.

Cissokho and Kulik (2021, §5.3) ask for consistency of sliding-blocks cluster estimators without
relying on `β`-mixing. We establish consistency under **strong (`α`-)mixing** rates alone, via
Ibragimov's `L^∞` covariance inequality for `α`-mixing σ-algebras (`abs_covariance_le_strongMixingCoeff`)
and Chebyshev's inequality.

## Main results

* `abs_covariance_le_strongMixingCoeff`: **Ibragimov's `L^∞` mixing covariance inequality**: if
  `U` is `m₁`-measurable, `V` is `m₂`-measurable (`m₁, m₂ ≤ mΩ`) and `|U|, |V| ≤ M`, then
  `|cov[U, V; P]| ≤ 4 M² α(m₁, m₂)`. Proved via the layer-cake representation on `[0, 2M]` and Fubini.
* `variance_sum_le_of_cov_le`: lag-bounded variance inequality for arbitrary square-integrable
  sums (generalizing `variance_sum_ite_mem_le`).
* `variance_slidingClusterSum_le`: variance bound for overlapping sliding-block sums of bounded
  cluster functionals vanishing on non-exceedance blocks, using only `P(M_r > u)` for lags
  `h < r + l` and `4 M² α(h - r + 1)` for lags `h ≥ r + l`.
* `tendstoInMeasure_slidingClusterSum_div`: concentration of the normalized sliding-block cluster
  sum `(∑_{i < n - rₙ + 1} Hₙ(W_i)) / (rₙ n pₙ)` around its population limit `μ`, under
  **`α`-mixing rates only** (`∑_{lₙ < g < n} α(g) = o(n (rₙ pₙ)²)`, with `lₙ / rₙ` bounded).
* `tendstoInMeasure_slidingClusterEstimator`: **consistency of sliding-blocks estimators for
  general bounded cluster functionals without `β`-mixing** (answering Cissokho–Kulik 2021, §5.3).
* `tendstoInMeasure_slidingBlocksEstimator`,
  `tendstoInMeasure_slidingBlocksEstimator_of_isMDependent`,
  `HasSpectralTailProcess.tendstoInMeasure_slidingBlocksEstimator`: consistency of the
  sliding-blocks extremal-index estimator under `α`-mixing, `m`-dependence, and anticlustering.

## Scope

* Bounded measurable cluster functionals vanishing on non-exceedance blocks; unbounded functionals
  (cf. Chen–Kulik 2023) and asymptotic normality are not covered here.
* Thresholds are deterministic intermediate sequences (`n pₙ → ∞`), not random order statistics.

## References

* Y. Cissokho and R. Kulik, *Estimation of cluster functionals for regularly varying time series:
  sliding blocks estimators*, Electron. J. Statist. 15 (2021), §5.3.
* I. A. Ibragimov, *Some limit theorems for stationary processes*, Theory Probab. Appl. 7 (1962).
* R. Kulik and P. Soulier, *Heavy-Tailed Time Series*, Springer (2020), Ch. 10.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal Classical

namespace ExtremeValueTheory

/-! ### Ibragimov's `L^∞` covariance inequality for `α`-mixing σ-algebras -/

section LayerCake

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Layer-cake identity on `[0, B]`: for `0 ≤ x ≤ B`, `∫ t in Ioo 0 B, 1_{t < x} = x`. -/
private lemma integral_Ioo_indicator_lt {B x : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B) :
    ∫ t in Set.Ioo 0 B, (if t < x then (1 : ℝ) else 0) = x := by
  have hcongr : Set.EqOn (fun t : ℝ => if t < x then (1 : ℝ) else 0)
      ((Set.Ioo 0 x).indicator (fun _ => (1 : ℝ))) (Set.Ioo 0 B) := by
    intro t ht
    by_cases htx : t < x
    · have ht' : t ∈ Set.Ioo 0 x := ⟨ht.1, htx⟩
      simp [htx, ht']
    · have ht' : t ∉ Set.Ioo 0 x := fun h => htx h.2
      simp [htx, ht']
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr,
    setIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_right.2 (Set.Ioo_subset_Ioo_right hxB),
    setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo_of_le hx0, sub_zero]

/-- Product layer-cake identity on `[0, B] × [0, B]`: for `0 ≤ x, y ≤ B`,
`∫ s in Ioo 0 B, ∫ t in Ioo 0 B, 1_{s < x ∧ t < y} = x * y`. -/
private lemma integral_Ioo_integral_Ioo_indicator_lt {B x y : ℝ}
    (hx0 : 0 ≤ x) (hxB : x ≤ B) (hy0 : 0 ≤ y) (hyB : y ≤ B) :
    ∫ s in Set.Ioo 0 B, (∫ t in Set.Ioo 0 B, if s < x ∧ t < y then (1 : ℝ) else 0) = x * y := by
  have hinner : ∀ s : ℝ, (∫ t in Set.Ioo 0 B, if s < x ∧ t < y then (1 : ℝ) else 0) =
      (if s < x then (1 : ℝ) else 0) * y := by
    intro s
    by_cases hs : s < x
    · simp only [hs, true_and, ↓reduceIte, one_mul]
      exact integral_Ioo_indicator_lt hy0 hyB
    · simp [hs]
  simp_rw [hinner, integral_mul_const, integral_Ioo_indicator_lt hx0 hxB]

/-- Layer-cake covariance bound for nonnegative bounded measurable functions whose upper-level
events satisfy `|P({s < f} ∩ {t < g}) - P{s < f} P{t < g}| ≤ α`. -/
private lemma abs_integral_mul_sub_le_of_forall_inter {f g : Ω → ℝ} {B α : ℝ} (hB : 0 ≤ B)
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ ω, 0 ≤ f ω) (hfB : ∀ ω, f ω ≤ B)
    (hg0 : ∀ ω, 0 ≤ g ω) (hgB : ∀ ω, g ω ≤ B)
    (hα : ∀ s t : ℝ, |P.real ({ω | s < f ω} ∩ {ω | t < g ω}) -
      P.real {ω | s < f ω} * P.real {ω | t < g ω}| ≤ α) :
    |∫ ω, f ω * g ω ∂P - (∫ ω, f ω ∂P) * (∫ ω, g ω ∂P)| ≤ B ^ 2 * α := by
  set μ : Measure ℝ := volume.restrict (Set.Ioo 0 B) with hμ_def
  have : IsFiniteMeasure μ := ⟨by
    rw [hμ_def, Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  have hIf : ∫ ω, f ω ∂P = ∫ s, P.real {ω | s < f ω} ∂μ := by
    have h1 : ∀ ω, f ω = ∫ s, (if s < f ω then (1 : ℝ) else 0) ∂μ :=
      fun ω => (integral_Ioo_indicator_lt (hf0 ω) (hfB ω)).symm
    conv_lhs => arg 2; ext ω; rw [h1 ω]
    have hm : Measurable (fun p : Ω × ℝ => if p.2 < f p.1 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_snd (hf.comp measurable_fst))
        measurable_const measurable_const
    have hint : Integrable (fun p : Ω × ℝ => if p.2 < f p.1 then (1 : ℝ) else 0) (P.prod μ) :=
      Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ fun p => by split_ifs <;> norm_num)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    dsimp only
    have heq : (fun ω => if s < f ω then (1 : ℝ) else 0) = {ω | s < f ω}.indicator 1 := by
      ext ω; simp [Set.indicator]
    rw [heq, integral_indicator_one (measurableSet_lt measurable_const hf)]
  have hIg : ∫ ω, g ω ∂P = ∫ t, P.real {ω | t < g ω} ∂μ := by
    have h1 : ∀ ω, g ω = ∫ t, (if t < g ω then (1 : ℝ) else 0) ∂μ :=
      fun ω => (integral_Ioo_indicator_lt (hg0 ω) (hgB ω)).symm
    conv_lhs => arg 2; ext ω; rw [h1 ω]
    have hm : Measurable (fun p : Ω × ℝ => if p.2 < g p.1 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_snd (hg.comp measurable_fst))
        measurable_const measurable_const
    have hint : Integrable (fun p : Ω × ℝ => if p.2 < g p.1 then (1 : ℝ) else 0) (P.prod μ) :=
      Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ fun p => by split_ifs <;> norm_num)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    dsimp only
    have heq : (fun ω => if t < g ω then (1 : ℝ) else 0) = {ω | t < g ω}.indicator 1 := by
      ext ω; simp [Set.indicator]
    rw [heq, integral_indicator_one (measurableSet_lt measurable_const hg)]
  have hIfg : ∫ ω, f ω * g ω ∂P =
      ∫ p : ℝ × ℝ, P.real ({ω | p.1 < f ω} ∩ {ω | p.2 < g ω}) ∂(μ.prod μ) := by
    have h1 : ∀ ω, f ω * g ω =
        ∫ p : ℝ × ℝ, (if p.1 < f ω ∧ p.2 < g ω then (1 : ℝ) else 0) ∂(μ.prod μ) := by
      intro ω
      have hmω : Measurable (fun p : ℝ × ℝ => if p.1 < f ω ∧ p.2 < g ω then (1 : ℝ) else 0) :=
        Measurable.ite ((measurableSet_lt measurable_fst measurable_const).inter
          (measurableSet_lt measurable_snd measurable_const)) measurable_const measurable_const
      have hiω : Integrable (fun p : ℝ × ℝ => if p.1 < f ω ∧ p.2 < g ω then (1 : ℝ) else 0)
          (μ.prod μ) :=
        Integrable.of_bound hmω.aestronglyMeasurable 1
          (ae_of_all _ fun p => by split_ifs <;> norm_num)
      rw [MeasureTheory.integral_prod _ hiω]
      exact (integral_Ioo_integral_Ioo_indicator_lt (hf0 ω) (hfB ω) (hg0 ω) (hgB ω)).symm
    conv_lhs => arg 2; ext ω; rw [h1 ω]
    have hm : Measurable (fun q : Ω × (ℝ × ℝ) =>
        if q.2.1 < f q.1 ∧ q.2.2 < g q.1 then (1 : ℝ) else 0) :=
      Measurable.ite
        ((measurableSet_lt (measurable_fst.comp measurable_snd) (hf.comp measurable_fst)).inter
          (measurableSet_lt (measurable_snd.comp measurable_snd) (hg.comp measurable_fst)))
        measurable_const measurable_const
    have hint : Integrable (fun q : Ω × (ℝ × ℝ) =>
        if q.2.1 < f q.1 ∧ q.2.2 < g q.1 then (1 : ℝ) else 0) (P.prod (μ.prod μ)) :=
      Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ fun q => by split_ifs <;> norm_num)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    dsimp only
    have heq : (fun ω => if p.1 < f ω ∧ p.2 < g ω then (1 : ℝ) else 0) =
        ({ω | p.1 < f ω} ∩ {ω | p.2 < g ω}).indicator 1 := by
      ext ω; simp [Set.indicator]
    rw [heq, integral_indicator_one
      ((measurableSet_lt measurable_const hf).inter (measurableSet_lt measurable_const hg))]
  have hIfIg : (∫ ω, f ω ∂P) * (∫ ω, g ω ∂P) =
      ∫ p : ℝ × ℝ, P.real {ω | p.1 < f ω} * P.real {ω | p.2 < g ω} ∂(μ.prod μ) := by
    rw [hIf, hIg, ← integral_prod_mul]
  have hmeas_pf : Measurable (fun s : ℝ => P.real {ω | s < f ω}) := by
    have : (fun s : ℝ => P.real {ω | s < f ω}) =
        fun s => ∫ ω, (if s < f ω then (1 : ℝ) else 0) ∂P := by
      funext s
      have heq : (fun ω => if s < f ω then (1 : ℝ) else 0) = {ω | s < f ω}.indicator 1 := by
        ext ω; simp [Set.indicator]
      rw [heq, integral_indicator_one (measurableSet_lt measurable_const hf)]
    rw [this]
    have hm : Measurable (fun q : ℝ × Ω => if q.1 < f q.2 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_fst (hf.comp measurable_snd))
        measurable_const measurable_const
    exact hm.stronglyMeasurable.integral_prod_right.measurable
  have hmeas_pg : Measurable (fun t : ℝ => P.real {ω | t < g ω}) := by
    have : (fun t : ℝ => P.real {ω | t < g ω}) =
        fun t => ∫ ω, (if t < g ω then (1 : ℝ) else 0) ∂P := by
      funext t
      have heq : (fun ω => if t < g ω then (1 : ℝ) else 0) = {ω | t < g ω}.indicator 1 := by
        ext ω; simp [Set.indicator]
      rw [heq, integral_indicator_one (measurableSet_lt measurable_const hg)]
    rw [this]
    have hm : Measurable (fun q : ℝ × Ω => if q.1 < g q.2 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_fst (hg.comp measurable_snd))
        measurable_const measurable_const
    exact hm.stronglyMeasurable.integral_prod_right.measurable
  have hmeas_inter : Measurable (fun p : ℝ × ℝ => P.real ({ω | p.1 < f ω} ∩ {ω | p.2 < g ω})) := by
    have : (fun p : ℝ × ℝ => P.real ({ω | p.1 < f ω} ∩ {ω | p.2 < g ω})) =
        fun p => ∫ ω, (if p.1 < f ω ∧ p.2 < g ω then (1 : ℝ) else 0) ∂P := by
      funext p
      have heq : (fun ω => if p.1 < f ω ∧ p.2 < g ω then (1 : ℝ) else 0) =
          ({ω | p.1 < f ω} ∩ {ω | p.2 < g ω}).indicator 1 := by
        ext ω; simp [Set.indicator]
      rw [heq, integral_indicator_one
        ((measurableSet_lt measurable_const hf).inter (measurableSet_lt measurable_const hg))]
    rw [this]
    have hm : Measurable (fun q : (ℝ × ℝ) × Ω =>
        if q.1.1 < f q.2 ∧ q.1.2 < g q.2 then (1 : ℝ) else 0) :=
      Measurable.ite
        ((measurableSet_lt (measurable_fst.comp measurable_fst) (hf.comp measurable_snd)).inter
          (measurableSet_lt (measurable_snd.comp measurable_fst) (hg.comp measurable_snd)))
        measurable_const measurable_const
    exact hm.stronglyMeasurable.integral_prod_right.measurable
  have hint1 : Integrable (fun p : ℝ × ℝ => P.real ({ω | p.1 < f ω} ∩ {ω | p.2 < g ω}))
      (μ.prod μ) :=
    Integrable.of_bound hmeas_inter.aestronglyMeasurable 1 (ae_of_all _ fun _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have hint2 : Integrable (fun p : ℝ × ℝ => P.real {ω | p.1 < f ω} * P.real {ω | p.2 < g ω})
      (μ.prod μ) :=
    Integrable.of_bound ((hmeas_pf.comp measurable_fst).mul
      (hmeas_pg.comp measurable_snd)).aestronglyMeasurable 1 (ae_of_all _ fun _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)]
      exact (mul_le_mul measureReal_le_one measureReal_le_one measureReal_nonneg zero_le_one).trans_eq
        (one_mul 1))
  rw [hIfg, hIfIg, ← integral_sub hint1 hint2]
  have hnorm := norm_integral_le_integral_norm
    (fun p : ℝ × ℝ => P.real ({ω | p.1 < f ω} ∩ {ω | p.2 < g ω}) -
      P.real {ω | p.1 < f ω} * P.real {ω | p.2 < g ω}) (μ := μ.prod μ)
  simp only [Real.norm_eq_abs] at hnorm
  have hle := hnorm.trans (integral_mono (hint1.sub hint2).abs (integrable_const α) fun p => hα p.1 p.2)
  rw [integral_const, smul_eq_mul, Measure.real_def, ← Set.univ_prod_univ, Measure.prod_prod,
    ENNReal.toReal_mul, hμ_def, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith), sub_zero] at hle
  linarith [show B * B = B ^ 2 by ring]

/-- Signed version of the layer-cake covariance bound: if `|U|, |V| ≤ M` and upper-level events
of `U + M` and `V + M` satisfy `|P({s < U + M} ∩ {t < V + M}) - P{s < U + M} P{t < V + M}| ≤ α`,
then `|cov[U, V; P]| ≤ 4 M² α`. -/
private lemma abs_covariance_le_of_forall_inter {U V : Ω → ℝ} {M α : ℝ} (hM : 0 ≤ M)
    (hU : Measurable U) (hV : Measurable V)
    (hUM : ∀ ω, |U ω| ≤ M) (hVM : ∀ ω, |V ω| ≤ M)
    (hα : ∀ s t : ℝ, |P.real ({ω | s < U ω + M} ∩ {ω | t < V ω + M}) -
      P.real {ω | s < U ω + M} * P.real {ω | t < V ω + M}| ≤ α) :
    |cov[U, V; P]| ≤ 4 * M ^ 2 * α := by
  set f : Ω → ℝ := fun ω => U ω + M
  set g : Ω → ℝ := fun ω => V ω + M
  have hU2 : MemLp U 2 P := MemLp.of_bound hU.aestronglyMeasurable M
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hUM ω)
  have hV2 : MemLp V 2 P := MemLp.of_bound hV.aestronglyMeasurable M
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hVM ω)
  have hU1 : Integrable U P := hU2.integrable one_le_two
  have hV1 : Integrable V P := hV2.integrable one_le_two
  have hcov_eq : cov[U, V; P] = ∫ ω, f ω * g ω ∂P - (∫ ω, f ω ∂P) * (∫ ω, g ω ∂P) := by
    rw [covariance_eq_sub hU2 hV2]
    have hIf : ∫ ω, f ω ∂P = (∫ ω, U ω ∂P) + M := by
      simp [f, integral_add hU1 (integrable_const M)]
    have hIg : ∫ ω, g ω ∂P = (∫ ω, V ω ∂P) + M := by
      simp [g, integral_add hV1 (integrable_const M)]
    have hUV : Integrable (fun ω => U ω * V ω) P := hU2.integrable_mul hV2
    have hIfg : ∫ ω, f ω * g ω ∂P =
        (∫ ω, U ω * V ω ∂P) + M * (∫ ω, U ω ∂P) + M * (∫ ω, V ω ∂P) + M ^ 2 := by
      have hexp : (fun ω => f ω * g ω) = fun ω =>
          U ω * V ω + M * U ω + M * V ω + M ^ 2 := by
        funext ω; simp only [f, g]; ring
      have h1 : Integrable (fun ω => U ω * V ω + M * U ω) P := hUV.add (hU1.const_mul M)
      have h2 : Integrable (fun ω => U ω * V ω + M * U ω + M * V ω) P := h1.add (hV1.const_mul M)
      rw [hexp, integral_add h2 (integrable_const _), integral_add h1 (hV1.const_mul M),
        integral_add hUV (hU1.const_mul M), integral_const_mul, integral_const_mul]
      simp
    rw [hIf, hIg, hIfg]
    simp only [Pi.mul_apply]
    ring
  rw [hcov_eq]
  have h := abs_integral_mul_sub_le_of_forall_inter (B := 2 * M) (by linarith)
    (hU.add_const M) (hV.add_const M)
    (fun ω => by linarith [neg_abs_le (U ω), hUM ω])
    (fun ω => by linarith [le_abs_self (U ω), hUM ω])
    (fun ω => by linarith [neg_abs_le (V ω), hVM ω])
    (fun ω => by linarith [le_abs_self (V ω), hVM ω]) hα
  linarith [show (2 * M) ^ 2 = 4 * M ^ 2 by ring]

/-- **Variance of a sum of square-integrable random variables with lag-bounded covariances.** -/
theorem variance_sum_le_of_cov_le {Y : ℕ → Ω → ℝ} (hY : ∀ i, MemLp (Y i) 2 P) (m : ℕ)
    {b : ℕ → ℝ} (hb0 : ∀ h, 0 ≤ b h)
    (hcov : ∀ i h, i + h < m → cov[Y i, Y (i + h); P] ≤ b h) :
    variance (fun ω => ∑ i ∈ range m, Y i ω) P ≤
      m * (b 0 + 2 * ∑ h ∈ Ico 1 m, b h) := by
  rw [variance_fun_sum' fun i _ => hY i]
  have hc : ∀ i ∈ range m, ∀ j ∈ range m, cov[Y i, Y j; P] ≤ b (i - j + (j - i)) := by
    intro i hi j hj
    rw [Finset.mem_range] at hi hj
    rcases le_total i j with hij | hij
    · obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [show i - (i + h) + (i + h - i) = h by omega]
      exact hcov i h hj
    · obtain ⟨h, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [covariance_comm, show j + h - j + (j - (j + h)) = h by omega]
      exact hcov j h hi
  exact (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hc i hi j hj).trans
    (sum_sum_dist_le hb0 m)

end LayerCake

section Ibragimov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Ibragimov's `L^∞` covariance inequality for `α`-mixing σ-algebras** (Ibragimov 1962):
if `U` is `m₁`-measurable, `V` is `m₂`-measurable (`m₁, m₂ ≤ mΩ`), and `|U|, |V| ≤ M` (`0 ≤ M`),
then `|cov[U, V; P]| ≤ 4 M² α(m₁, m₂)`. -/
theorem abs_covariance_le_strongMixingCoeff {m₁ m₂ : MeasurableSpace Ω}
    (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) {U V : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hU : Measurable[m₁] U) (hV : Measurable[m₂] V)
    (hUM : ∀ ω, |U ω| ≤ M) (hVM : ∀ ω, |V ω| ≤ M) :
    |cov[U, V; P]| ≤ 4 * M ^ 2 * (strongMixingCoeff m₁ m₂ P).toReal := by
  have hUΩ : Measurable[mΩ] U := hU.mono h₁ le_rfl
  have hVΩ : Measurable[mΩ] V := hV.mono h₂ le_rfl
  refine @abs_covariance_le_of_forall_inter Ω mΩ P _ U V M
    (strongMixingCoeff m₁ m₂ P).toReal hM hUΩ hVΩ hUM hVM fun s t => ?_
  have hA : MeasurableSet[m₁] {ω | s < U ω + M} :=
    (hU.add_const M) measurableSet_Ioi
  have hB : MeasurableSet[m₂] {ω | t < V ω + M} :=
    (hV.add_const M) measurableSet_Ioi
  exact abs_measureReal_inter_sub_le_strongMixingCoeff hA hB

end Ibragimov

/-! ### Sliding blocks: definitions and variance bounds -/

section SlidingDefs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The `i`-th sliding block window `(X_i, …, X_{i + r - 1})` of length `r`. -/
def slidingBlockWindow (X : ℕ → Ω → ℝ) (r i : ℕ) (ω : Ω) : Fin r → ℝ :=
  fun k => X (i + k.1) ω

/-- The event that the `i`-th sliding block `{i, …, i + r - 1}` contains an exceedance of `u`. -/
def slidingBlockEvent (X : ℕ → Ω → ℝ) (r i : ℕ) (u : ℝ) : Set Ω :=
  (maxLE X (Ico i (i + r)) u)ᶜ

/-- The sum of a cluster functional `H` over the first `m` sliding blocks of length `r`. -/
noncomputable def slidingClusterSum (X : ℕ → Ω → ℝ) (r m : ℕ) (H : (Fin r → ℝ) → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ range m, H (slidingBlockWindow X r i ω)

/-- **The sliding-blocks cluster estimator** (Cissokho and Kulik 2021):
`(∑_{i < n - r + 1} H(X_i, …, X_{i+r-1})) / (r · #{i < n : X_i > u})`. -/
noncomputable def slidingClusterEstimator (X : ℕ → Ω → ℝ) (n r : ℕ) (u : ℝ)
    (H : (Fin r → ℝ) → ℝ) (ω : Ω) : ℝ :=
  slidingClusterSum X r (n - r + 1) H ω / (r * tailCount X n u ω)

/-- The indicator of an exceedance in a block of length `r`: `1` if some entry exceeds `u`,
`0` otherwise. -/
noncomputable def blockExceedInd (r : ℕ) (u : ℝ) (x : Fin r → ℝ) : ℝ :=
  if ∃ k : Fin r, u < x k then 1 else 0

/-- The number of the first `m` sliding blocks of length `r` containing an exceedance of `u`. -/
noncomputable def slidingBlockCount (X : ℕ → Ω → ℝ) (r m : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  slidingClusterSum X r m (blockExceedInd r u) ω

/-- **The sliding-blocks estimator of the extremal index**:
`#{i < n - r + 1 : max_{i ≤ t < i + r} X_t > u} / (r · #{i < n : X_i > u})`. -/
noncomputable def slidingBlocksEstimator (X : ℕ → Ω → ℝ) (n r : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  slidingClusterEstimator X n r u (blockExceedInd r u) ω

variable {X : ℕ → Ω → ℝ}

lemma measurable_slidingBlockWindow_of_comap_le {m' : MeasurableSpace Ω} {r i : ℕ}
    (h : ∀ k : Fin r, MeasurableSpace.comap (X (i + k.1)) inferInstance ≤ m') :
    Measurable[m'] (slidingBlockWindow X r i) := by
  rw [measurable_pi_iff]
  intro k
  exact fun s hs => h k _ ⟨s, hs, rfl⟩

lemma measurable_slidingBlockWindow (hX : ∀ t, Measurable (X t)) (r i : ℕ) :
    Measurable (slidingBlockWindow X r i) := by
  rw [measurable_pi_iff]
  intro k
  exact hX (i + k.1)

lemma measurable_blockExceedInd (r : ℕ) (u : ℝ) : Measurable (blockExceedInd r u) := by
  have hs : MeasurableSet {x : Fin r → ℝ | ∃ k : Fin r, u < x k} := by
    have : {x : Fin r → ℝ | ∃ k : Fin r, u < x k} = ⋃ k : Fin r, {x | u < x k} := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iUnion fun k => measurableSet_lt measurable_const (measurable_pi_apply k)
  exact Measurable.ite hs measurable_const measurable_const

lemma blockExceedInd_eq_ite_mem (X : ℕ → Ω → ℝ) (r i : ℕ) (u : ℝ) (ω : Ω) :
    blockExceedInd r u (slidingBlockWindow X r i ω) =
      if ω ∈ slidingBlockEvent X r i u then 1 else 0 := by
  have hiff : (∃ k : Fin r, u < slidingBlockWindow X r i ω k) ↔ ω ∈ slidingBlockEvent X r i u := by
    simp only [slidingBlockWindow, slidingBlockEvent, Set.mem_compl_iff, maxLE, Set.mem_ofPred_eq,
      Finset.mem_Ico, not_forall, not_le]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨i + k.1, ⟨by omega, by omega⟩, hk⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, ht⟩; exact ⟨⟨t - i, by omega⟩, by rwa [Nat.add_sub_cancel' ht1]⟩
  simp [blockExceedInd, hiff]

lemma slidingBlockEvent_zero_eq_blockEvent (X : ℕ → Ω → ℝ) (r : ℕ) (u : ℝ) :
    slidingBlockEvent X r 0 u = blockEvent X r 0 u := by
  simp [slidingBlockEvent, blockEvent]

variable [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- For a stationary sequence, the expectation of `H(slidingBlockWindow X r i)` does not depend
on `i`. -/
theorem _root_.ProbabilityTheory.IsStationary.integral_slidingBlockWindow
    (hs : IsStationary X P) (hX : ∀ t, Measurable (X t)) (r i : ℕ)
    {H : (Fin r → ℝ) → ℝ} (hH : Measurable H) :
    ∫ ω, H (slidingBlockWindow X r i ω) ∂P = ∫ ω, H (slidingBlockWindow X r 0 ω) ∂P := by
  set φ : (ℕ → ℝ) → ℝ := fun x => H (fun k : Fin r => x k.1)
  have hφ : Measurable φ := hH.comp (measurable_pi_iff.2 fun k => measurable_pi_apply k.1)
  have h1 : (fun ω => H (slidingBlockWindow X r i ω)) = fun ω => φ (fun n => X (n + i) ω) := by
    funext ω; simp only [φ]; congr 1; funext k; simp only [slidingBlockWindow]; rw [add_comm]
  have h2 : (fun ω => H (slidingBlockWindow X r 0 ω)) = fun ω => φ (fun n => X n ω) := by
    funext ω; simp only [φ]; congr 1; funext k; simp [slidingBlockWindow]
  have hmap : P.map (fun ω n => X (n + i) ω) = P.map (fun ω n => X n ω) := hs.map_shift hX i
  rw [h1, h2, ← integral_map (measurable_pi_iff.2 fun n => hX (n + i)).aemeasurable
    hφ.aestronglyMeasurable, hmap,
    integral_map (measurable_pi_iff.2 fun n => hX n).aemeasurable hφ.aestronglyMeasurable]

theorem _root_.ProbabilityTheory.IsStationary.measureReal_slidingBlockEvent
    (hs : IsStationary X P) (hX : ∀ t, Measurable (X t)) (r i : ℕ) (u : ℝ) :
    P.real (slidingBlockEvent X r i u) = P.real (blockEvent X r 0 u) := by
  simp only [slidingBlockEvent, blockEvent]
  rw [probReal_compl_eq_one_sub (measurableSet_maxLE hX _ u),
    probReal_compl_eq_one_sub (measurableSet_maxLE hX _ u),
    hs.measureReal_maxLE_Ico hX, hs.measureReal_maxLE_Ico hX]

/-- Lag-`h` covariance bound for sliding blocks of length `r` with gap parameter `l` and
functional bound `M`: `2 M² P(M_r > u)` for `h < r + l`, and `4 M² α(h - r + 1)` for `h ≥ r + l`. -/
noncomputable def slidingCovBound (X : ℕ → Ω → ℝ) (P : Measure Ω) (r l : ℕ) (u M : ℝ)
    (h : ℕ) : ℝ :=
  if h < r + l then 2 * M ^ 2 * P.real (blockEvent X r 0 u)
  else 4 * M ^ 2 * (alphaMixing X P (h - r + 1)).toReal

omit [IsProbabilityMeasure P] in
theorem slidingCovBound_nonneg (r l : ℕ) (u M : ℝ) (h : ℕ) :
    0 ≤ slidingCovBound X P r l u M h := by
  unfold slidingCovBound
  split_ifs
  · exact mul_nonneg (by positivity) measureReal_nonneg
  · exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

/-- Covariance bound for two sliding-block cluster functional evaluations at lag `h`. -/
theorem covariance_slidingCluster_le (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {r : ℕ} (hr : 0 < r) (l : ℕ) {u M : ℝ} (hM : 0 ≤ M)
    {H : (Fin r → ℝ) → ℝ} (hHm : Measurable H)
    (hHb : ∀ x, |H x| ≤ M) (hH0 : ∀ x, (∀ k : Fin r, x k ≤ u) → H x = 0)
    (i h : ℕ) :
    cov[fun ω => H (slidingBlockWindow X r i ω),
        fun ω => H (slidingBlockWindow X r (i + h) ω); P] ≤
      slidingCovBound X P r l u M h := by
  set Yi : Ω → ℝ := fun ω => H (slidingBlockWindow X r i ω)
  set Yj : Ω → ℝ := fun ω => H (slidingBlockWindow X r (i + h) ω)
  have hYiM : ∀ ω, |Yi ω| ≤ M := fun ω => hHb _
  have hYjM : ∀ ω, |Yj ω| ≤ M := fun ω => hHb _
  have hYim : Measurable Yi := hHm.comp (measurable_slidingBlockWindow hX r i)
  have hYjm : Measurable Yj := hHm.comp (measurable_slidingBlockWindow hX r (i + h))
  have hYi2 : MemLp Yi 2 P := MemLp.of_bound hYim.aestronglyMeasurable M
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hYiM ω)
  have hYj2 : MemLp Yj 2 P := MemLp.of_bound hYjm.aestronglyMeasurable M
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hYjM ω)
  have hYi1 : Integrable Yi P := hYi2.integrable one_le_two
  have hYj1 : Integrable Yj P := hYj2.integrable one_le_two
  unfold slidingCovBound
  split_ifs with hlt
  · -- Short / overlapping lag `h < r + l`: bound via `|Yi| ≤ M · 1_{slidingBlockEvent}`
    have hYi_ind : ∀ ω, |Yi ω| ≤ (slidingBlockEvent X r i u).indicator (fun _ => M) ω := by
      intro ω
      by_cases hmem : ω ∈ slidingBlockEvent X r i u
      · rw [Set.indicator_of_mem hmem]; exact hYiM ω
      · rw [Set.indicator_of_notMem hmem]
        have hall : ∀ k : Fin r, slidingBlockWindow X r i ω k ≤ u := by
          intro k
          simp only [slidingBlockEvent, Set.mem_compl_iff, not_not, maxLE, Set.mem_ofPred_eq,
            Finset.mem_Ico] at hmem
          exact hmem (i + k.1) ⟨by omega, by omega⟩
        simp [Yi, hH0 _ hall]
    have hBi_meas : MeasurableSet (slidingBlockEvent X r i u) :=
      (measurableSet_maxLE hX _ u).compl
    have hint_ind : Integrable ((slidingBlockEvent X r i u).indicator (fun _ => M)) P :=
      (integrable_const M).indicator hBi_meas
    have hE_abs_Yi : ∫ ω, |Yi ω| ∂P ≤ M * P.real (blockEvent X r 0 u) := by
      calc ∫ ω, |Yi ω| ∂P
          ≤ ∫ ω, (slidingBlockEvent X r i u).indicator (fun _ => M) ω ∂P :=
            integral_mono hYi1.abs hint_ind hYi_ind
        _ = P.real (slidingBlockEvent X r i u) * M := by
            rw [integral_indicator_const _ hBi_meas, smul_eq_mul]
        _ = M * P.real (blockEvent X r 0 u) := by
            rw [hs.measureReal_slidingBlockEvent hX, mul_comm]
    have hE_prod : ∫ ω, Yi ω * Yj ω ∂P ≤ M ^ 2 * P.real (blockEvent X r 0 u) := by
      calc ∫ ω, Yi ω * Yj ω ∂P
          ≤ ∫ ω, |Yi ω * Yj ω| ∂P := integral_mono (hYi2.integrable_mul hYj2)
            (hYi2.integrable_mul hYj2).abs fun ω => le_abs_self _
        _ ≤ ∫ ω, M * |Yi ω| ∂P := by
            refine integral_mono (hYi2.integrable_mul hYj2).abs (hYi1.abs.const_mul M)
              fun ω => ?_
            rw [abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (hYjM ω) (abs_nonneg _)
        _ = M * ∫ ω, |Yi ω| ∂P := integral_const_mul M _
        _ ≤ M * (M * P.real (blockEvent X r 0 u)) := mul_le_mul_of_nonneg_left hE_abs_Yi hM
        _ = M ^ 2 * P.real (blockEvent X r 0 u) := by ring
    have hE_Yi_le : |∫ ω, Yi ω ∂P| ≤ M * P.real (blockEvent X r 0 u) :=
      (abs_integral_le_integral_abs).trans hE_abs_Yi
    have hE_Yj_le : |∫ ω, Yj ω ∂P| ≤ M := by
      calc |∫ ω, Yj ω ∂P| ≤ ∫ ω, |Yj ω| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ _, M ∂P := integral_mono hYj1.abs (integrable_const M) hYjM
        _ = M := by simp
    have hE_prod2 : -((∫ ω, Yi ω ∂P) * (∫ ω, Yj ω ∂P)) ≤ M ^ 2 * P.real (blockEvent X r 0 u) := by
      calc -((∫ ω, Yi ω ∂P) * (∫ ω, Yj ω ∂P))
          ≤ |(∫ ω, Yi ω ∂P) * (∫ ω, Yj ω ∂P)| := neg_le_abs _
        _ = |∫ ω, Yi ω ∂P| * |∫ ω, Yj ω ∂P| := abs_mul _ _
        _ ≤ (M * P.real (blockEvent X r 0 u)) * M :=
            mul_le_mul hE_Yi_le hE_Yj_le (abs_nonneg _) (mul_nonneg hM measureReal_nonneg)
        _ = M ^ 2 * P.real (blockEvent X r 0 u) := by ring
    rw [covariance_eq_sub hYi2 hYj2]
    simp only [Pi.mul_apply]
    linarith
  · -- Separated blocks `h ≥ r + l`: apply Ibragimov's `L^∞` `α`-mixing covariance inequality
    set s := i + r - 1
    have hle_past : pastMeasurableSpace X s ≤ mΩ :=
      iSup₂_le fun t _ => (hX t).comap_le
    have hle_fut : futureMeasurableSpace X (s + (h - r + 1)) ≤ mΩ :=
      iSup₂_le fun t _ => (hX t).comap_le
    have hYi_past : Measurable[pastMeasurableSpace X s] Yi :=
      hHm.comp (measurable_slidingBlockWindow_of_comap_le fun k =>
        comap_le_pastMeasurableSpace (by omega))
    have hYj_fut : Measurable[futureMeasurableSpace X (s + (h - r + 1))] Yj :=
      hHm.comp (measurable_slidingBlockWindow_of_comap_le fun k =>
        comap_le_futureMeasurableSpace (by omega))
    have hIbr := abs_covariance_le_strongMixingCoeff (P := P) hle_past hle_fut hM hYi_past hYj_fut
      hYiM hYjM
    have hα : (strongMixingCoeff (pastMeasurableSpace X s)
        (futureMeasurableSpace X (s + (h - r + 1))) P).toReal ≤
        (alphaMixing X P (h - r + 1)).toReal :=
      ENNReal.toReal_mono (alphaMixing_ne_top _) (le_iSup (fun s' =>
        strongMixingCoeff (pastMeasurableSpace X s')
          (futureMeasurableSpace X (s' + (h - r + 1))) P) s)
    calc cov[Yi, Yj; P] ≤ |cov[Yi, Yj; P]| := le_abs_self _
      _ ≤ 4 * M ^ 2 * (strongMixingCoeff (pastMeasurableSpace X s)
            (futureMeasurableSpace X (s + (h - r + 1))) P).toReal := hIbr
      _ ≤ 4 * M ^ 2 * (alphaMixing X P (h - r + 1)).toReal := by gcongr

omit [IsProbabilityMeasure P] in
/-- Summing `slidingCovBound` over `1 ≤ h < m`, for `r ≥ 1`. -/
theorem sum_slidingCovBound_le {r : ℕ} (hr : 0 < r) (l m : ℕ) (u M : ℝ) :
    ∑ h ∈ Ico 1 m, slidingCovBound X P r l u M h ≤
      (r + l : ℝ) * (2 * M ^ 2 * P.real (blockEvent X r 0 u)) +
        4 * M ^ 2 * ∑ g ∈ Ico (l + 1) m, (alphaMixing X P g).toReal := by
  set β := 2 * M ^ 2 * P.real (blockEvent X r 0 u)
  set a : ℕ → ℝ := fun g => (alphaMixing X P g).toReal
  have hβ : 0 ≤ β := mul_nonneg (by positivity) measureReal_nonneg
  have ha : ∀ g, 0 ≤ a g := fun _ => ENNReal.toReal_nonneg
  calc ∑ h ∈ Ico 1 m, slidingCovBound X P r l u M h
      = ∑ h ∈ (Ico 1 m).filter (· < r + l), β +
          ∑ h ∈ (Ico 1 m).filter (fun h => ¬ h < r + l), 4 * M ^ 2 * a (h - r + 1) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Ico 1 m) (· < r + l)]
        congr 1
        · refine Finset.sum_congr rfl fun h hh => ?_
          simp [slidingCovBound, (Finset.mem_filter.1 hh).2, β]
        · refine Finset.sum_congr rfl fun h hh => ?_
          simp [slidingCovBound, (Finset.mem_filter.1 hh).2, a]
    _ ≤ (r + l : ℝ) * β + 4 * M ^ 2 * ∑ g ∈ Ico (l + 1) m, a g := by
        refine add_le_add ?_ ?_
        · rw [Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ hβ
          have hsub : (Ico 1 m).filter (· < r + l) ⊆ range (r + l) := fun h hh =>
            Finset.mem_range.2 (Finset.mem_filter.1 hh).2
          exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
        · rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Finset.sum_image (g := fun h => h - r + 1) (fun x hx y hy hxy => by
            simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at hx hy hxy
            omega)]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun g hg => ?_) fun g _ _ => ha g
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico] at hg
          obtain ⟨h, ⟨⟨hh1, hh2⟩, hh3⟩, rfl⟩ := hg
          simp only [Finset.mem_Ico]
          omega

/-- **Variance of a sliding-blocks cluster sum**: for a stationary sequence, block length `r ≥ 1`,
auxiliary gap `l`, and bounded measurable functional `H` (`|H| ≤ M`) vanishing on blocks without
an exceedance of `u`,
`Var(∑_{i<m} H(W_i)) ≤ m * (2 M² (1 + 2(r + l)) P(M_r > u) + 8 M² ∑_{l < g < m} α(g))`. -/
theorem variance_slidingClusterSum_le (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {r : ℕ} (hr : 0 < r) (l m : ℕ) {u M : ℝ} (hM : 0 ≤ M)
    {H : (Fin r → ℝ) → ℝ} (hHm : Measurable H)
    (hHb : ∀ x, |H x| ≤ M) (hH0 : ∀ x, (∀ k : Fin r, x k ≤ u) → H x = 0) :
    variance (slidingClusterSum X r m H) P ≤
      m * (2 * M ^ 2 * (1 + 2 * (r + l : ℝ)) * P.real (blockEvent X r 0 u) +
        8 * M ^ 2 * ∑ g ∈ Ico (l + 1) m, (alphaMixing X P g).toReal) := by
  have hY2 : ∀ i, MemLp (fun ω => H (slidingBlockWindow X r i ω)) 2 P := fun i =>
    MemLp.of_bound (hHm.comp (measurable_slidingBlockWindow hX r i)).aestronglyMeasurable M
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hHb _)
  have hV := variance_sum_le_of_cov_le hY2 m (slidingCovBound_nonneg (X := X) (P := P) r l u M)
    (fun i h _ => covariance_slidingCluster_le hX hs hr l hM hHm hHb hH0 i h)
  have h0 : slidingCovBound X P r l u M 0 = 2 * M ^ 2 * P.real (blockEvent X r 0 u) := by
    have : 0 < r + l := by omega
    simp [slidingCovBound, this]
  rw [h0] at hV
  have hsum := sum_slidingCovBound_le (X := X) (P := P) hr l m u M
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  calc variance (slidingClusterSum X r m H) P
      ≤ m * (2 * M ^ 2 * P.real (blockEvent X r 0 u) +
          2 * ∑ h ∈ Ico 1 m, slidingCovBound X P r l u M h) := hV
    _ ≤ m * (2 * M ^ 2 * P.real (blockEvent X r 0 u) +
          2 * ((r + l : ℝ) * (2 * M ^ 2 * P.real (blockEvent X r 0 u)) +
            4 * M ^ 2 * ∑ g ∈ Ico (l + 1) m, (alphaMixing X P g).toReal)) := by gcongr
    _ = _ := by ring

end SlidingDefs

/-! ### Concentration and consistency of sliding-blocks cluster estimators without `β`-mixing -/

section SlidingConsistency

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- **Concentration of the sliding-blocks cluster sum under `α`-mixing** (Cissokho–Kulik 2021, §5.3).
Let `X` be stationary, `rₙ ≥ 1`, `rₙ / n → 0`, `n pₙ → ∞`, and let `Hₙ` be bounded measurable
cluster functionals (`|Hₙ| ≤ M`) vanishing on blocks without an exceedance of `uₙ`, with
`E[Hₙ(W_0)] / (rₙ pₙ) → μ`. If for some auxiliary gap sequence `lₙ` with `lₙ ≤ C rₙ` we have
`∑_{lₙ < g < n} α(g) / (n (rₙ pₙ)²) → 0`, then

  `(∑_{i < n - rₙ + 1} Hₙ(W_i)) / (rₙ n pₙ) → μ` in probability.

No `β`-mixing is assumed. -/
theorem tendstoInMeasure_slidingClusterSum_div (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {u : ℕ → ℝ} {r l : ℕ → ℕ} {M μ C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    {H : (n : ℕ) → (Fin (r n) → ℝ) → ℝ} (hHm : ∀ n, Measurable (H n))
    (hHb : ∀ n x, |H n x| ≤ M)
    (hH0 : ∀ n x, (∀ k : Fin (r n), x k ≤ u n) → H n x = 0)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hμ : Tendsto (fun n => (∫ ω, H n (slidingBlockWindow X (r n) 0 ω) ∂P) /
      (r n * P.real {ω | u n < X 0 ω})) atTop (𝓝 μ))
    (hl : ∀ᶠ n in atTop, (l n : ℝ) ≤ C * r n)
    (hmix : Tendsto (fun n => (∑ g ∈ Ico (l n + 1) n, (alphaMixing X P g).toReal) /
      (n * (r n * P.real {ω | u n < X 0 ω}) ^ 2)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => slidingClusterSum X (r n) (n - r n + 1) (H n) ω /
      (r n * (n * P.real {ω | u n < X 0 ω}))) atTop (fun _ => μ) := by
  set p : ℕ → ℝ := fun n => P.real {ω | u n < X 0 ω} with hp
  have hpos := hk.eventually_gt_atTop 0
  have hgood : ∀ᶠ n in atTop, 0 < r n ∧ r n ≤ n ∧ (0 : ℝ) < n ∧ 0 < p n ∧ (l n : ℝ) ≤ C * r n := by
    filter_upwards [hpos, hr, hrn.eventually (gt_mem_nhds one_pos), hl] with n hn hr0 hr1 hln
    obtain ⟨hn0, hp0⟩ := pos_and_pos_of_mul_pos hn
    refine ⟨hr0, ?_, hn0, hp0, hln⟩
    rw [div_lt_one hn0] at hr1
    exact_mod_cast hr1.le
  have hnorm_pos : ∀ᶠ n in atTop, 0 < (r n : ℝ) * (n * p n) := by
    filter_upwards [hgood] with n ⟨hr0, _, hn0, hp0, _⟩
    have hrR : (0 : ℝ) < r n := by exact_mod_cast hr0
    positivity
  have hS2 : ∀ n, MemLp (slidingClusterSum X (r n) (n - r n + 1) (H n)) 2 P := fun n =>
    memLp_finsetSum _ fun i _ =>
      MemLp.of_bound ((hHm n).comp (measurable_slidingBlockWindow hX (r n) i)).aestronglyMeasurable M
        (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hHb n _)
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine (tendsto_measure_abs_div_sub_of_variance
    (S := fun n => slidingClusterSum X (r n) (n - r n + 1) (H n))
    (c := μ) hS2 hnorm_pos ?_ ?_ hε).congr fun n => ?_
  · -- The mean: `((n - rₙ + 1) / n) * (E[Hₙ(W_0)] / (rₙ pₙ)) → 1 * μ = μ`
    have hfrac : Tendsto (fun n : ℕ => ((n - r n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
      have h1 : Tendsto (fun n : ℕ => 1 - (r n : ℝ) / n + (1 : ℝ) / n) atTop (𝓝 (1 - 0 + 0)) :=
        (tendsto_const_nhds.sub hrn).add
          (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
      simp only [sub_zero, add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [hgood] with n ⟨_, hrle, hn0, _, _⟩
      rw [Nat.cast_add, Nat.cast_sub hrle, Nat.cast_one]
      field_simp
    have hmean := hfrac.mul hμ
    rw [one_mul] at hmean
    refine hmean.congr' ?_
    filter_upwards [hgood] with n ⟨hr0, _, hn0, hp0, _⟩
    have hrR : (0 : ℝ) < r n := by exact_mod_cast hr0
    have hInt : ∀ i, Integrable (fun ω => H n (slidingBlockWindow X (r n) i ω)) P := fun i =>
      (MemLp.of_bound ((hHm n).comp (measurable_slidingBlockWindow hX (r n) i)).aestronglyMeasurable
        M (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hHb n _)).integrable one_le_two
    have hsumE : ∫ ω, slidingClusterSum X (r n) (n - r n + 1) (H n) ω ∂P =
        ((n - r n + 1 : ℕ) : ℝ) * ∫ ω, H n (slidingBlockWindow X (r n) 0 ω) ∂P := by
      unfold slidingClusterSum
      rw [integral_finsetSum _ fun i _ => hInt i]
      simp only [hs.integral_slidingBlockWindow hX (r n) _ (hHm n), sum_const, card_range,
        nsmul_eq_mul]
    rw [hsumE, hp]
    have hp0' : 0 < P.real {ω | u n < X 0 ω} := hp0
    field_simp
  · -- The variance: `≤ 2 M² (3 + 2 C) / (n pₙ) + 8 M² (∑_{lₙ < g < n} α(g)) / (n (rₙ pₙ)²) → 0`
    have hlim := ((tendsto_inv_atTop_zero.comp hk).const_mul (2 * M ^ 2 * (3 + 2 * C))).add
      (hmix.const_mul (8 * M ^ 2))
    simp only [mul_zero, add_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun n => by
      have := variance_nonneg (slidingClusterSum X (r n) (n - r n + 1) (H n)) P; positivity)
      ?_ hlim
    filter_upwards [hgood] with n ⟨hr0, hrle, hn0, hp0, hln⟩
    have hrR : (0 : ℝ) < r n := by exact_mod_cast hr0
    have hr1 : (1 : ℝ) ≤ r n := by exact_mod_cast hr0
    set m := n - r n + 1
    have hmn : m ≤ n := by omega
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hβle : P.real (blockEvent X (r n) 0 (u n)) ≤ r n * p n :=
      hs.measureReal_blockEvent_le hX (r n) 0 (u n)
    have hsum_α : ∑ g ∈ Ico (l n + 1) m, (alphaMixing X P g).toReal ≤
        ∑ g ∈ Ico (l n + 1) n, (alphaMixing X P g).toReal :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hmn)
        fun _ _ _ => ENNReal.toReal_nonneg
    have hsum_α0 : 0 ≤ ∑ g ∈ Ico (l n + 1) n, (alphaMixing X P g).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have h12 : (1 : ℝ) + 2 * (r n + l n : ℝ) ≤ (3 + 2 * C) * r n := by nlinarith
    have hV := variance_slidingClusterSum_le hX hs hr0 (l n) m hM (hHm n) (hHb n) (hH0 n)
    have hV' : variance (slidingClusterSum X (r n) m (H n)) P ≤
        n * (2 * M ^ 2 * ((3 + 2 * C) * r n) * (r n * p n) +
          8 * M ^ 2 * ∑ g ∈ Ico (l n + 1) n, (alphaMixing X P g).toReal) := by
      refine hV.trans ?_
      have hnonneg1 : 0 ≤ 2 * M ^ 2 * (1 + 2 * (r n + l n : ℝ)) * P.real (blockEvent X (r n) 0 (u n)) :=
        mul_nonneg (by positivity) measureReal_nonneg
      have hnonneg2 : 0 ≤ 8 * M ^ 2 * ∑ g ∈ Ico (l n + 1) m, (alphaMixing X P g).toReal :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      calc (m : ℝ) * (2 * M ^ 2 * (1 + 2 * (r n + l n : ℝ)) * P.real (blockEvent X (r n) 0 (u n)) +
              8 * M ^ 2 * ∑ g ∈ Ico (l n + 1) m, (alphaMixing X P g).toReal)
          ≤ n * (2 * M ^ 2 * (1 + 2 * (r n + l n : ℝ)) * P.real (blockEvent X (r n) 0 (u n)) +
              8 * M ^ 2 * ∑ g ∈ Ico (l n + 1) m, (alphaMixing X P g).toReal) := by gcongr
        _ ≤ n * (2 * M ^ 2 * ((3 + 2 * C) * r n) * (r n * p n) +
              8 * M ^ 2 * ∑ g ∈ Ico (l n + 1) n, (alphaMixing X P g).toReal) := by gcongr
    calc variance (slidingClusterSum X (r n) m (H n)) P / (r n * (n * p n)) ^ 2
        ≤ n * (2 * M ^ 2 * ((3 + 2 * C) * r n) * (r n * p n) +
            8 * M ^ 2 * ∑ g ∈ Ico (l n + 1) n, (alphaMixing X P g).toReal) /
            (r n * (n * p n)) ^ 2 := by gcongr
      _ = 2 * M ^ 2 * (3 + 2 * C) * (n * p n)⁻¹ +
            8 * M ^ 2 * ((∑ g ∈ Ico (l n + 1) n, (alphaMixing X P g).toReal) /
              (n * (r n * p n) ^ 2)) := by
          simp only [hp]; field_simp
  · simp [Real.dist_eq, hp]

/-- **Consistency of the sliding-blocks cluster estimator without `β`-mixing**
(Cissokho and Kulik 2021, §5.3). Under `α`-mixing rates alone, the self-normalized sliding-blocks
estimator `(∑_{i < n - rₙ + 1} Hₙ(W_i)) / (rₙ · #{i < n : X_i > uₙ})` converges in probability to
`μ = lim E[Hₙ(W_0)] / (rₙ pₙ)`. -/
theorem tendstoInMeasure_slidingClusterEstimator (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {u : ℕ → ℝ} {r l s : ℕ → ℕ} {M μ C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    {H : (n : ℕ) → (Fin (r n) → ℝ) → ℝ} (hHm : ∀ n, Measurable (H n))
    (hHb : ∀ n x, |H n x| ≤ M)
    (hH0 : ∀ n x, (∀ k : Fin (r n), x k ≤ u n) → H n x = 0)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hμ : Tendsto (fun n => (∫ ω, H n (slidingBlockWindow X (r n) 0 ω) ∂P) /
      (r n * P.real {ω | u n < X 0 ω})) atTop (𝓝 μ))
    (hclus : Tendsto (fun n : ℕ => (∑ h ∈ Icc 1 (s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0))
    (hmixT : Tendsto (fun n : ℕ => (∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0))
    (hl : ∀ᶠ n in atTop, (l n : ℝ) ≤ C * r n)
    (hmixB : Tendsto (fun n => (∑ g ∈ Ico (l n + 1) n, (alphaMixing X P g).toReal) /
      (n * (r n * P.real {ω | u n < X 0 ω}) ^ 2)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => slidingClusterEstimator X n (r n) (u n) (H n)) atTop
      (fun _ => μ) := by
  have hA := tendstoInMeasure_slidingClusterSum_div hX hs hM hC hHm hHb hH0 hr hrn hk hμ hl hmixB
  have hN0 := tendstoInMeasure_tailCount_div hX hs hk s hclus hmixT
  have hc : ∀ᶠ n in atTop, (r n : ℝ) * (n * P.real {ω | u n < X 0 ω}) ≠ 0 := by
    filter_upwards [hr, hk.eventually_gt_atTop 0] with n hr0 hn
    have hrR : (0 : ℝ) < r n := by exact_mod_cast hr0
    exact (mul_pos hrR hn).ne'
  have hN : TendstoInMeasure P (fun n ω => (r n * tailCount X n (u n) ω) /
      (r n * (n * P.real {ω | u n < X 0 ω}))) atTop (fun _ => 1) := by
    refine tendstoInMeasure_of_eventuallyEq hN0 ?_
    filter_upwards [hr] with n hr0 ω
    have hrR : (r n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hr0.ne'
    field_simp
  exact tendstoInMeasure_div_of_div hc hA hN

/-- **Consistency of the sliding-blocks extremal-index estimator under `α`-mixing**
(no `β`-mixing): specializes `tendstoInMeasure_slidingClusterEstimator` to
`Hₙ = blockExceedInd rₙ uₙ` with `lₙ = rₙ`, requiring only `∑_{rₙ < g < n} α(g) = o(n (rₙ pₙ)²)`. -/
theorem tendstoInMeasure_slidingBlocksEstimator (hX : ∀ t, Measurable (X t)) (hs : IsStationary X P)
    {u : ℕ → ℝ} {r s : ℕ → ℕ} {θ : ℝ}
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hθ : Tendsto (fun n => P.real (blockEvent X (r n) 0 (u n)) /
      (r n * P.real {ω | u n < X 0 ω})) atTop (𝓝 θ))
    (hclus : Tendsto (fun n : ℕ => (∑ h ∈ Icc 1 (s n), P.real {ω | u n < X 0 ω ∧ u n < X h ω}) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0))
    (hmixT : Tendsto (fun n : ℕ => (∑ h ∈ Ico (s n + 1) n, (alphaMixing X P h).toReal) /
      (n * P.real {ω | u n < X 0 ω} ^ 2)) atTop (𝓝 0))
    (hmixB : Tendsto (fun n => (∑ g ∈ Ico (r n + 1) n, (alphaMixing X P g).toReal) /
      (n * (r n * P.real {ω | u n < X 0 ω}) ^ 2)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => slidingBlocksEstimator X n (r n) (u n)) atTop (fun _ => θ) := by
  refine tendstoInMeasure_slidingClusterEstimator hX hs (M := 1) (C := 1) zero_le_one zero_le_one
    (H := fun n => blockExceedInd (r n) (u n))
    (fun n => measurable_blockExceedInd (r n) (u n))
    (fun n x => by unfold blockExceedInd; split_ifs <;> norm_num)
    (fun n x hx => by
      unfold blockExceedInd
      have : ¬ ∃ k : Fin (r n), u n < x k := by push Not; exact hx
      simp [this])
    hr hrn hk ?_ hclus hmixT (Eventually.of_forall fun n => by linarith) hmixB
  refine hθ.congr fun n => ?_
  congr 1
  have heq : (fun ω => blockExceedInd (r n) (u n) (slidingBlockWindow X (r n) 0 ω)) =
      (blockEvent X (r n) 0 (u n)).indicator 1 := by
    ext ω
    rw [blockExceedInd_eq_ite_mem, slidingBlockEvent_zero_eq_blockEvent, Set.indicator_apply]
    rfl
  rw [heq, integral_indicator_one (measurableSet_blockEvent hX (r n) 0 (u n))]

/-- Sufficient pointwise mixing condition: `α(rₙ + 1) = o((rₙ pₙ)²)` implies the summed
`α`-mixing condition `∑_{rₙ < g < n} α(g) = o(n (rₙ pₙ)²)`. -/
theorem tendsto_sum_alphaMixing_sliding_of_pointwise {u : ℕ → ℝ} {r : ℕ → ℕ}
    (hmix : Tendsto (fun n => (alphaMixing X P (r n + 1)).toReal /
      (r n * P.real {ω | u n < X 0 ω}) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (∑ g ∈ Ico (r n + 1) n, (alphaMixing X P g).toReal) /
      (n * (r n * P.real {ω | u n < X 0 ω}) ^ 2)) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => div_nonneg (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
    (by positivity)) (fun n => ?_) hmix
  by_cases hden : (n : ℝ) * (r n * P.real {ω | u n < X 0 ω}) ^ 2 = 0
  · rw [hden, div_zero]
    exact div_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  · have hn0 : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp at hden
      · exact_mod_cast h
    have hsum : ∑ g ∈ Ico (r n + 1) n, (alphaMixing X P g).toReal ≤
        n * (alphaMixing X P (r n + 1)).toReal := by
      calc ∑ g ∈ Ico (r n + 1) n, (alphaMixing X P g).toReal
          ≤ ∑ _g ∈ Ico (r n + 1) n, (alphaMixing X P (r n + 1)).toReal :=
            Finset.sum_le_sum fun g hg => ENNReal.toReal_mono (alphaMixing_ne_top _)
              (alphaMixing_anti X (Finset.mem_Ico.1 hg).1)
        _ = ((n - (r n + 1) : ℕ) : ℝ) * (alphaMixing X P (r n + 1)).toReal := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ n * (alphaMixing X P (r n + 1)).toReal := by
            gcongr; exact_mod_cast Nat.sub_le n (r n + 1)
    calc (∑ g ∈ Ico (r n + 1) n, (alphaMixing X P g).toReal) /
            (n * (r n * P.real {ω | u n < X 0 ω}) ^ 2)
        ≤ (n * (alphaMixing X P (r n + 1)).toReal) /
            (n * (r n * P.real {ω | u n < X 0 ω}) ^ 2) := by gcongr
      _ = (alphaMixing X P (r n + 1)).toReal / (r n * P.real {ω | u n < X 0 ω}) ^ 2 := by
          rw [mul_div_mul_left _ _ hn0.ne']

/-- **Consistency of the sliding-blocks extremal-index estimator for `m`-dependent sequences**:
the cluster and mixing conditions are automatic. -/
theorem tendstoInMeasure_slidingBlocksEstimator_of_isMDependent (hX : ∀ t, Measurable (X t))
    (hs : IsStationary X P) {m : ℕ} (hm : IsMDependent X m P) {u : ℕ → ℝ} {r : ℕ → ℕ} {θ : ℝ}
    (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < X 0 ω}) atTop atTop)
    (hθ : Tendsto (fun n => P.real (blockEvent X (r n) 0 (u n)) /
      (r n * P.real {ω | u n < X 0 ω})) atTop (𝓝 θ)) :
    TendstoInMeasure P (fun n => slidingBlocksEstimator X n (r n) (u n)) atTop (fun _ => θ) := by
  refine tendstoInMeasure_slidingBlocksEstimator hX hs (hr.eventually_gt_atTop 0) hrn hk hθ
    (s := fun _ => m)
    (tendsto_sum_measureReal_lt_and_lt_div_of_isMDependent hX hs hm hk
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop))
    (tendsto_sum_alphaMixing_div_of_isMDependent hm (Eventually.of_forall fun _ => le_rfl) _)
    (tendsto_sum_alphaMixing_sliding_of_pointwise ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hr.eventually_ge_atTop m] with n hn
  rw [hm.alphaMixing_eq_zero (by omega), ENNReal.toReal_zero, zero_div]

/-- **Consistency of the sliding-blocks estimator for `|X|` with a spectral tail process**:
under forward anticlustering and `α`-mixing rates (no `β`-mixing), the sliding-blocks estimator
applied to `|X|` converges in probability to the candidate extremal index `ϑ`. -/
theorem HasSpectralTailProcess.tendstoInMeasure_slidingBlocksEstimator
    {X : ℤ → Ω → ℝ}
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Θ : ℤ → Ω' → ℝ} {α : ℝ} (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hAC : ForwardAntiClusteringAt P X u r)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hk : Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop atTop) (s : ℕ → ℕ)
    (hclus : Tendsto (fun n : ℕ =>
      (∑ h ∈ Icc 1 (s n), P.real {ω | u n < |X 0 ω| ∧ u n < |X h ω|}) /
        (n * P.real {ω | u n < |X 0 ω|} ^ 2)) atTop (𝓝 0))
    (hmixT : Tendsto (fun n : ℕ =>
      (∑ h ∈ Ico (s n + 1) n, (alphaMixing (fun k : ℕ => |X k|) P h).toReal) /
        (n * P.real {ω | u n < |X 0 ω|} ^ 2)) atTop (𝓝 0))
    (hmixB : Tendsto (fun n =>
      (∑ g ∈ Ico (r n + 1) n, (alphaMixing (fun k : ℕ => |X k|) P g).toReal) /
        (n * (r n * P.real {ω | u n < |X 0 ω|}) ^ 2)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => slidingBlocksEstimator (fun k : ℕ => |X k|) n (r n) (u n))
      atTop (fun _ => (candidateExtremalIndex Q Θ α).toReal) := by
  have hXa : ∀ t : ℕ, Measurable ((fun k : ℕ => |X k|) t) := fun t =>
    continuous_abs.measurable.comp (hX t)
  refine _root_.ExtremeValueTheory.tendstoInMeasure_slidingBlocksEstimator
    (X := fun k : ℕ => |X k|) hXa (hstat.isStationary_abs hX) (hr.eventually_gt_atTop 0) hrn
    (by simpa using hk) ?_ (s := s) (by simpa using hclus) (by simpa using hmixT)
    (by simpa using hmixB)
  simp only [blockEvent_abs]
  simpa using h.tendsto_blockRatio hα hX hΘm hstat hu hr hAC

end SlidingConsistency

end ExtremeValueTheory
