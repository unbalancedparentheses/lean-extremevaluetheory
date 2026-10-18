/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.DomainOfAttractionBasic
import ExtremeValueTheory.Dependence.ExtremalIndex
import ExtremeValueTheory.StableLaws.StableIndex
import ExtremeValueTheory.GEV.MaxStable

/-!
# Multivariate maximum domains of attraction

A probability law `μ` on `ℝ^ι` (joint distribution function `F`) is in the **maximum domain of
attraction** of a law `ν` (joint distribution function `G`) with normalizations `a n > 0` and
`b n` (coordinatewise) if

  `F(a n x + b n) ^ n → G(x)` at every continuity point `x` of `G`,

i.e. the coordinatewise maxima of `n` i.i.d. copies of `X ∼ μ`, normalized by `(M_n - b n) / a n`,
converge in distribution to `ν` ([dHF, §6.1]; [Res87, §5.4]). The limit `ν` is a **multivariate
extreme value distribution** when its marginals are nondegenerate.

## Main results

* `IsMDAWith.tendsto_marginal`: the marginals converge, `F_i(a n i t + b n i) ^ n → G_i(t)` at the
  continuity points of `G_i` ([dHF, Theorem 6.1.1, (6.1.3)]); hence the marginals of a
  multivariate extreme value distribution are univariate extreme value distributions and the
  marginals of `μ` are in their domains of attraction (`IsMDAWith.isExtremeValueDistr_marginal`,
  `IsMDAWith.marginal_mem_domainOfAtraction`). In particular `G` is continuous and the convergence
  holds at every `x` (`IsMDAWith.tendsto_of_not_isDegenerate`).
* `IsMDAWith.tendsto_mul_one_sub`: `n (1 - F(a n x + b n)) → -log G(x)` wherever `G` and its
  marginals are positive.
* **Reduction to standardized margins** ([dHF, Theorem 6.1.1]; [Res87, Proposition 5.10]): with
  the tail quantile functions `U_i(s) = F_i^←(1 - 1/s)` of the marginals of `μ`,

    `n (1 - F(U_1(n y_1), …, U_d(n y_d))) → V(y) = -log G_0(y)`,  `y ∈ (0, ∞)^ι`,

  where `G_0` is the distribution function of the unit Fréchet standardization of `ν`
  (`IsMDAWith.tendsto_mul_one_sub_tailQuantile`); this holds for arbitrary marginals of `μ`.
* `IsMDAWith.isSimpleMaxStable_frechetStandardization`: the standardized limit `G_0` is simple
  max-stable, so it has the spectral representation of `MaxStable/Converse.lean`.
* `isMDAWith_iff`: the converse, for continuous marginals of `μ` and `ν`: `μ` is in the domain of
  attraction of `ν` with normalizations `(a, b)` if and only if every marginal `F_i` is in the
  domain of attraction of `G_i` with normalizations `(a n i, b n i)` and the standardized
  convergence above holds ([dHF, Theorem 6.2.1]; [Res87, Proposition 5.10]).

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Chapter 6 [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Chapter 5 [Res87].
-/

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace ExtremeValueTheory

variable {ι : Type*}

section RealLemmas

/-- `n (1 - r) ≤ r ^ (-n) - 1` for `r ∈ (0, 1]`. -/
lemma natCast_mul_one_sub_le_inv_pow_sub_one {r : ℝ} (hr0 : 0 < r) (n : ℕ) :
    n * (1 - r) ≤ (r ^ n)⁻¹ - 1 := by
  have h1 : 1 - r ≤ -Real.log r := by linarith [Real.log_le_sub_one_of_pos hr0]
  have h2 : Real.log ((r ^ n)⁻¹) ≤ (r ^ n)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.2 (pow_pos hr0 n))
  rw [Real.log_inv, Real.log_pow] at h2
  nlinarith [n.cast_nonneg (α := ℝ)]

/-- If `p n ∈ [0, 1]` and `p n ^ n → c > 0`, then `n (1 - p n) → -log c`. -/
lemma tendsto_natCast_mul_one_sub_of_tendsto_pow {p : ℕ → ℝ} {c : ℝ} (h0 : ∀ n, 0 ≤ p n)
    (h1 : ∀ n, p n ≤ 1)
    (hc : 0 < c) (h : Tendsto (fun n ↦ p n ^ n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ ↦ n * (1 - p n)) atTop (𝓝 (-Real.log c)) := by
  have hL : Tendsto (fun n ↦ -Real.log (p n ^ n)) atTop (𝓝 (-Real.log c)) :=
    ((Real.continuousAt_log hc.ne').tendsto.comp h).neg
  have hpos : ∀ᶠ n in atTop, 0 < p n := by
    filter_upwards [h.eventually (lt_mem_nhds (half_lt_self hc)), eventually_ge_atTop 1]
      with n hn hn1
    rcases (h0 n).lt_or_eq with hp | hp
    · exact hp
    · rw [← hp, zero_pow (by omega)] at hn
      linarith
  -- upper bound: `n (1 - p) ≤ -log (p ^ n)`
  have hupper : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (1 - p n) ≤ -Real.log (p n ^ n) := by
    filter_upwards [hpos] with n hn
    rw [Real.log_pow]
    nlinarith [Real.log_le_sub_one_of_pos hn, n.cast_nonneg (α := ℝ)]
  -- lower bound: `n (1 - p) ≥ p · (-log (p ^ n))`
  have hlower : ∀ᶠ n : ℕ in atTop, p n * -Real.log (p n ^ n) ≤ (n : ℝ) * (1 - p n) := by
    filter_upwards [hpos] with n hn
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hn)
    rw [Real.log_inv] at this
    have h' : p n * -Real.log (p n) ≤ 1 - p n := by
      have := mul_le_mul_of_nonneg_left this hn.le
      rwa [mul_sub, mul_inv_cancel₀ hn.ne', mul_one] at this
    rw [Real.log_pow]
    nlinarith [n.cast_nonneg (α := ℝ)]
  -- `p n → 1`
  have hp1 : Tendsto p atTop (𝓝 1) := by
    have hdiv : Tendsto (fun n : ℕ ↦ -Real.log (p n ^ n) / n) atTop (𝓝 0) := by
      have := hL.div_atTop tendsto_natCast_atTop_atTop
      simpa using this
    have h0 : Tendsto (fun n ↦ 1 - p n) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv
        (Eventually.of_forall fun n ↦ sub_nonneg.2 (h1 n)) ?_
      filter_upwards [hupper, eventually_ge_atTop 1] with n hn hn1
      rw [le_div_iff₀ (by exact_mod_cast hn1)]
      linarith
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    simpa using this
  have hlow' : Tendsto (fun n ↦ p n * -Real.log (p n ^ n)) atTop (𝓝 (-Real.log c)) := by
    simpa using hp1.mul hL
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow' hL hlower hupper

end RealLemmas

section Definitions

variable [Fintype ι]

/-- `μ` is in the **maximum domain of attraction** of `ν` with normalizations `a n > 0` and `b n`:
`F(a n x + b n) ^ n → G(x)` at every continuity point `x` of `G`, where `F(x) = μ (Iic x)` and
`G(x) = ν (Iic x)` ([dHF, §6.1]). -/
structure IsMDAWith (μ ν : Measure (ι → ℝ)) (a b : ℕ → ι → ℝ) : Prop where
  pos : ∀ n i, 0 < a n i
  tendsto : ∀ x, ContinuousAt (fun y ↦ ν.real (Iic y)) x →
    Tendsto (fun n ↦ μ.real (Iic (a n * x + b n)) ^ n) atTop (𝓝 (ν.real (Iic x)))

/-- `μ` is in the maximum domain of attraction of the **multivariate extreme value distribution**
`ν`: the marginals of `ν` are nondegenerate and `F(a n x + b n) ^ n → G(x)` for some
normalizations ([dHF, Definition 6.1.0]; [Res87, §5.4]). -/
def IsInMultivariateMDA (μ ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] : Prop :=
  (∀ i, ¬ (marginal ν i).IsDegenerate) ∧ ∃ a b : ℕ → ι → ℝ, IsMDAWith μ ν a b

end Definitions

section Marginals

variable [Fintype ι] {μ ν : Measure (ι → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {a b : ℕ → ι → ℝ}

/-- `F_i(x_i) ≤ F(x) + ∑_j (1 - F_j(m_j))` whenever `m_j ≤ x_j` for all `j ≠ i`. -/
lemma marginal_le_add_sum (x m : ι → ℝ) (i : ι) (hm : ∀ j ≠ i, m j ≤ x j) :
    marginal μ i (x i) ≤ μ.real (Iic x) + ∑ j, (1 - marginal μ j (m j)) := by
  have hsub : {z : ι → ℝ | z i ≤ x i} ⊆ Iic x ∪ ⋃ j, {z : ι → ℝ | m j < z j} := by
    intro z (hz : z i ≤ x i)
    by_cases h : z ∈ Iic x
    · exact Or.inl h
    · right
      simp only [mem_Iic, Pi.le_def, not_forall, not_le] at h
      obtain ⟨j, hj⟩ := h
      have hji : j ≠ i := fun e ↦ by subst e; linarith
      exact mem_iUnion.2 ⟨j, (hm j hji).trans_lt hj⟩
  rw [marginal_apply]
  calc μ.real {z | z i ≤ x i} ≤ μ.real (Iic x ∪ ⋃ j, {z : ι → ℝ | m j < z j}) :=
        measureReal_mono hsub
    _ ≤ μ.real (Iic x) + μ.real (⋃ j, {z : ι → ℝ | m j < z j}) := measureReal_union_le _ _
    _ ≤ μ.real (Iic x) + ∑ j, μ.real {z : ι → ℝ | m j < z j} := by
        gcongr; exact measureReal_iUnion_fintype_le _
    _ = _ := by simp only [measureReal_lt_apply]

/-- There are arbitrarily large points at which all marginals of `ν` are continuous. -/
lemma exists_gt_forall_continuousAt (K : ℝ) :
    ∃ M, K < M ∧ ∀ j, ContinuousAt (marginal ν j) M := by
  have hcount : (⋃ j, {x | ¬ ContinuousAt (marginal ν j) x}).Countable :=
    countable_iUnion fun j ↦ (marginal_mono j).countable_not_continuousAt
  obtain ⟨M, hM, hKM⟩ := (hcount.dense_compl (𝕜 := ℝ)).exists_between (lt_add_one K)
  refine ⟨M, hKM.1, fun j ↦ ?_⟩
  simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hM
  exact hM j

/-- **Convergence of the marginals** ([dHF, Theorem 6.1.1, (6.1.3)]): if
`F(a n x + b n) ^ n → G(x)` at the continuity points of `G`, then
`F_i(a n i t + b n i) ^ n → G_i(t)` at the continuity points of `G_i`. -/
theorem IsMDAWith.tendsto_marginal (h : IsMDAWith μ ν a b) (i : ι) {t : ℝ}
    (ht : ContinuousAt (marginal ν i) t) :
    Tendsto (fun n ↦ marginal μ i (a n i * t + b n i) ^ n) atTop (𝓝 (marginal ν i t)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set d : ℝ := (Fintype.card ι : ℝ) with hd_def
  have hd : 0 ≤ d := Nat.cast_nonneg _
  set δ : ℝ := min (1 / 4) (ε / (2 + 4 * d)) with hδ_def
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ14 : δ ≤ 1 / 4 := min_le_left _ _
  have hδε : (2 + 4 * d) * δ ≤ ε := by
    have := min_le_right (1 / 4 : ℝ) (ε / (2 + 4 * d))
    rw [← hδ_def, le_div_iff₀ (by positivity)] at this
    linarith
  -- a large continuity point `M` of all marginals of `ν` with small marginal tails
  have hsum : Tendsto (fun M ↦ ∑ j, (1 - marginal ν j M)) atTop (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ fun j _ ↦
      (tendsto_const_nhds (x := (1 : ℝ))).sub (marginal ν j).tendsto_atTop
    simpa using this
  obtain ⟨K, hK⟩ := (eventually_atTop.1 (hsum.eventually (gt_mem_nhds hδ0)))
  obtain ⟨M, hKM, hMc⟩ := exists_gt_forall_continuousAt (ν := ν) K
  have hMsum := hK M hKM.le
  set xM : ι → ℝ := Function.update (fun _ ↦ M) i t
  set cM : ι → ℝ := fun _ ↦ M
  have hxMi : xM i = t := Function.update_self _ _ _
  have hxMj : ∀ j ≠ i, xM j = M := fun j hj ↦ Function.update_of_ne hj _ _
  have hxM_cont : ContinuousAt (fun y ↦ ν.real (Iic y)) xM := by
    refine continuousAt_measureReal_Iic fun j ↦ ?_
    by_cases hj : j = i
    · subst hj; rw [hxMi]; exact ht
    · rw [hxMj j hj]; exact hMc j
  have hcM_cont : ContinuousAt (fun y ↦ ν.real (Iic y)) cM :=
    continuousAt_measureReal_Iic fun j ↦ hMc j
  -- bounds for the limit law
  have hG1 : ν.real (Iic xM) ≤ marginal ν i t := hxMi ▸ measureReal_Iic_le_marginal xM i
  have hG2 : marginal ν i t ≤ ν.real (Iic xM) + δ := by
    have := marginal_le_add_sum (μ := ν) xM cM i fun j hj ↦ (hxMj j hj).ge
    rw [hxMi] at this
    linarith
  have hGc : 1 - δ < ν.real (Iic cM) := by
    have := one_sub_sum_le_measureReal_Iic (μ := ν) cM
    linarith
  -- eventual bounds
  have hp := h.tendsto xM hxM_cont
  have hr := h.tendsto cM hcM_cont
  have hev : ∀ᶠ n in atTop, |marginal μ i (a n i * t + b n i) ^ n - marginal ν i t| < ε := by
    filter_upwards [hp.eventually (Ioo_mem_nhds (show ν.real (Iic xM) - δ < ν.real (Iic xM) by
      linarith) (show ν.real (Iic xM) < ν.real (Iic xM) + δ by linarith)),
      hr.eventually (lt_mem_nhds (show 1 - 2 * δ < ν.real (Iic cM) by linarith)),
      eventually_ge_atTop 1] with n hpn hrn hn1
    set p := μ.real (Iic (a n * xM + b n))
    set q := marginal μ i (a n i * t + b n i)
    set r := μ.real (Iic (a n * cM + b n))
    have hq_eq : q = marginal μ i ((a n * xM + b n) i) := by
      simp only [q, Pi.add_apply, Pi.mul_apply, hxMi]
    have hpq : p ≤ q := hq_eq ▸ measureReal_Iic_le_marginal _ i
    have hqp : q ≤ p + d * (1 - r) := by
      have h1 := marginal_le_add_sum (μ := μ) (a n * xM + b n) (a n * cM + b n) i
        fun j hj ↦ by simp only [Pi.add_apply, Pi.mul_apply, hxMj j hj, cM, le_refl]
      have h2 : ∑ j, (1 - marginal μ j ((a n * cM + b n) j)) ≤ ∑ _j : ι, (1 - r) :=
        Finset.sum_le_sum fun j _ ↦ by
          have := measureReal_Iic_le_marginal (μ := μ) (a n * cM + b n) j
          linarith
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
      rw [← hq_eq] at h1
      linarith
    have hr0 : 0 < r := by
      by_contra hcon
      have hr00 : r = 0 := le_antisymm (not_lt.1 hcon) measureReal_nonneg
      rw [hr00, zero_pow (by omega)] at hrn; linarith
    have hrn' : n * (1 - r) ≤ 4 * δ := by
      have h1 := natCast_mul_one_sub_le_inv_pow_sub_one hr0 n
      have hpos : 0 < r ^ n := pow_pos hr0 n
      have h2 : (r ^ n)⁻¹ ≤ 1 + 4 * δ := by
        rw [inv_le_iff_one_le_mul₀ hpos]
        nlinarith
      linarith
    have hpow : q ^ n - p ^ n ≤ n * (q - p) := by
      have := abs_pow_sub_pow_le_of_mem_Icc (a := q) (b := p)
        ⟨(marginal μ i).apply_nonneg _, (marginal μ i).apply_le_one _⟩
        ⟨measureReal_nonneg, measureReal_le_one⟩ n
      rw [abs_of_nonneg (sub_nonneg.2 hpq)] at this
      exact (le_abs_self _).trans this
    have hpqn : p ^ n ≤ q ^ n := pow_le_pow_left₀ measureReal_nonneg hpq n
    have hnqp : n * (q - p) ≤ d * (4 * δ) := by
      have := mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.2 hqp) (n.cast_nonneg (α := ℝ))
      nlinarith
    rw [abs_lt]
    constructor <;> nlinarith [hpn.1, hpn.2]
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨N, fun n hn ↦ by rw [Real.dist_eq]; exact hN n hn⟩

/-- **The marginals of the limit are univariate extreme value distributions** ([dHF, Theorem
6.1.1]; [Res87, Proposition 5.10]): if the `i`-th marginal of `ν` is nondegenerate, it is an
extreme value distribution. -/
theorem IsMDAWith.isExtremeValueDistr_marginal (h : IsMDAWith μ ν a b) {i : ι}
    (hnd : ¬ (marginal ν i).IsDegenerate) : (marginal ν i).IsExtremeValueDistr := by
  refine ⟨hnd, marginal μ i, fun n ↦ (AffineIncrEquiv.mkOfCoefs (h.pos n i) (b n i))⁻¹,
    fun t ht ↦ ?_⟩
  simpa only [CumulativeDistributionFunction.mulAction_apply_eq, inv_inv, AffineIncrEquiv.apply_eq,
    AffineIncrEquiv.coefs_fst_mkOfCoefs, AffineIncrEquiv.coefs_snd_mkOfCoefs] using
    h.tendsto_marginal i ht

/-- **The marginals of `μ` are in the domains of attraction of the marginals of `ν`**. -/
theorem IsMDAWith.marginal_mem_domainOfAtraction (h : IsMDAWith μ ν a b) {i : ι}
    (hnd : ¬ (marginal ν i).IsDegenerate) :
    marginal μ i ∈ (⟨marginal ν i, h.isExtremeValueDistr_marginal hnd⟩ :
      ExtremeValueDistr).domainOfAtraction :=
  ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs (h.pos n i) (b n i))⁻¹, fun t ht ↦ by
    simpa only [CumulativeDistributionFunction.mulAction_apply_eq, inv_inv, AffineIncrEquiv.apply_eq,
      AffineIncrEquiv.coefs_fst_mkOfCoefs, AffineIncrEquiv.coefs_snd_mkOfCoefs] using
      h.tendsto_marginal i ht⟩

/-- With nondegenerate marginals the limit has continuous marginals. -/
theorem IsMDAWith.continuous_marginal (h : IsMDAWith μ ν a b) {i : ι}
    (hnd : ¬ (marginal ν i).IsDegenerate) : Continuous (marginal ν i) :=
  (h.isExtremeValueDistr_marginal hnd).continuous

omit [IsProbabilityMeasure μ] in
/-- For a multivariate extreme value limit the convergence holds at every point. -/
theorem IsMDAWith.tendsto_of_continuous (h : IsMDAWith μ ν a b)
    (hc : ∀ i, Continuous (marginal ν i)) (x : ι → ℝ) :
    Tendsto (fun n ↦ μ.real (Iic (a n * x + b n)) ^ n) atTop (𝓝 (ν.real (Iic x))) :=
  h.tendsto x (continuousAt_measureReal_Iic fun i ↦ (hc i).continuousAt)

theorem IsMDAWith.tendsto_of_not_isDegenerate (h : IsMDAWith μ ν a b)
    (hnd : ∀ i, ¬ (marginal ν i).IsDegenerate) (x : ι → ℝ) :
    Tendsto (fun n ↦ μ.real (Iic (a n * x + b n)) ^ n) atTop (𝓝 (ν.real (Iic x))) :=
  h.tendsto_of_continuous (fun i ↦ h.continuous_marginal (hnd i)) x

end Marginals

end ExtremeValueTheory
