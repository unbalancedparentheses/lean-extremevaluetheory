/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.DomainOfAttraction

/-!
# Multivariate domains of attraction: reduction to standardized margins

For `μ` in the maximum domain of attraction of `ν` (with continuous marginals `G_i`), with the
tail quantile functions `U_i(s) = F_i^←(1 - 1/s)` of the marginals of `μ`,

  `n (1 - F(U_1(n y_1), …, U_d(n y_d))) → V(y) = -log G_0(y)`  for `y ∈ (0, ∞)^ι`,

where `G_0` is the distribution function of the unit Fréchet standardization of `ν` ([dHF,
Theorem 6.1.1]; [Res87, Proposition 5.10]). No regularity of the marginals of `μ` is needed. The
standardized limit `G_0` is a simple max-stable law (`IsSimpleMaxStable`), so that the spectral
representation of `MaxStable/Converse.lean` applies to it.

## Main results

* `IsMDAWith.tendsto_mul_one_sub_marginal`, `IsMDAWith.tendsto_mul_one_sub`: the logarithmic form
  `n (1 - F(a n x + b n)) → -log G(x)` of the domain of attraction condition.
* `IsMDAWith.measureReal_Iic_pos`: `G(x) > 0` as soon as all `G_i(x_i) > 0` (in particular
  `G(x) ≥ ∏ … > 0`, positive dependence of the limit).
* `IsMDAWith.tendsto_mul_one_sub_tailQuantile`: the standardized convergence.
* `IsMDAWith.isSimpleMaxStable_frechetStandardization`: the standardized limit is simple
  max-stable.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Chapter 6 [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Chapter 5 [Res87].
-/

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace ExtremeValueTheory

variable {ι : Type*} [Fintype ι] {μ ν : Measure (ι → ℝ)} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] {a b : ℕ → ι → ℝ}

section Logarithmic

/-- The marginal domain of attraction condition in logarithmic form:
`n (1 - F_i(a n i t + b n i)) → -log G_i(t)` when `G_i(t) > 0`. -/
theorem IsMDAWith.tendsto_mul_one_sub_marginal (h : IsMDAWith μ ν a b) (i : ι) {t : ℝ}
    (ht : ContinuousAt (marginal ν i) t) (hpos : 0 < marginal ν i t) :
    Tendsto (fun n : ℕ ↦ n * (1 - marginal μ i (a n i * t + b n i))) atTop
      (𝓝 (-Real.log (marginal ν i t))) :=
  tendsto_natCast_mul_one_sub_of_tendsto_pow (fun _ ↦ (marginal μ i).apply_nonneg _)
    (fun _ ↦ (marginal μ i).apply_le_one _) hpos (h.tendsto_marginal i ht)

omit [Fintype ι] [IsProbabilityMeasure ν] in
/-- The domain of attraction condition in logarithmic form:
`n (1 - F(a n x + b n)) → -log G(x)` when `G(x) > 0`. -/
theorem IsMDAWith.tendsto_mul_one_sub (h : IsMDAWith μ ν a b) {x : ι → ℝ}
    (hc : ContinuousAt (fun y ↦ ν.real (Iic y)) x) (hpos : 0 < ν.real (Iic x)) :
    Tendsto (fun n : ℕ ↦ n * (1 - μ.real (Iic (a n * x + b n)))) atTop
      (𝓝 (-Real.log (ν.real (Iic x)))) :=
  tendsto_natCast_mul_one_sub_of_tendsto_pow (fun _ ↦ measureReal_nonneg)
    (fun _ ↦ measureReal_le_one) hpos (h.tendsto x hc)

/-- **Positivity of the limit**: `G(x) > 0` whenever all marginals are positive (and continuous)
at `x`; indeed `G(x) ≥ exp (-1 - ∑_i -log G_i(x_i))`. -/
theorem IsMDAWith.measureReal_Iic_pos (h : IsMDAWith μ ν a b) {x : ι → ℝ}
    (hc : ∀ i, ContinuousAt (marginal ν i) (x i)) (hpos : ∀ i, 0 < marginal ν i (x i)) :
    0 < ν.real (Iic x) := by
  set L := ∑ i, -Real.log (marginal ν i (x i))
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ ↦ neg_nonneg.2
    (Real.log_nonpos ((marginal ν i).apply_nonneg _) ((marginal ν i).apply_le_one _))
  have hsum : Tendsto (fun n : ℕ ↦ ∑ i, (n : ℝ) * (1 - marginal μ i (a n i * x i + b n i)))
      atTop (𝓝 L) :=
    tendsto_finsetSum _ fun i _ ↦ h.tendsto_mul_one_sub_marginal i (hc i) (hpos i)
  set f : ℕ → ℝ := fun n ↦ 1 - (L + 1) / n
  have hf : Tendsto (fun n ↦ f n ^ n) atTop (𝓝 (Real.exp (-(L + 1)))) := by
    refine tendsto_pow_of_tendsto_mul_one_sub (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [f]
    field_simp
    ring
  have hle : ∀ᶠ n in atTop, f n ^ n ≤ μ.real (Iic (a n * x + b n)) ^ n := by
    filter_upwards [hsum.eventually (gt_mem_nhds (lt_add_one L)),
      eventually_gt_atTop ⌈L + 1⌉₊] with n hn hnL
    have hnL' : L + 1 < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hnL)
    have hn0 : (0 : ℝ) < n := by linarith
    have hf0 : 0 ≤ f n := by
      simp only [f, sub_nonneg]
      rw [div_le_one hn0]
      exact hnL'.le
    have hb := one_sub_sum_le_measureReal_Iic (μ := μ) (a n * x + b n)
    have hs : ∑ i, (1 - marginal μ i ((a n * x + b n) i)) ≤ (L + 1) / n := by
      rw [le_div_iff₀ hn0, Finset.sum_mul]
      simp only [Pi.add_apply, Pi.mul_apply]
      have : ∑ i, (1 - marginal μ i (a n i * x i + b n i)) * n =
          ∑ i, (n : ℝ) * (1 - marginal μ i (a n i * x i + b n i)) :=
        Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
      rw [this]
      exact hn.le
    exact pow_le_pow_left₀ hf0 (by simp only [f]; linarith) n
  have := le_of_tendsto_of_tendsto hf (h.tendsto x (continuousAt_measureReal_Iic hc)) hle
  exact (Real.exp_pos _).trans_le this

end Logarithmic

section FrechetPoint

/-- A point `t` with `G_i(t_i) = exp (-1 / w_i)` for all `i` (it exists for continuous marginals
and `w > 0`, by the intermediate value theorem). -/
noncomputable def frechetPoint (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (w : ι → ℝ) :
    ι → ℝ :=
  fun i ↦ Classical.epsilon fun t ↦ marginal ν i t = Real.exp (-1 / w i)

omit [Fintype ι] in
lemma marginal_frechetPoint (hc : ∀ i, Continuous (marginal ν i)) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (i : ι) :
    marginal ν i (frechetPoint ν w i) = Real.exp (-1 / w i) :=
  Classical.epsilon_spec (exists_marginal_eq ν (hc i) (Real.exp_pos _)
    (Real.exp_lt_one_iff.2 (div_neg_of_neg_of_pos (by norm_num) (hw i))))

lemma measureReal_Iic_frechetStandardization_eq (hc : ∀ i, Continuous (marginal ν i))
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    (frechetStandardization ν).real (Iic w) = ν.real (Iic (frechetPoint ν w)) :=
  measureReal_Iic_frechetStandardization hc hw (marginal_frechetPoint hc hw)

/-- The standardized distribution function is Lipschitz in the unit Fréchet marginal values. -/
lemma abs_measureReal_Iic_frechetStandardization_sub_le (hc : ∀ i, Continuous (marginal ν i))
    {w y : ι → ℝ} (hw : ∀ i, 0 < w i) (hy : ∀ i, 0 < y i) :
    |(frechetStandardization ν).real (Iic w) - (frechetStandardization ν).real (Iic y)| ≤
      ∑ i, |Real.exp (-1 / w i) - Real.exp (-1 / y i)| := by
  rw [measureReal_Iic_frechetStandardization_eq hc hw,
    measureReal_Iic_frechetStandardization_eq hc hy]
  simpa only [marginal_frechetPoint hc hw, marginal_frechetPoint hc hy] using
    abs_measureReal_Iic_sub_le (μ := ν) (frechetPoint ν w) (frechetPoint ν y)

/-- Continuity of `s ↦ G_0(s y)` at `s = 1`. -/
lemma tendsto_measureReal_Iic_frechetStandardization_smul (hc : ∀ i, Continuous (marginal ν i))
    {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    Tendsto (fun s : ℝ ↦ (frechetStandardization ν).real (Iic (s • y))) (𝓝 1)
      (𝓝 ((frechetStandardization ν).real (Iic y))) := by
  have hbound : Tendsto (fun s : ℝ ↦ ∑ i, |Real.exp (-1 / (s * y i)) - Real.exp (-1 / y i)|)
      (𝓝 1) (𝓝 0) := by
    have hcont : ∀ i, ContinuousAt (fun s : ℝ ↦ |Real.exp (-1 / (s * y i)) -
        Real.exp (-1 / y i)|) 1 := fun i ↦
      ((Real.continuous_exp.continuousAt.comp (continuousAt_const.div
        (continuousAt_id.mul continuousAt_const) (by simpa using (hy i).ne'))).sub
        continuousAt_const).abs
    have := tendsto_finsetSum Finset.univ fun i _ ↦ (hcont i).tendsto
    simpa using this
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ ↦
    dist_nonneg) ?_ hbound)
  filter_upwards [lt_mem_nhds one_pos] with s hs
  rw [Real.dist_eq]
  have hsy : ∀ i, 0 < (s • y) i := fun i ↦ by simpa using mul_pos hs (hy i)
  simpa only [Pi.smul_apply, smul_eq_mul] using
    abs_measureReal_Iic_frechetStandardization_sub_le hc hsy hy

end FrechetPoint

section Standardized

/-- **Reduction to standardized margins** ([dHF, Theorem 6.1.1]; [Res87, Proposition 5.10]): if
`μ` is in the domain of attraction of `ν` and the marginals of `ν` are continuous, then with the
tail quantile functions `U_i(s) = F_i^←(1 - 1/s)` of the marginals of `μ`,
`n (1 - F(U_1(n y_1), …, U_d(n y_d))) → V(y) = -log G_0(y)` for every `y ∈ (0, ∞)^ι`, where
`G_0` is the distribution function of the unit Fréchet standardization of `ν`. -/
theorem IsMDAWith.tendsto_mul_one_sub_tailQuantile (h : IsMDAWith μ ν a b)
    (hc : ∀ i, Continuous (marginal ν i)) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    Tendsto (fun n : ℕ ↦ n * (1 - μ.real (Iic fun i ↦ (marginal μ i).tailQuantile (n * y i))))
      atTop (𝓝 (maxStableExponent (frechetStandardization ν) y)) := by
  set H : (ι → ℝ) → ℝ := fun w ↦ (frechetStandardization ν).real (Iic w)
  have hsmul : ∀ s : ℝ, 0 < s → ∀ i, 0 < (s • y) i := fun s hs i ↦ by
    simpa using mul_pos hs (hy i)
  have hHpos : ∀ w : ι → ℝ, (∀ i, 0 < w i) → 0 < H w := fun w hw ↦ by
    simp only [H]
    rw [measureReal_Iic_frechetStandardization_eq hc hw]
    exact h.measureReal_Iic_pos (fun i ↦ (hc i).continuousAt) fun i ↦ by
      rw [marginal_frechetPoint hc hw]; exact Real.exp_pos _
  -- the joint limits along the Fréchet points
  have hlim : ∀ s : ℝ, 0 < s → Tendsto (fun n : ℕ ↦ n * (1 - μ.real (Iic
      (a n * frechetPoint ν (s • y) + b n)))) atTop (𝓝 (-Real.log (H (s • y)))) := by
    intro s hs
    have hpos : 0 < ν.real (Iic (frechetPoint ν (s • y))) := by
      rw [← measureReal_Iic_frechetStandardization_eq hc (hsmul s hs)]
      exact hHpos _ (hsmul s hs)
    have := h.tendsto_mul_one_sub (continuousAt_measureReal_Iic fun i ↦ (hc i).continuousAt)
      hpos
    simpa only [H, measureReal_Iic_frechetStandardization_eq hc (hsmul s hs)] using this
  -- the marginal limits along the Fréchet points
  have hmarg : ∀ s : ℝ, 0 < s → ∀ i, Tendsto (fun n : ℕ ↦ n * (1 - marginal μ i
      (a n i * frechetPoint ν (s • y) i + b n i))) atTop (𝓝 (1 / (s * y i))) := by
    intro s hs i
    have := h.tendsto_mul_one_sub_marginal i (hc i).continuousAt
      (by rw [marginal_frechetPoint hc (hsmul s hs)]; exact Real.exp_pos _)
    rw [marginal_frechetPoint hc (hsmul s hs), Real.log_exp] at this
    convert this using 2
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  -- continuity of `s ↦ -log G_0(s y)` at `1`
  have hcont : Tendsto (fun s : ℝ ↦ -Real.log (H (s • y))) (𝓝 1) (𝓝 (-Real.log (H y))) :=
    ((Real.continuousAt_log (hHpos y hy).ne').tendsto.comp
      (tendsto_measureReal_Iic_frechetStandardization_smul hc hy)).neg
  have hny : ∀ᶠ n : ℕ in atTop, ∀ i, 1 < (n : ℝ) * y i := eventually_all.2 fun i ↦
    (tendsto_natCast_atTop_atTop.atTop_mul_const (hy i)).eventually_gt_atTop 1
  change Tendsto _ atTop (𝓝 (-Real.log (H y)))
  refine tendsto_order.2 ⟨fun c hcL ↦ ?_, fun c hcL ↦ ?_⟩
  · -- lower bound, from Fréchet points with `s > 1`
    obtain ⟨s, hsc, hs1⟩ := (((hcont.mono_left nhdsWithin_le_nhds).eventually
      (lt_mem_nhds hcL)).and (self_mem_nhdsWithin (s := Ioi 1))).exists
    have hs0 : (0 : ℝ) < s := lt_trans one_pos hs1
    have hev : ∀ᶠ n : ℕ in atTop, ∀ i, (n : ℝ) * (1 - marginal μ i
        (a n i * frechetPoint ν (s • y) i + b n i)) < 1 / y i := eventually_all.2 fun i ↦
      (hmarg s hs0 i).eventually (gt_mem_nhds (one_div_lt_one_div_of_lt (hy i)
        (lt_mul_left (hy i) hs1)))
    filter_upwards [hev, hny, (hlim s hs0).eventually (lt_mem_nhds hsc)] with n hn hn1 hnc
    refine hnc.trans_le (mul_le_mul_of_nonneg_left (sub_le_sub_left (measureReal_mono
      (Iic_subset_Iic.2 fun i ↦ ?_)) 1) n.cast_nonneg)
    by_contra hcon
    have hspec := ((marginal μ i).tailQuantile_spec (hn1 i)).2 _ (not_le.1 hcon)
    have hy0 := hy i
    have h1 := hn i
    simp only [Pi.add_apply, Pi.mul_apply] at hspec
    rw [div_lt_iff₀ (lt_trans one_pos (hn1 i))] at hspec
    rw [lt_div_iff₀ hy0] at h1
    linarith
  · -- upper bound, from Fréchet points with `s < 1`
    obtain ⟨s, hsc, hs1⟩ := (((hcont.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds hcL)).and (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))).exists
    have hs0 : (0 : ℝ) < s := hs1.1
    have hev : ∀ᶠ n : ℕ in atTop, ∀ i, 1 / y i < (n : ℝ) * (1 - marginal μ i
        (a n i * frechetPoint ν (s • y) i + b n i)) := eventually_all.2 fun i ↦
      (hmarg s hs0 i).eventually (lt_mem_nhds (one_div_lt_one_div_of_lt (mul_pos hs0 (hy i))
        (mul_lt_of_lt_one_left (hy i) hs1.2)))
    filter_upwards [hev, hny, (hlim s hs0).eventually (gt_mem_nhds hsc)] with n hn hn1 hnc
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (sub_le_sub_left (measureReal_mono
      (Iic_subset_Iic.2 fun i ↦ ?_)) 1) n.cast_nonneg) hnc
    simp only [Pi.add_apply, Pi.mul_apply]
    refine (marginal μ i).le_tailQuantile (hn1 i) ?_
    have hy0 := hy i
    have h1 := hn i
    rw [div_lt_iff₀ hy0] at h1
    rw [div_lt_iff₀ (lt_trans one_pos (hn1 i))]
    linarith

/-- **The standardized limit is simple max-stable** ([dHF, Theorem 6.1.1]; [Res87, Proposition
5.10]): the unit Fréchet standardization `G_0` of a limit `ν` with continuous marginals satisfies
`G_0(y) ^ n = G_0(y / n)`. Hence it has a spectral measure
(`IsSimpleMaxStable.exists_hasSpectralMeasure`). -/
theorem IsMDAWith.isSimpleMaxStable_frechetStandardization (h : IsMDAWith μ ν a b)
    (hc : ∀ i, Continuous (marginal ν i)) : IsSimpleMaxStable (frechetStandardization ν) where
  isProbabilityMeasure := inferInstance
  measure_le i y hy := frechetStandardization_measure_le hc i hy
  measure_Iic_pow k hk y hy := by
    set ν₀ := frechetStandardization ν
    set U : ℕ → (ι → ℝ) → ℝ := fun n w ↦
      n * (1 - μ.real (Iic fun i ↦ (marginal μ i).tailQuantile (n * w i)))
    have hky : ∀ i, 0 < ((k : ℝ)⁻¹ • y) i := fun i ↦ by
      simpa using mul_pos (inv_pos.2 (Nat.cast_pos.2 hk)) (hy i)
    have h1 := h.tendsto_mul_one_sub_tailQuantile hc hky
    have h2 := (h.tendsto_mul_one_sub_tailQuantile hc hy).const_mul (k : ℝ)
    have hk_tend : Tendsto (fun j : ℕ ↦ k * j) atTop atTop :=
      tendsto_atTop_mono (fun j ↦ Nat.le_mul_of_pos_left j hk) tendsto_id
    have h3 := h1.comp hk_tend
    have heq : (fun j ↦ U (k * j) ((k : ℝ)⁻¹ • y)) = fun j ↦ (k : ℝ) * U j y := by
      funext j
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      simp only [U, Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
      have : ∀ i, (k : ℝ) * j * ((k : ℝ)⁻¹ * y i) = j * y i := fun i ↦ by field_simp
      simp only [this]
      ring
    have hV : maxStableExponent ν₀ ((k : ℝ)⁻¹ • y) = k * maxStableExponent ν₀ y := by
      refine tendsto_nhds_unique (h3.congr fun j ↦ ?_) h2
      exact congrFun heq j
    have hpos : ∀ w : ι → ℝ, (∀ i, 0 < w i) → 0 < ν₀.real (Iic w) := fun w hw ↦ by
      rw [measureReal_Iic_frechetStandardization_eq hc hw]
      exact h.measureReal_Iic_pos (fun i ↦ (hc i).continuousAt) fun i ↦ by
        rw [marginal_frechetPoint hc hw]; exact Real.exp_pos _
    have hreal : ν₀.real (Iic y) ^ k = ν₀.real (Iic ((k : ℝ)⁻¹ • y)) := by
      have e1 : ν₀.real (Iic y) = Real.exp (-maxStableExponent ν₀ y) := by
        rw [maxStableExponent, neg_neg, Real.exp_log (hpos y hy)]
      have e2 : ν₀.real (Iic ((k : ℝ)⁻¹ • y)) =
          Real.exp (-maxStableExponent ν₀ ((k : ℝ)⁻¹ • y)) := by
        rw [maxStableExponent, neg_neg, Real.exp_log (hpos _ hky)]
      rw [e1, e2, hV, ← Real.exp_nat_mul]
      ring_nf
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν₀ (Iic y)),
      ← ENNReal.ofReal_toReal (measure_ne_top ν₀ (Iic ((k : ℝ)⁻¹ • y))),
      ← ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    exact congrArg ENNReal.ofReal hreal

end Standardized

end ExtremeValueTheory
