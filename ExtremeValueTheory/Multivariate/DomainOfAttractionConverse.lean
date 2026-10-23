/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.DomainOfAttractionStandardized

/-!
# Multivariate domains of attraction: the converse

For continuous marginals, membership in a multivariate maximum domain of attraction is equivalent
to the marginal domain of attraction conditions together with the convergence of the
standardized joint tail ([dHF, Theorem 6.2.1]; [Res87, Proposition 5.10]):

  `F(a n x + b n) ^ n → G(x)` for all `x`
  `⇔` `F_i(a n i t + b n i) ^ n → G_i(t)` for all `i, t`, and
      `n (1 - F(U_1(n y_1), …, U_d(n y_d))) → V(y) = -log G_0(y)` for all `y ∈ (0, ∞)^ι`,

where `U_i(s) = F_i^←(1 - 1/s)` and `G_0` is the distribution function of the unit Fréchet
standardization of `ν`.

## Main results

* `marginal_tailQuantile_eq`: `F_i(U_i(s)) = 1 - 1/s` for a continuous marginal.
* `isMDAWith_of_tendsto`: the converse direction "⇐".
* `isMDAWith_iff`: the characterization.
* `tendsto_measureReal_Iic_frechetStandardization_lower`: `G(x)` is the limit of the standardized
  distribution function along unit Fréchet points approaching the marginal values from below.
* `IsMDAWith.exists_pow_eq`: multivariate extreme value distributions are max-stable,
  `G(α x + β) ^ k = G(x)`.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Chapter 6 [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Chapter 5 [Res87].
-/

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace ExtremeValueTheory

variable {ι : Type*}

/-- For a continuous c.d.f., the tail quantile function inverts the tail exactly:
`F(U(s)) = 1 - 1/s` for `s > 1`. -/
theorem CumulativeDistributionFunction.apply_tailQuantile_eq
    {F : CumulativeDistributionFunction} (hc : Continuous F) {s : ℝ} (hs : 1 < s) :
    F (F.tailQuantile s) = 1 - 1 / s := by
  have hspec := F.tailQuantile_spec hs
  refine le_antisymm ?_ (by linarith [hspec.1])
  have ht : Tendsto F (𝓝[<] (F.tailQuantile s)) (𝓝 (F (F.tailQuantile s))) :=
    (hc.tendsto _).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun y hy ↦ by
    linarith [hspec.2 y hy])

/-- `U(s) ≤ z` as soon as `1 - F(z) ≤ 1/s`. -/
theorem CumulativeDistributionFunction.tailQuantile_le
    (F : CumulativeDistributionFunction) {s z : ℝ} (hs : 1 < s) (hz : 1 - F z ≤ 1 / s) :
    F.tailQuantile s ≤ z := by
  by_contra hcon
  linarith [(F.tailQuantile_spec hs).2 z (not_le.1 hcon)]

/-- The parametrization `y = -1 / log v` of the unit Fréchet scale by a marginal value
`v ∈ (0, 1)`: `y > 0` and `exp (-1 / y) = v`. -/
lemma frechetParam {v : ℝ} (h0 : 0 < v) (h1 : v < 1) :
    0 < -1 / Real.log v ∧ Real.exp (-1 / (-1 / Real.log v)) = v := by
  have hl : Real.log v < 0 := Real.log_neg h0 h1
  refine ⟨div_pos_of_neg_of_neg (by norm_num) hl, ?_⟩
  have : -1 / (-1 / Real.log v) = Real.log v := by field_simp
  rw [this, Real.exp_log h0]

variable [Fintype ι] {μ ν : Measure (ι → ℝ)} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] {a b : ℕ → ι → ℝ}

/-- **Approximation from below in the standardized scale**: if all marginal values
`u_i = G_i(x_i)` are positive, then `G_0(y(r)) → G(x)` as `r ↑ 1`, where `y(r)_i = -1 / log (r u_i)`
is the unit Fréchet point with `exp (-1 / y(r)_i) = r u_i`. -/
theorem tendsto_measureReal_Iic_frechetStandardization_lower
    (hcν : ∀ i, Continuous (marginal ν i)) {x : ι → ℝ} (hu0 : ∀ i, 0 < marginal ν i (x i)) :
    Tendsto (fun r : ℝ ↦ (frechetStandardization ν).real
      (Iic fun i ↦ -1 / Real.log (r * marginal ν i (x i)))) (𝓝[<] 1) (𝓝 (ν.real (Iic x))) := by
  set u : ι → ℝ := fun i ↦ marginal ν i (x i)
  have hu1 : ∀ i, u i ≤ 1 := fun i ↦ (marginal ν i).apply_le_one _
  set d : ℝ := (Fintype.card ι : ℝ) with hd_def
  set yl : ℝ → ι → ℝ := fun r i ↦ -1 / Real.log (r * u i)
  have hyl : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ i, 0 < yl r i ∧ Real.exp (-1 / yl r i) = r * u i :=
    fun r hr i ↦ frechetParam (mul_pos hr.1 (hu0 i))
      (lt_of_lt_of_le (mul_lt_of_lt_one_left (hu0 i) hr.2) (hu1 i))
  have hbound : ∀ r ∈ Ioo (0 : ℝ) 1,
      |(frechetStandardization ν).real (Iic (yl r)) - ν.real (Iic x)| ≤ d * (1 - r) := by
    intro r hr
    have hy : ∀ i, 0 < yl r i := fun i ↦ (hyl r hr i).1
    rw [measureReal_Iic_frechetStandardization_eq hcν hy]
    refine (abs_measureReal_Iic_sub_le (μ := ν) (frechetPoint ν (yl r)) x).trans ?_
    have : ∀ i, |marginal ν i (frechetPoint ν (yl r) i) - marginal ν i (x i)| ≤ 1 - r :=
      fun i ↦ by
        rw [marginal_frechetPoint hcν hy, (hyl r hr i).2,
          show r * u i - marginal ν i (x i) = -((1 - r) * u i) by ring, abs_neg,
          abs_of_nonneg (mul_nonneg (by linarith [hr.2]) (hu0 i).le)]
        nlinarith [hu1 i, hr.2]
    calc ∑ i, |marginal ν i (frechetPoint ν (yl r) i) - marginal ν i (x i)|
        ≤ ∑ _i : ι, (1 - r) := Finset.sum_le_sum fun i _ ↦ this i
      _ = d * (1 - r) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (g := fun r ↦ d * (1 - r))
    (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ ?_)
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with r hr
    rw [Real.dist_eq]; exact hbound r hr
  · have : Tendsto (fun r : ℝ ↦ d * (1 - r)) (𝓝 1) (𝓝 (d * (1 - 1))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_id)
    simpa using this.mono_left nhdsWithin_le_nhds

/-- **The converse** ([dHF, Theorem 6.2.1]; [Res87, Proposition 5.10]): for continuous marginals
of `μ` and `ν`, if every marginal of `μ` is in the domain of attraction of the corresponding
marginal of `ν` with normalizations `(a n i, b n i)`, and the standardized joint tail converges,
`n (1 - F(U_1(n y_1), …, U_d(n y_d))) → -log G_0(y)`, then `μ` is in the domain of attraction of
`ν` with normalizations `(a, b)`. -/
theorem isMDAWith_of_tendsto (hcμ : ∀ i, Continuous (marginal μ i))
    (hcν : ∀ i, Continuous (marginal ν i)) (ha : ∀ n i, 0 < a n i)
    (hmarg : ∀ i t, Tendsto (fun n ↦ marginal μ i (a n i * t + b n i) ^ n) atTop
      (𝓝 (marginal ν i t)))
    (hstd : ∀ y : ι → ℝ, (∀ i, 0 < y i) → Tendsto (fun n : ℕ ↦
      n * (1 - μ.real (Iic fun i ↦ (marginal μ i).tailQuantile (n * y i)))) atTop
      (𝓝 (maxStableExponent (frechetStandardization ν) y))) :
    IsMDAWith μ ν a b := by
  classical
  refine ⟨ha, fun x _ ↦ ?_⟩
  set ν₀ := frechetStandardization ν
  set U : ℕ → (ι → ℝ) → ι → ℝ := fun n y i ↦ (marginal μ i).tailQuantile (n * y i)
  set s : ℕ → ι → ℝ := fun n ↦ a n * x + b n
  have hs : ∀ n i, s n i = a n i * x i + b n i := fun n i ↦ rfl
  -- a vanishing marginal
  by_cases h0 : ∃ i, marginal ν i (x i) = 0
  · obtain ⟨i, hi⟩ := h0
    have hG : ν.real (Iic x) = 0 :=
      le_antisymm (hi ▸ measureReal_Iic_le_marginal x i) measureReal_nonneg
    rw [hG]
    refine squeeze_zero (fun n ↦ pow_nonneg measureReal_nonneg n)
      (fun n ↦ pow_le_pow_left₀ measureReal_nonneg (measureReal_Iic_le_marginal (s n) i) n) ?_
    simpa [hs, hi] using hmarg i (x i)
  push Not at h0
  set u : ι → ℝ := fun i ↦ marginal ν i (x i)
  have hu0 : ∀ i, 0 < u i := fun i ↦ lt_of_le_of_ne ((marginal ν i).apply_nonneg _) (h0 i).symm
  have hu1 : ∀ i, u i ≤ 1 := fun i ↦ (marginal ν i).apply_le_one _
  -- the marginal limits in logarithmic form
  have hℓ : ∀ i, Tendsto (fun n : ℕ ↦ n * (1 - marginal μ i (s n i))) atTop
      (𝓝 (-Real.log (u i))) := fun i ↦
    tendsto_natCast_mul_one_sub_of_tendsto_pow (fun _ ↦ (marginal μ i).apply_nonneg _)
      (fun _ ↦ (marginal μ i).apply_le_one _) (hu0 i) (hmarg i (x i))
  -- `n y_i > 1` eventually
  have hny : ∀ y : ι → ℝ, (∀ i, 0 < y i) → ∀ᶠ n : ℕ in atTop, ∀ i, 1 < (n : ℝ) * y i :=
    fun y hy ↦ eventually_all.2 fun i ↦
      (tendsto_natCast_atTop_atTop.atTop_mul_const (hy i)).eventually_gt_atTop 1
  -- the standardized law is positive on `(0, ∞)^ι`
  have hG0pos : ∀ y : ι → ℝ, (∀ i, 0 < y i) → 0 < ν₀.real (Iic y) := by
    intro y hy
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · have : Iic y = univ := eq_univ_of_forall fun z ↦ fun i ↦ (IsEmpty.false i).elim
      rw [this, probReal_univ]
      exact one_pos
    by_contra hcon
    have h00 : ν₀.real (Iic y) = 0 := le_antisymm (not_lt.1 hcon) measureReal_nonneg
    have hlim := hstd y hy
    rw [maxStableExponent, h00, Real.log_zero, neg_zero] at hlim
    have hge : ∀ᶠ n : ℕ in atTop, 1 / y i₀ ≤
        (n : ℝ) * (1 - μ.real (Iic fun i ↦ (marginal μ i).tailQuantile (n * y i))) := by
      filter_upwards [hny y hy] with n hn
      have h1 := measureReal_Iic_le_marginal (μ := μ)
        (fun i ↦ (marginal μ i).tailQuantile (n * y i)) i₀
      rw [(marginal μ i₀).apply_tailQuantile_eq (hcμ i₀) (hn i₀)] at h1
      have hn0 : (0 : ℝ) < n * y i₀ := lt_trans one_pos (hn i₀)
      have hn0' : (0 : ℝ) < n := by
        by_contra hc; rw [not_lt] at hc
        nlinarith [hy i₀, (n.cast_nonneg : (0 : ℝ) ≤ n)]
      have : 1 / y i₀ = (n : ℝ) * (1 / (n * y i₀)) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) hn0'.le
    have := ge_of_tendsto hlim hge
    exact absurd this (not_le.2 (one_div_pos.2 (hy i₀)))
  -- Lipschitz bound in the marginal values of `ν`
  have hlip : ∀ y : ι → ℝ, (∀ i, 0 < y i) →
      |ν₀.real (Iic y) - ν.real (Iic x)| ≤ ∑ i, |Real.exp (-1 / y i) - u i| := by
    intro y hy
    rw [measureReal_Iic_frechetStandardization_eq hcν hy]
    simpa only [marginal_frechetPoint hcν hy] using
      abs_measureReal_Iic_sub_le (μ := ν) (frechetPoint ν y) x
  set d : ℝ := (Fintype.card ι : ℝ) with hd_def
  -- the lower parametrization `exp (-1 / y_i) = r u_i`, `r ∈ (0, 1)`
  set yl : ℝ → ι → ℝ := fun r i ↦ -1 / Real.log (r * u i)
  have hyl : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ i, 0 < yl r i ∧ Real.exp (-1 / yl r i) = r * u i :=
    fun r hr i ↦ frechetParam (mul_pos hr.1 (hu0 i))
      (lt_of_lt_of_le (mul_lt_of_lt_one_left (hu0 i) hr.2) (hu1 i))
  -- positivity of `G(x)`
  have hGpos : 0 < ν.real (Iic x) := by
    have hr : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    refine (hG0pos _ fun i ↦ (hyl _ hr i).1).trans_le ?_
    rw [measureReal_Iic_frechetStandardization_eq hcν fun i ↦ (hyl _ hr i).1]
    refine measureReal_mono (Iic_subset_Iic.2 fun i ↦ ?_)
    by_contra hcon
    have h1 := marginal_mono (μ := ν) i (not_le.1 hcon).le
    rw [marginal_frechetPoint hcν (fun i ↦ (hyl _ hr i).1), (hyl _ hr i).2] at h1
    change u i ≤ 1 / 2 * u i at h1
    linarith [hu0 i]
  set L := -Real.log (ν.real (Iic x))
  have hlogc : Tendsto (fun w ↦ -Real.log w) (𝓝 (ν.real (Iic x))) (𝓝 L) :=
    ((Real.continuousAt_log hGpos.ne').tendsto).neg
  -- the upper parametrization
  set v : ℝ → ι → ℝ := fun r i ↦ if u i < 1 then u i + r * (1 - u i) else 1 - r
  set yh : ℝ → ι → ℝ := fun r i ↦ -1 / Real.log (v r i)
  have hv : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ i, 0 < v r i ∧ v r i < 1 := by
    intro r hr i
    simp only [v]
    split_ifs with h
    · constructor <;> nlinarith [hu0 i, hr.1, hr.2]
    · constructor <;> linarith [hr.1, hr.2]
  have hyh : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ i, 0 < yh r i ∧ Real.exp (-1 / yh r i) = v r i :=
    fun r hr i ↦ frechetParam (hv r hr i).1 (hv r hr i).2
  set c : ℝ → ι → ℝ := fun r i ↦ if u i < 1 then 0 else -Real.log (1 - r)
  have hyh_bound : ∀ r ∈ Ioo (0 : ℝ) 1, |ν₀.real (Iic (yh r)) - ν.real (Iic x)| ≤ d * r := by
    intro r hr
    refine (hlip _ fun i ↦ (hyh r hr i).1).trans ?_
    have : ∀ i, |Real.exp (-1 / yh r i) - u i| ≤ r := fun i ↦ by
      rw [(hyh r hr i).2]
      simp only [v]
      split_ifs with h
      · rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg hr.1.le (by linarith))]
        nlinarith [hu0 i, hr.1]
      · rw [show u i = 1 by linarith [hu1 i, not_lt.1 h], show 1 - r - 1 = -r by ring, abs_neg,
          abs_of_pos hr.1]
    calc ∑ i, |Real.exp (-1 / yh r i) - u i| ≤ ∑ _i : ι, r := Finset.sum_le_sum fun i _ ↦ this i
      _ = d * r := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- continuity of the bounds in the parameter
  have hA : Tendsto (fun r ↦ maxStableExponent ν₀ (yl r)) (𝓝[<] 1) (𝓝 L) :=
    hlogc.comp (tendsto_measureReal_Iic_frechetStandardization_lower hcν hu0)
  have hB : Tendsto (fun r ↦ maxStableExponent ν₀ (yh r) - ∑ i, c r i) (𝓝[>] 0) (𝓝 L) := by
    have h1 : Tendsto (fun r ↦ maxStableExponent ν₀ (yh r)) (𝓝[>] 0) (𝓝 L) := by
      refine hlogc.comp (tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (g := fun r ↦ d * r)
        (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ ?_))
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with r hr
        rw [Real.dist_eq]; exact hyh_bound r hr
      · have : Tendsto (fun r : ℝ ↦ d * r) (𝓝 0) (𝓝 (d * 0)) := tendsto_const_nhds.mul tendsto_id
        simpa using this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun r ↦ ∑ i, c r i) (𝓝[>] 0) (𝓝 0) := by
      have hc0 : ∀ i, Tendsto (fun r ↦ c r i) (𝓝 0) (𝓝 0) := fun i ↦ by
        simp only [c]
        split_ifs
        · exact tendsto_const_nhds
        · have : ContinuousAt (fun r : ℝ ↦ -Real.log (1 - r)) 0 :=
            ((Real.continuousAt_log (by norm_num)).comp
              (continuousAt_const.sub continuousAt_id)).neg
          simpa using this.tendsto
      have := tendsto_finsetSum Finset.univ fun i _ ↦ hc0 i
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa using h1.sub h2
  -- the logarithmic form of the joint limit
  have hjoint : Tendsto (fun n : ℕ ↦ n * (1 - μ.real (Iic (s n)))) atTop (𝓝 L) := by
    refine tendsto_order.2 ⟨fun e he ↦ ?_, fun e he ↦ ?_⟩
    · -- lower bound
      obtain ⟨r, hre, hr⟩ := ((hB.eventually (lt_mem_nhds he)).and
        (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos))).exists
      have hyhp : ∀ i, 0 < yh r i := fun i ↦ (hyh r hr i).1
      -- marginal comparison for the coordinates with `u i < 1`
      have hev : ∀ᶠ n : ℕ in atTop, ∀ i, u i < 1 →
          1 / yh r i < (n : ℝ) * (1 - marginal μ i (s n i)) := eventually_all.2 fun i ↦ by
        by_cases hui : u i < 1
        · have hlt : 1 / yh r i < -Real.log (u i) := by
            have hvi : u i < v r i := by
              simp only [v, hui, ite_true]
              nlinarith [hr.1]
            rw [one_div, show (yh r i)⁻¹ = -Real.log (v r i) by
              simp only [yh]; rw [inv_div, div_neg, div_one]]
            exact neg_lt_neg (Real.log_lt_log (hu0 i) hvi)
          exact ((hℓ i).eventually (lt_mem_nhds hlt)).mono fun n hn _ ↦ hn
        · exact Eventually.of_forall fun n h ↦ absurd h hui
      filter_upwards [hev, hny _ hyhp, (hstd _ hyhp).eventually
        (lt_mem_nhds (show e + ∑ i, c r i < maxStableExponent ν₀ (yh r) by linarith))]
        with n hn hn1 hnV
      -- the strip bounds
      have hstrip : ∀ i, (n : ℝ) * μ.real {z | U n (yh r) i < z i ∧ z i ≤ s n i} ≤ c r i := by
        intro i
        by_cases hui : u i < 1
        · have hle : s n i ≤ U n (yh r) i := by
            refine (marginal μ i).le_tailQuantile (hn1 i) ?_
            have h1 := hn i hui
            rw [div_lt_iff₀ (hyhp i)] at h1
            rw [div_lt_iff₀ (lt_trans one_pos (hn1 i))]
            linarith
          have : {z : ι → ℝ | U n (yh r) i < z i ∧ z i ≤ s n i} = ∅ := by
            ext z; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
            intro h; linarith
          simp only [this, measureReal_empty, mul_zero, c, hui, ite_true, le_refl]
        · have hsub : μ.real {z | U n (yh r) i < z i ∧ z i ≤ s n i} ≤
              μ.real {z | U n (yh r) i < z i} := measureReal_mono fun z hz ↦ hz.1
          rw [measureReal_lt_apply, (marginal μ i).apply_tailQuantile_eq (hcμ i) (hn1 i)] at hsub
          have hvi : v r i = 1 - r := by simp only [v, hui, ite_false]
          have hc_eq : c r i = 1 / yh r i := by
            have hl : Real.log (1 - r) ≠ 0 :=
              (Real.log_neg (by linarith [hr.2]) (by linarith [hr.1])).ne
            simp only [c, hui, ite_false, yh, hvi]
            field_simp
          rw [hc_eq]
          have hn0 : (n : ℝ) ≠ 0 := by
            intro h0; have := hn1 i; rw [h0, zero_mul] at this; linarith
          have : (n : ℝ) * (1 - (1 - 1 / (n * yh r i))) = 1 / yh r i := by
            field_simp
            ring
          rw [← this]
          exact mul_le_mul_of_nonneg_left hsub n.cast_nonneg
      have hmain := measureReal_Iic_le_add_sum (μ := μ) (s n) (U n (yh r))
      have hsum : (n : ℝ) * ∑ i, μ.real {z | U n (yh r) i < z i ∧ z i ≤ s n i} ≤ ∑ i, c r i := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ ↦ hstrip i
      have : (n : ℝ) * (1 - μ.real (Iic (U n (yh r)))) - ∑ i, c r i ≤
          (n : ℝ) * (1 - μ.real (Iic (s n))) := by nlinarith
      change e + ∑ i, c r i < (n : ℝ) * (1 - μ.real (Iic (U n (yh r)))) at hnV
      linarith
    · -- upper bound
      obtain ⟨r, hre, hr⟩ := ((hA.eventually (gt_mem_nhds he)).and
        (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))).exists
      have hylp : ∀ i, 0 < yl r i := fun i ↦ (hyl r hr i).1
      have hev : ∀ᶠ n : ℕ in atTop, ∀ i,
          (n : ℝ) * (1 - marginal μ i (s n i)) < 1 / yl r i := eventually_all.2 fun i ↦ by
        have hlt : -Real.log (u i) < 1 / yl r i := by
          rw [one_div, show (yl r i)⁻¹ = -Real.log (r * u i) by
            simp only [yl]; rw [inv_div, div_neg, div_one]]
          exact neg_lt_neg (Real.log_lt_log (mul_pos hr.1 (hu0 i))
            (mul_lt_of_lt_one_left (hu0 i) hr.2))
        exact (hℓ i).eventually (gt_mem_nhds hlt)
      filter_upwards [hev, hny _ hylp, (hstd _ hylp).eventually (gt_mem_nhds hre)]
        with n hn hn1 hnV
      refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (sub_le_sub_left (measureReal_mono
        (Iic_subset_Iic.2 fun i ↦ ?_)) 1) n.cast_nonneg) hnV
      refine (marginal μ i).tailQuantile_le (hn1 i) ?_
      have h1 := hn i
      rw [lt_div_iff₀ (hylp i)] at h1
      rw [le_div_iff₀ (lt_trans one_pos (hn1 i))]
      linarith
  have := tendsto_pow_of_tendsto_mul_one_sub hjoint
  rwa [neg_neg, Real.exp_log hGpos] at this

/-- **Characterization of multivariate domains of attraction** ([dHF, Theorems 6.1.1 and 6.2.1];
[Res87, Proposition 5.10]): for continuous marginals, `μ` is in the domain of attraction of `ν`
with normalizations `(a, b)` if and only if each marginal `F_i` is in the domain of attraction of
`G_i` with normalizations `(a n i, b n i)` and the standardized joint tail converges to the
exponent function of the unit Fréchet standardization of `ν`. -/
theorem isMDAWith_iff (hcμ : ∀ i, Continuous (marginal μ i))
    (hcν : ∀ i, Continuous (marginal ν i)) (ha : ∀ n i, 0 < a n i) :
    IsMDAWith μ ν a b ↔
      (∀ i t, Tendsto (fun n ↦ marginal μ i (a n i * t + b n i) ^ n) atTop
        (𝓝 (marginal ν i t))) ∧
      ∀ y : ι → ℝ, (∀ i, 0 < y i) → Tendsto (fun n : ℕ ↦
        n * (1 - μ.real (Iic fun i ↦ (marginal μ i).tailQuantile (n * y i)))) atTop
        (𝓝 (maxStableExponent (frechetStandardization ν) y)) :=
  ⟨fun h ↦ ⟨fun i _ ↦ h.tendsto_marginal i (hcν i).continuousAt,
    fun _ hy ↦ h.tendsto_mul_one_sub_tailQuantile hcν hy⟩,
    fun h ↦ isMDAWith_of_tendsto hcμ hcν ha h.1 h.2⟩

/-- **Multivariate extreme value distributions are max-stable** ([dHF, Theorem 6.1.1];
[Res87, Proposition 5.9]): if `μ` is in the domain of attraction of `ν` and the marginals of `ν`
are nondegenerate, then for every `k ≥ 1` there are `α > 0` and `β` (coordinatewise) with
`G(α x + β) ^ k = G(x)` for all `x`. -/
theorem IsMDAWith.exists_pow_eq (h : IsMDAWith μ ν a b) (hnd : ∀ i, ¬ (marginal ν i).IsDegenerate)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ α β : ι → ℝ, (∀ i, 0 < α i) ∧ ∀ x, ν.real (Iic (α * x + β)) ^ k = ν.real (Iic x) := by
  have hcν : ∀ i, Continuous (marginal ν i) := fun i ↦ h.continuous_marginal (hnd i)
  have hms := fun i ↦ ((h.isExtremeValueDistr_marginal (hnd i)).isMaxStable).2 k hk
  choose α β hα hαβ using hms
  refine ⟨α, β, hα, fun x ↦ ?_⟩
  set x' : ι → ℝ := α * x + β
  have hx' : ∀ i, marginal ν i (x' i) ^ k = marginal ν i (x i) := fun i ↦ hαβ i (x i)
  by_cases h0 : ∃ i, marginal ν i (x i) = 0
  · obtain ⟨i, hi⟩ := h0
    have hi' : marginal ν i (x' i) = 0 := by
      have := hx' i; rw [hi] at this; exact pow_eq_zero_iff (by omega) |>.1 this
    have e1 : ν.real (Iic x) = 0 :=
      le_antisymm (hi ▸ measureReal_Iic_le_marginal x i) measureReal_nonneg
    have e2 : ν.real (Iic x') = 0 :=
      le_antisymm (hi' ▸ measureReal_Iic_le_marginal x' i) measureReal_nonneg
    rw [e1, e2, zero_pow (by omega)]
  push Not at h0
  have hu0 : ∀ i, 0 < marginal ν i (x i) := fun i ↦
    lt_of_le_of_ne ((marginal ν i).apply_nonneg _) (h0 i).symm
  have hu0' : ∀ i, 0 < marginal ν i (x' i) := fun i ↦ by
    rcases ((marginal ν i).apply_nonneg (x' i)).lt_or_eq with hp | hp
    · exact hp
    · have := hx' i; rw [← hp, zero_pow (by omega)] at this; exact absurd this.symm (h0 i)
  set ν₀ := frechetStandardization ν
  have hms₀ := h.isSimpleMaxStable_frechetStandardization hcν
  set w : ℝ → ι → ℝ := fun r i ↦ -1 / Real.log (r * marginal ν i (x' i))
  set wx : ℝ → ι → ℝ := fun r i ↦ -1 / Real.log (r * marginal ν i (x i))
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- the scaling identity `G_0(w(r)) ^ k = G_0(w_x(r ^ k))`
  have hid : ∀ r ∈ Ioo (0 : ℝ) 1, ν₀.real (Iic (w r)) ^ k = ν₀.real (Iic (wx (r ^ k))) := by
    intro r hr
    have hw : ∀ i, 0 < w r i := fun i ↦ (frechetParam (mul_pos hr.1 (hu0' i))
      (lt_of_lt_of_le (mul_lt_of_lt_one_left (hu0' i) hr.2)
        ((marginal ν i).apply_le_one _))).1
    rw [hms₀.measureReal_Iic_pow (by omega) hw]
    congr 2
    funext i
    simp only [w, wx, Pi.smul_apply, smul_eq_mul]
    rw [← hx' i, ← mul_pow, Real.log_pow]
    have hl : Real.log (r * marginal ν i (x' i)) ≠ 0 :=
      (Real.log_neg (mul_pos hr.1 (hu0' i)) (lt_of_lt_of_le
        (mul_lt_of_lt_one_left (hu0' i) hr.2) ((marginal ν i).apply_le_one _))).ne
    field_simp
  have hL := ((tendsto_measureReal_Iic_frechetStandardization_lower hcν hu0').pow k)
  have hpowk : Tendsto (fun r : ℝ ↦ r ^ k) (𝓝[<] 1) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((continuous_pow k).tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 1))
      simpa using this
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with r hr
      exact pow_lt_one₀ hr.1.le hr.2 (by omega)
  have hR := (tendsto_measureReal_Iic_frechetStandardization_lower hcν hu0).comp hpowk
  refine tendsto_nhds_unique (hL.congr' ?_) hR
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with r hr
  exact hid r hr

end ExtremeValueTheory
