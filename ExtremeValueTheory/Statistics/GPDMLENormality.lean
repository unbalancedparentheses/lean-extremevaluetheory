/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDJointNormalityNeg
import ExtremeValueTheory.Statistics.MeasurableArgmax

/-!
# Asymptotic normality of the joint GPD maximum likelihood estimator, `ξ₀ > -1/2`, `ξ₀ ≠ 0`

We combine the two regimes of the regular case `ξ₀ > -1/2` of [Smith 1985]:

* `ξ₀ > 0` (`tendstoInDistribution_gpdJointMLE`, uniform Lipschitz control of the Hessian) and
* `-1/2 < ξ₀ < 0` (`tendstoInDistribution_gpdJointMLE_neg`, one-sided control of the Hessian
  near the moving endpoint and the endpoint estimate `max_{i<n} 1/(σ₀ + ξ₀ Xᵢ) = o_P(√n)`),

into one statement for strongly consistent admissible roots of the likelihood equations
(`tendstoInDistribution_gpdJointMLE_all`), and into statements for the maximum likelihood
estimator over a compact parameter set `K ⊂ {ξ > -1, σ > 0}` with `θ₀` in its interior:

* `tendstoInDistribution_gpdMLE_all`: every (almost everywhere) measurable sequence of maximizers
  is asymptotically normal, `√n (θ̂ₙ - θ₀) ⇒ N(0, I(θ₀)⁻¹)`;
* `exists_measurable_gpdMLE`: measurable maximizers exist (the lexicographically smallest
  maximizer, `exists_measurable_isMaxOn`);
* `exists_gpdMLE_tendstoInDistribution`: **unconditional form** — there is a measurable maximum
  likelihood estimator, and it is asymptotically normal.

For a maximizer, admissibility is automatic: the log-likelihood at `θ₀` is finite almost surely,
so the maximal log-likelihood is finite and every observation lies in the support of `θ̂ₙ`; the
likelihood equations hold once `θ̂ₙ` is in the interior of `K` (`score_eq_zero_of_isMaxOn'`).

The exponential case `ξ₀ = 0` is not covered: the score and Hessian formulas used here are those
of `ξ ≠ 0` (they extend continuously to `ξ = 0`, but the extension is not formalized).

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* R. I. Jennrich, *Asymptotic properties of non-linear least squares estimators*, Ann. Math.
  Statist. 40 (1969).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

section Admissible

/-- If the extended-real log-likelihood is finite, every observation lies in the support. -/
lemma gpdLogDensityE_ne_bot_of_gpdLogLikE_ne_bot {ξ σ : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (h : gpdLogLikE ξ σ x ≠ ⊥) (i : Fin n) : gpdLogDensityE ξ σ (x i) ≠ ⊥ := by
  intro hi
  apply h
  rw [gpdLogLikE, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi, EReal.bot_add]

/-- On the support, the extended-real log-likelihood is the real log-likelihood. -/
lemma gpdLogLikE_eq_coe' {ξ σ : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ 0 < 1 + ξ * x i / σ) :
    gpdLogLikE ξ σ x = ((∑ i, log (gpdDensity ξ σ (x i)) : ℝ) : EReal) := by
  rw [gpdLogLikE, ereal_coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold gpdLogDensityE
  rw [ite_eq_left_iff.2 fun h => absurd (hx i) h]

/-- **The likelihood equations at an interior maximizer, any shape `ξ ≠ 0`.** If `θ` maximizes
the log-likelihood over `K`, lies in the interior of `K`, has `ξ ≠ 0`, `σ > 0`, and all
observations lie in its support, then both components of the score vanish at `θ`. -/
theorem score_eq_zero_of_isMaxOn' {K : Set (ℝ × ℝ)} {n : ℕ} {x : Fin n → ℝ} {θ : ℝ × ℝ}
    (hθK : θ ∈ interior K) (hθ₁ : θ.1 ≠ 0) (hθ₂ : 0 < θ.2)
    (hadm : ∀ i, 0 ≤ x i ∧ 0 < 1 + θ.1 * x i / θ.2)
    (hmax : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K θ) :
    ∑ i, gpdScoreXi θ.1 θ.2 (x i) = 0 ∧ ∑ i, gpdScoreSigma θ.1 θ.2 (x i) = 0 := by
  have hint := isOpen_interior.mem_nhds hθK
  -- nearby parameters are admissible
  have hnear : ∀ᶠ p in 𝓝 θ, 0 < p.2 ∧ ∀ i, 0 < 1 + p.1 * x i / p.2 := by
    refine (continuous_snd.continuousAt.eventually (lt_mem_nhds hθ₂)).and ?_
    refine eventually_all.2 fun i => ?_
    have hc : ContinuousAt (fun p : ℝ × ℝ => 1 + p.1 * x i / p.2) θ :=
      continuousAt_const.add ((continuous_fst.continuousAt.mul continuousAt_const).div
        continuous_snd.continuousAt hθ₂.ne')
    exact hc.eventually (lt_mem_nhds (hadm i).2)
  have hle : ∀ᶠ p in 𝓝 θ, ∑ i, log (gpdDensity p.1 p.2 (x i)) ≤
      ∑ i, log (gpdDensity θ.1 θ.2 (x i)) := by
    filter_upwards [hnear, hint] with p hp hpK
    have := hmax (interior_subset hpK)
    simp only [mem_ofPred_eq] at this
    rw [gpdLogLikE_eq_coe' (fun i => ⟨(hadm i).1, hp.2 i⟩), gpdLogLikE_eq_coe' hadm] at this
    exact EReal.coe_le_coe_iff.1 this
  constructor
  · have hd : HasDerivAt (fun ξ => ∑ i, log (gpdDensity ξ θ.2 (x i)))
        (∑ i, gpdScoreXi θ.1 θ.2 (x i)) θ.1 := by
      have := HasDerivAt.sum (u := Finset.univ) fun i _ =>
        hasDerivAt_log_gpdDensity_xi hθ₂ hθ₁ (hadm i).1
          (by have h := (hadm i).2
              have : 1 + θ.1 * x i / θ.2 = (θ.2 + θ.1 * x i) / θ.2 := by field_simp
              rw [this] at h
              exact (div_pos_iff_of_pos_right hθ₂).1 h)
      convert this using 1
      funext ξ; simp
    have hloc : IsLocalMax (fun ξ => ∑ i, log (gpdDensity ξ θ.2 (x i))) θ.1 :=
      have hc : Tendsto (fun ξ : ℝ => (ξ, θ.2)) (𝓝 θ.1) (𝓝 θ) := by
        have := (continuous_id.prodMk continuous_const).continuousAt (f := fun ξ : ℝ => (ξ, θ.2))
          (x := θ.1)
        simpa using this.tendsto
      (hc.eventually hle).mono fun ξ h => h
    exact hloc.hasDerivAt_eq_zero hd
  · have hd : HasDerivAt (fun σ => ∑ i, log (gpdDensity θ.1 σ (x i)))
        (∑ i, gpdScoreSigma θ.1 θ.2 (x i)) θ.2 := by
      have := HasDerivAt.sum (u := Finset.univ) fun i _ =>
        hasDerivAt_log_gpdDensity_sigma hθ₂ hθ₁ (hadm i).1
          (by have h := (hadm i).2
              have : 1 + θ.1 * x i / θ.2 = (θ.2 + θ.1 * x i) / θ.2 := by field_simp
              rw [this] at h
              exact (div_pos_iff_of_pos_right hθ₂).1 h)
      convert this using 1
      funext σ; simp
    have hloc : IsLocalMax (fun σ => ∑ i, log (gpdDensity θ.1 σ (x i))) θ.2 :=
      have hc : Tendsto (fun σ : ℝ => (θ.1, σ)) (𝓝 θ.2) (𝓝 θ) := by
        have := (continuous_const.prodMk continuous_id).continuousAt (f := fun σ : ℝ => (θ.1, σ))
          (x := θ.2)
        simpa using this.tendsto
      (hc.eventually hle).mono fun σ h => h
    exact hloc.hasDerivAt_eq_zero hd

end Admissible

section Normality

variable {ξ₀ σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
  [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ}

/-- **Joint asymptotic normality of GPD likelihood roots in the regular case** `ξ₀ > -1/2`,
`ξ₀ ≠ 0` ([Smith 1985]). Let `X₀, X₁, …` be iid `GPD(ξ₀, σ₀)` and let `θ̂ₙ` be measurable,
strongly consistent estimators which almost surely, for all large `n`, are admissible (every
observation lies in the support `σ̂ₙ + ξ̂ₙ Xᵢ > 0`; automatic for `ξ₀ > 0`) and solve the
likelihood equations. Then `√n (θ̂ₙ - θ₀) ⇒ N(0, I(θ₀)⁻¹)`. -/
theorem tendstoInDistribution_gpdJointMLE_all (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0)
    (hσ₀ : 0 < σ₀) (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ i < n, 0 < (θh n ω).2 + (θh n ω).1 * X i ω)
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gpdFisherInfoInv ξ₀ σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - ξ₀, (θh n ω).2 - σ₀])
      atTop W (fun _ => P) P' := by
  rcases lt_or_gt_of_ne hξ₀0 with h | h
  · exact tendstoInDistribution_gpdJointMLE_neg hξ₀ h hσ₀ hX hind hθm hcons hadm hroot hW
  · exact tendstoInDistribution_gpdJointMLE h hσ₀ hX hind hθm hcons hroot hW

/-- A maximizer of the likelihood over `K ∋ θ₀` is admissible whenever the data lie in the
support of `θ₀`. -/
lemma admissible_of_isMaxOn {K : Set (ℝ × ℝ)} (hθ₀ : (ξ₀, σ₀) ∈ K) (hσ₀ : 0 < σ₀) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i ∧ 0 < σ₀ + ξ₀ * x i) {θ : ℝ × ℝ}
    (hmax : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K θ) :
    ∀ i, 0 ≤ x i ∧ 0 < 1 + θ.1 * x i / θ.2 := by
  have h0 : gpdLogLikE ξ₀ σ₀ x ≠ ⊥ := by
    rw [gpdLogLikE_eq_coe' fun i => ⟨(hx i).1.le, one_add_mul_div_pos hσ₀ (hx i).2⟩]
    exact EReal.coe_ne_bot _
  have hle := hmax hθ₀
  simp only [mem_ofPred_eq] at hle
  have h1 : gpdLogLikE θ.1 θ.2 x ≠ ⊥ := ne_bot_of_le_ne_bot h0 hle
  exact fun i => gpdLogDensityE_ne_bot_iff.1 (gpdLogDensityE_ne_bot_of_gpdLogLikE_ne_bot h1 i)

/-- **Asymptotic normality of the joint GPD maximum likelihood estimator, `ξ₀ > -1/2`,
`ξ₀ ≠ 0`** ([Smith 1985]; [Coles, §4.3.3]). Let `K ⊂ {ξ > -1, σ > 0}` be compact with the true
parameter `θ₀ = (ξ₀, σ₀)` in its interior, let `X₀, X₁, …` be iid `GPD(θ₀)`, and let `θ̂ₙ` be
(almost everywhere) measurable maximizers over `K` of the log-likelihood of `X₀, …, X_{n-1}`.
Then `√n (θ̂ₙ - θ₀) ⇒ N(0, I(θ₀)⁻¹)`, `I(ξ, σ)⁻¹ = (1 + ξ) [[1 + ξ, -σ], [-σ, 2σ²]]`. -/
theorem tendstoInDistribution_gpdMLE_all {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω))
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gpdFisherInfoInv ξ₀ σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - ξ₀, (θh n ω).2 - σ₀])
      atTop W (fun _ => P) P' := by
  rcases lt_or_gt_of_ne hξ₀0 with hneg | hpos
  swap
  · exact tendstoInDistribution_gpdMLE hK hKS hθ₀ hpos hσ₀ hX hind hθm hθK hmax hW
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)) := by
    filter_upwards [ae_tendsto_gpdMLE' hK hKS (interior_subset hθ₀) hX hind] with ω hω
    refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
      (Eventually.of_forall fun n => ?_)
    have := hmax n ω (interior_subset hθ₀)
    simp only [mem_ofPred_eq] at this
    simpa using this
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < X i ω ∧ 0 < σ₀ + ξ₀ * X i ω := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)
  have hadmAll : ∀ᵐ ω ∂P, ∀ n, ∀ i : Fin n,
      0 ≤ X i ω ∧ 0 < 1 + (θh n ω).1 * X i ω / (θh n ω).2 := by
    filter_upwards [hsupp] with ω hω n
    exact admissible_of_isMaxOn (interior_subset hθ₀) hσ₀ (fun i => hω i) (hmax n ω)
  refine tendstoInDistribution_gpdJointMLE_neg hξ₀ hneg hσ₀ hX hind hθm hcons ?_ ?_ hW
  · filter_upwards [hadmAll] with ω hω
    refine Eventually.of_forall fun n i hi => ?_
    have h := (hω n ⟨i, hi⟩).2
    have hσ := (hKS _ (hθK n ω)).2
    have e : 1 + (θh n ω).1 * X i ω / (θh n ω).2 =
        ((θh n ω).2 + (θh n ω).1 * X i ω) / (θh n ω).2 := by field_simp
    rw [e] at h
    exact (div_pos_iff_of_pos_right hσ).1 h
  · filter_upwards [hadmAll, hcons] with ω hω hc
    filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀),
      hc.eventually (gpdNbhdNeg_mem_nhds hneg hσ₀)] with n h1 h2
    obtain ⟨-, h3, h4⟩ := param_bounds_of_mem_gpdNbhdNeg hneg hσ₀ hξ₀ h2
    have := score_eq_zero_of_isMaxOn' (x := fun i : Fin n => X i ω) h1 h3.ne h4 (hω n)
      (hmax n ω)
    rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω)) n,
      Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω)) n]
      at this
    exact this

/-- **Measurable maximum likelihood estimators exist** on a compact nonempty parameter set
`K ⊂ {ξ > -1, σ > 0}`: for every sample size there is a measurable map from the data to a
maximizer of the extended-real log-likelihood over `K`. -/
theorem exists_measurable_gpdMLE {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hne : K.Nonempty) (n : ℕ) :
    ∃ g : (Fin n → ℝ) → ℝ × ℝ, Measurable g ∧
      ∀ x, g x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K (g x) := by
  refine exists_measurable_isMaxOn hK (f := fun p x => gpdLogLikE p.1 p.2 x) (fun x => ?_)
    (fun θ => ?_) hne
  · refine (continuousOn_finsetSum_ereal Finset.univ
      (fun i _ => (continuousOn_gpdLogDensityE (x i)).mono fun p hp => hKS p hp)
      (fun i _ p hp => ?_)).1
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
      (gpdLogDensityE_le (hKS p hp).1 (hKS p hp).2 (x i))
  · exact Finset.measurable_sum _ fun i _ =>
      (measurable_gpdLogDensityE _ _).comp (measurable_pi_apply i)

/-- **Asymptotic normality of the GPD maximum likelihood estimator, unconditional form.** Let
`K ⊂ {ξ > -1, σ > 0}` be compact with `θ₀ = (ξ₀, σ₀)`, `ξ₀ > -1/2`, `ξ₀ ≠ 0`, in its interior and
let `X₀, X₁, …` be iid `GPD(θ₀)`. Then there is a maximum likelihood estimator — an
(almost everywhere) measurable maximizer `θ̂ₙ ∈ K` of the log-likelihood of `X₀, …, X_{n-1}` for
every `n` and every outcome, a measurable function of the sample — and every such estimator
satisfies `√n (θ̂ₙ - θ₀) ⇒ N(0, I(θ₀)⁻¹)`. -/
theorem exists_gpdMLE_tendstoInDistribution {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gpdFisherInfoInv ξ₀ σ₀)) P') :
    ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ, (∀ n, Measurable (g n)) ∧
      (∀ n x, g n x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K (g n x)) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω => √(n : ℝ) • !₂[(g n (fun i : Fin n => X i ω)).1 - ξ₀,
          (g n (fun i : Fin n => X i ω)).2 - σ₀])
        atTop W (fun _ => P) P' := by
  choose g hgm hg using exists_measurable_gpdMLE hK hKS ⟨_, interior_subset hθ₀⟩
  refine ⟨g, hgm, hg, ?_⟩
  exact tendstoInDistribution_gpdMLE_all hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind
    (θh := fun n ω => g n (fun i : Fin n => X i ω))
    (fun n => (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable))
    (fun n ω => (hg n _).1) (fun n ω => (hg n _).2) hW

end Normality

end ExtremeValueTheory
