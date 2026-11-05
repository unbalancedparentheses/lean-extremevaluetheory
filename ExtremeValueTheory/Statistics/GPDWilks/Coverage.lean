/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDWilks.Profile

/-!
# Profile likelihood confidence sets for the GPD, `ξ₀ > 0`

The sets `{ψ : D_p(ψ) ≤ c}` of [Coles, §2.6.6], defined from the data alone, with the likelihood
maximized over a compact parameter set, and their asymptotic coverage. No estimator appears in the
statements: measurable maximizers are selected inside the proofs (`exists_measurable_gpdMLE`), and
the deviance does not depend on the selection.

## Main results

* `gpdMaxLogLik`, `gpdProfileLogLik`, `gpdProfileInterval`, `gpdDevianceRegion`: the definitions.
* `tendsto_measure_mem_gpdProfileInterval`: coverage `χ²₁((-∞, c])`, for an interest parameter with
  a chart of its level set; `exists_tendsto_measure_mem_gpdProfileInterval` is the form with limit
  `1 - α`.
* `tendsto_measure_mem_gpdShapeProfileInterval`, `tendsto_measure_mem_gpdScaleProfileInterval`,
  `tendsto_measure_mem_gpdReturnLevelProfileInterval`: the shape, the scale, the POT return level.
* `tendsto_measure_mem_gpdDevianceRegion`: coverage `χ²₂((-∞, c])` of the deviance region for the
  full parameter.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §2.6.5–2.6.6, §4.3.3.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Asymptotics

namespace ExtremeValueTheory

/-! ### Profile likelihood intervals and their coverage -/

section Coverage

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {ξ₀ σ₀ : ℝ}

/-- The maximized log-likelihood `sup_{θ ∈ K} ℓₙ(θ)`, in the extended reals (the log-likelihood is
`-∞` at parameters under which some observation is impossible, and the supremum of the empty set is
`-∞`). -/
noncomputable def gpdMaxLogLik (K : Set (ℝ × ℝ)) {n : ℕ} (x : Fin n → ℝ) : EReal :=
  ⨆ p ∈ K, gpdLogLikE p.1 p.2 x

/-- The **profile log-likelihood** of the interest parameter `g` at the value `ψ` ([Coles, §2.6.6]):
`ℓ_p(ψ) = sup {ℓₙ(θ) : θ ∈ K, g θ = ψ}`. -/
noncomputable def gpdProfileLogLik (K : Set (ℝ × ℝ)) (g : ℝ × ℝ → ℝ) (ψ : ℝ) {n : ℕ}
    (x : Fin n → ℝ) : EReal :=
  gpdMaxLogLik (K ∩ g ⁻¹' {ψ}) x

/-- The **profile likelihood confidence set** ([Coles, §2.6.6]) for `g` at critical value `c`:
the values `ψ` with profile deviance `D_p(ψ) = 2 (sup_K ℓₙ - ℓ_p(ψ)) ≤ c`, with `c` the `(1 - α)`
quantile of `χ²₁`. (It is an interval when the profile likelihood is unimodal; nothing here depends
on that, and we do not prove that it is.) A value `ψ` not attained on `K` has `ℓ_p(ψ) = -∞`, so it
is excluded as soon as `sup_K ℓₙ` is finite. -/
def gpdProfileInterval (K : Set (ℝ × ℝ)) (g : ℝ × ℝ → ℝ) (c : ℝ) {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  {ψ | 2 * (gpdMaxLogLik K x - gpdProfileLogLik K g ψ x) ≤ (c : EReal)}

/-- The **deviance confidence region** for the full parameter ([Coles, §2.6.5]):
`{θ : D(θ) = 2 (sup_K ℓₙ - ℓₙ(θ)) ≤ c}`, with `c` the `(1 - α)` quantile of `χ²₂`. -/
def gpdDevianceRegion (K : Set (ℝ × ℝ)) (c : ℝ) {n : ℕ} (x : Fin n → ℝ) : Set (ℝ × ℝ) :=
  {θ | 2 * (gpdMaxLogLik K x - gpdLogLikE θ.1 θ.2 x) ≤ (c : EReal)}

lemma gpdMaxLogLik_eq_of_isMaxOn {K : Set (ℝ × ℝ)} {n : ℕ} {x : Fin n → ℝ} {θ : ℝ × ℝ}
    (hθ : θ ∈ K) (hmax : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K θ) :
    gpdMaxLogLik K x = gpdLogLikE θ.1 θ.2 x :=
  le_antisymm (iSup₂_le fun _ hp => hmax hp)
    (le_iSup₂ (f := fun (p : ℝ × ℝ) (_ : p ∈ K) => gpdLogLikE p.1 p.2 x) θ hθ)

/-- Where the extended-real log-likelihood is not `-∞`, it is the ordinary sum of log-densities. -/
lemma gpdLogLikE_eq_coe_of_ne_bot {ξ σ : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (h : gpdLogLikE ξ σ x ≠ ⊥) :
    gpdLogLikE ξ σ x = ((∑ i, log (gpdDensity ξ σ (x i)) : ℝ) : EReal) := by
  have hall : ∀ i, gpdLogDensityE ξ σ (x i) ≠ ⊥ := fun i hi => h <| by
    rw [gpdLogLikE, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi, EReal.bot_add]
  rw [gpdLogLikE, ereal_coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := gpdLogDensityE_ne_bot_iff.1 (hall i)
  unfold gpdLogDensityE
  rw [ite_eq_left this]

/-- Value of the extended-real deviance when both log-likelihoods are at maximizers of sets
containing `θ₀`, on nonnegative data. -/
private lemma deviance_le_iff {K₁ K₂ : Set (ℝ × ℝ)} (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (h₁ : (ξ₀, σ₀) ∈ K₁) (h₂ : (ξ₀, σ₀) ∈ K₂) {n : ℕ} {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i)
    {θ₁ θ₂ : ℝ × ℝ}
    (hm₁ : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => x i)) K₁ θ₁)
    (hm₂ : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => x i)) K₂ θ₂) (c : ℝ) :
    2 * (gpdLogLikE θ₁.1 θ₁.2 (fun i : Fin n => x i) -
        gpdLogLikE θ₂.1 θ₂.2 (fun i : Fin n => x i)) ≤ (c : EReal) ↔
      2 * (gpdLogLikN θ₁.1 θ₁.2 x n - gpdLogLikN θ₂.1 θ₂.2 x n) ≤ c := by
  have h₀ : gpdLogLikE ξ₀ σ₀ (fun i : Fin n => x i) ≠ ⊥ := by
    rw [gpdLogLikE_eq_coe hξ₀ hσ₀ fun i => hx i]
    exact EReal.coe_ne_bot _
  have key : ∀ {K : Set (ℝ × ℝ)} {θ : ℝ × ℝ}, (ξ₀, σ₀) ∈ K →
      IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => x i)) K θ →
      gpdLogLikE θ.1 θ.2 (fun i : Fin n => x i) = ((gpdLogLikN θ.1 θ.2 x n : ℝ) : EReal) := by
    intro K θ hK hm
    have hle : gpdLogLikE ξ₀ σ₀ (fun i : Fin n => x i) ≤ gpdLogLikE θ.1 θ.2 (fun i : Fin n => x i) :=
      hm hK
    rw [gpdLogLikE_eq_coe_of_ne_bot (ne_bot_of_le_ne_bot h₀ hle), gpdLogLikN,
      Fin.sum_univ_eq_sum_range (fun i => log (gpdDensity θ.1 θ.2 (x i))) n]
  rw [key h₁ hm₁, key h₂ hm₂, ← EReal.coe_sub,
    show (2 : EReal) = ((2 : ℝ) : EReal) from rfl, ← EReal.coe_mul, EReal.coe_le_coe_iff]

/-- **Asymptotic coverage of the profile likelihood confidence set for the GPD** ([Coles, §2.6.6]).
Let `K ⊂ {ξ > -1, σ > 0}` be compact with `θ₀ = (ξ₀, σ₀)`, `ξ₀ > 0`, in its interior, let `g` be
continuous on `K` with a chart of the level set through `θ₀` (`IsGPDProfileChart`), and let
`X₀, X₁, …` be iid `GPD(θ₀)`. Then

  `P(g θ₀ ∈ {ψ : D_p(ψ) ≤ c}) → χ²₁((-∞, c])`,

for every `c`, where the likelihood is maximized over `K`. By `exists_chiSquared_one_Iic_eq`, the
limit is `1 - α` when `c` is the `(1 - α)` quantile of `χ²₁`. -/
theorem tendsto_measure_mem_gpdProfileInterval {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g K) {s₀ : ℝ} {φ : ℝ × ℝ → ℝ} {γ₁ γ₂ t₁ t₂ : ℝ → ℝ}
    (hchart : IsGPDProfileChart g ξ₀ σ₀ s₀ φ γ₁ γ₂ t₁ t₂) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | g (ξ₀, σ₀) ∈ gpdProfileInterval K g c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 1 (Iic c))) := by
  set K' := K ∩ g ⁻¹' {g (ξ₀, σ₀)} with hK'
  have hK'c : IsCompact K' := hK.of_isClosed_subset
    (hg.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton) inter_subset_left
  have hK'S : ∀ p ∈ K', -1 < p.1 ∧ 0 < p.2 := fun p hp => hKS p hp.1
  have hθ₀K' : (ξ₀, σ₀) ∈ K' := ⟨interior_subset hθ₀, rfl⟩
  choose G hGm hG using exists_measurable_gpdMLE hK hKS ⟨_, interior_subset hθ₀⟩
  choose G' hGm' hG' using exists_measurable_gpdMLE hK'c hK'S ⟨_, hθ₀K'⟩
  have hsam : ∀ n : ℕ, AEMeasurable (fun ω => (fun i : Fin n => X i ω)) P := fun n =>
    AEMeasurable.of_eval fun i => (hX i).aemeasurable
  have hD := tendstoInDistribution_gpdProfileDeviance hK hKS hθ₀ hξ₀ hσ₀ hX hind hg hchart
    (θh := fun n ω => G n fun i : Fin n => X i ω)
    (fun n => (hGm n).comp_aemeasurable (hsam n)) (fun n ω => (hG n _).1) (fun n ω => (hG n _).2)
    (θt := fun n ω => G' n fun i : Fin n => X i ω)
    (fun n => (hGm' n).comp_aemeasurable (hsam n)) (fun n ω => (hG' n _).1)
    (fun n ω => (hG' n _).2) (Z := id) (P' := chiSquared 1) HasLaw.id
  refine (hD.tendsto_measure_le_of_noAtoms HasLaw.id c).congr fun n => ?_
  refine measure_congr ?_
  filter_upwards [ae_forall_pos_of_gpd hσ₀ hX] with ω hω
  have hx : ∀ i, 0 ≤ X i ω := fun i => (hω i).le
  apply propext
  change 2 * (gpdLogLikN _ _ (fun i => X i ω) n - gpdLogLikN _ _ (fun i => X i ω) n) ≤ c ↔
    2 * (gpdMaxLogLik K (fun i : Fin n => X i ω) -
      gpdProfileLogLik K g (g (ξ₀, σ₀)) (fun i : Fin n => X i ω)) ≤ (c : EReal)
  rw [gpdProfileLogLik, gpdMaxLogLik_eq_of_isMaxOn (hG n _).1 (hG n _).2,
    gpdMaxLogLik_eq_of_isMaxOn (hG' n _).1 (hG' n _).2,
    deviance_le_iff (x := fun i => X i ω) hξ₀ hσ₀ (interior_subset hθ₀) hθ₀K' hx (hG n _).2
      (hG' n _).2 c]

/-- **Asymptotic coverage of the profile likelihood confidence set at level `1 - α`.** For
`α ∈ (0, 1)` there is `c > 0`, the `(1 - α)` quantile of `χ²₁`, with
`P(g θ₀ ∈ {ψ : D_p(ψ) ≤ c}) → 1 - α`. -/
theorem exists_tendsto_measure_mem_gpdProfileInterval {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {g : ℝ × ℝ → ℝ} (hg : ContinuousOn g K) {s₀ : ℝ} {φ : ℝ × ℝ → ℝ} {γ₁ γ₂ t₁ t₂ : ℝ → ℝ}
    (hchart : IsGPDProfileChart g ξ₀ σ₀ s₀ φ γ₁ γ₂ t₁ t₂) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧ (chiSquared 1).real (Iic c) = 1 - α ∧
      Tendsto (fun n : ℕ => P {ω | g (ξ₀, σ₀) ∈ gpdProfileInterval K g c (fun i : Fin n => X i ω)})
        atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨c, hc, hq⟩ := exists_chiSquared_one_Iic_eq hα0 hα1
  refine ⟨c, hc, hq, ?_⟩
  rw [← hq, ofReal_measureReal]
  exact tendsto_measure_mem_gpdProfileInterval hK hKS hθ₀ hξ₀ hσ₀ hX hind hg hchart c

/-- **Profile likelihood interval for the shape `ξ` of the GPD** ([Coles, §2.6.6]): coverage
`χ²₁((-∞, c])`, on a compact parameter set with `θ₀`, `ξ₀ > 0`, in its interior. -/
theorem tendsto_measure_mem_gpdShapeProfileInterval {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | ξ₀ ∈ gpdProfileInterval K Prod.fst c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 1 (Iic c))) :=
  tendsto_measure_mem_gpdProfileInterval hK hKS hθ₀ hξ₀ hσ₀ hX hind continuousOn_fst
    (isGPDProfileChart_shape ξ₀ σ₀) c

/-- **Profile likelihood interval for the scale `σ` of the GPD** ([Coles, §2.6.6]): coverage
`χ²₁((-∞, c])`, on a compact parameter set with `θ₀`, `ξ₀ > 0`, in its interior. -/
theorem tendsto_measure_mem_gpdScaleProfileInterval {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | σ₀ ∈ gpdProfileInterval K Prod.snd c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 1 (Iic c))) :=
  tendsto_measure_mem_gpdProfileInterval hK hKS hθ₀ hξ₀ hσ₀ hX hind continuousOn_snd
    (isGPDProfileChart_scale ξ₀ σ₀) c

/-- **Profile likelihood interval for the POT return level** ([Coles, §2.6.6, §4.3.3]): for the
`N`-observation return level `x_N = u + σ h_ξ(N ζ)` with `N ζ > 1` and known threshold `u` and
exceedance probability `ζ`, the coverage probability converges to `χ²₁((-∞, c])`, on a compact
parameter set with `θ₀`, `ξ₀ > 0`, in its interior. This is the interval practitioners prefer to
the Wald interval `tendsto_measure_mem_gpdReturnLevelInterval`, since it can be asymmetric. -/
theorem tendsto_measure_mem_gpdReturnLevelProfileInterval {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) {u ζ N : ℝ}
    (hNζ : 1 < N * ζ) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | gpdReturnLevel u ξ₀ σ₀ ζ N ∈
        gpdProfileInterval K (fun p => gpdReturnLevel u p.1 p.2 ζ N) c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 1 (Iic c))) := by
  have hcont : Continuous fun p : ℝ × ℝ => gpdReturnLevel u p.1 p.2 ζ N := by
    unfold gpdReturnLevel
    exact continuous_const.add (continuous_snd.mul
      ((continuous_boxCox_shape (one_pos.trans hNζ)).comp continuous_fst))
  exact tendsto_measure_mem_gpdProfileInterval hK hKS hθ₀ hξ₀ hσ₀ hX hind hcont.continuousOn
    (isGPDProfileChart_returnLevel hξ₀.ne' hNζ) c

/-- **Asymptotic coverage of the deviance region for the full GPD parameter** ([Coles, §2.6.5]):
`P(θ₀ ∈ {θ : D(θ) ≤ c}) → χ²₂((-∞, c])`, on a compact parameter set with `θ₀`, `ξ₀ > 0`, in its
interior. -/
theorem tendsto_measure_mem_gpdDevianceRegion {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | (ξ₀, σ₀) ∈ gpdDevianceRegion K c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 2 (Iic c))) := by
  choose G hGm hG using exists_measurable_gpdMLE hK hKS ⟨_, interior_subset hθ₀⟩
  have hsam : ∀ n : ℕ, AEMeasurable (fun ω => (fun i : Fin n => X i ω)) P := fun n =>
    AEMeasurable.of_eval fun i => (hX i).aemeasurable
  have hD := tendstoInDistribution_gpdDeviance hK hKS hθ₀ hξ₀ hσ₀ hX hind
    (θh := fun n ω => G n fun i : Fin n => X i ω)
    (fun n => (hGm n).comp_aemeasurable (hsam n)) (fun n ω => (hG n _).1) (fun n ω => (hG n _).2)
    (Z := id) (P' := chiSquared 2) HasLaw.id
  refine (hD.tendsto_measure_le_of_noAtoms HasLaw.id c).congr fun n => ?_
  refine measure_congr ?_
  filter_upwards [ae_forall_pos_of_gpd hσ₀ hX] with ω hω
  have hx : ∀ i, 0 ≤ X i ω := fun i => (hω i).le
  apply propext
  change 2 * (gpdLogLikN _ _ (fun i => X i ω) n - gpdLogLikN _ _ (fun i => X i ω) n) ≤ c ↔
    2 * (gpdMaxLogLik K (fun i : Fin n => X i ω) -
      gpdLogLikE ξ₀ σ₀ (fun i : Fin n => X i ω)) ≤ (c : EReal)
  have hm₀ : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω))
      {(ξ₀, σ₀)} (ξ₀, σ₀) := isMaxOn_iff.2 fun p hp => by
    rw [mem_singleton_iff.1 hp]
  rw [gpdMaxLogLik_eq_of_isMaxOn (hG n _).1 (hG n _).2]
  exact (deviance_le_iff (x := fun i => X i ω) hξ₀ hσ₀ (interior_subset hθ₀) (mem_singleton _) hx
    (hG n _).2 hm₀ c).symm

end Coverage

end ExtremeValueTheory
