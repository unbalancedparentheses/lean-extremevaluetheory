/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDLikelihood

/-!
# Wald's consistency theorem for maximum likelihood (M-) estimators

Let `Θ` be a compact metric space, `m : Θ → α → ℝ` a criterion (typically the log-density
`m θ = log f_θ`), and `X₀, X₁, …` iid with law `μ`. Assume

* `θ ↦ m θ x` is continuous for every `x`, and every `m θ` is measurable;
* an integrable envelope `G` dominates `|m θ x| ≤ G x` uniformly in `θ`;
* identifiability: `θ₀` is the unique maximizer of `θ ↦ E m(θ, X)`.

Then, almost surely, every sequence `θ̂ₙ` of maximizers of the empirical criterion
`θ ↦ ∑_{i<n} m(θ, Xᵢ)` (or, more generally, any `θ̂ₙ` with
`∑_{i<n} m(θ₀, Xᵢ) ≤ ∑_{i<n} m(θ̂ₙ, Xᵢ)`) converges to `θ₀`
(A. Wald, *Note on the consistency of the maximum likelihood estimate*, Ann. Math. Statist. 20
(1949); A. W. van der Vaart, *Asymptotic Statistics*, Theorem 5.14).

## Main result

* `ExtremeValueTheory.ae_tendsto_of_wald`.

## Proof

Fix a sequence `u` dense in `Θ`. For centers `u a` and radii `rⱼ = 1/(j + 1)`, the local
suprema `w_{a,j}(x) = sup {m(u k, x) : d(u k, u a) < rⱼ}` are countable suprema, hence
measurable, dominated by `G`, and dominate `m(θ, x)` for every `θ` in the ball (by continuity and
density). For every `θ`, centers `u aⱼ` with `d(u aⱼ, θ) < rⱼ / 2` give `w_{aⱼ,j} → m(θ, ·)`
pointwise, so `E w_{aⱼ,j} → E m(θ, X) < E m(θ₀, X)` by dominated convergence, for `θ ≠ θ₀`.
By compactness, `{θ : d(θ, θ₀) ≥ ε}` is covered by finitely many balls with
`E w_{a,j} < E m(θ₀, X)`. The strong law of large numbers, applied to the countably many
`w_{a,j}` and to `m(θ₀, ·)`, shows that eventually on each of these balls the empirical
criterion is below its value at `θ₀`, so `θ̂ₙ` is eventually `ε`-close to `θ₀`.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

section Wald

variable {Θ : Type*} [MetricSpace Θ] {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  {m : Θ → α → ℝ} {G : α → ℝ} {u : ℕ → Θ}

/-- The local supremum of the criterion over the dense points `u k` in the ball of radius
`1/(j + 1)` around `u a`. -/
noncomputable def waldSup (m : Θ → α → ℝ) (u : ℕ → Θ) (a j : ℕ) (x : α) : ℝ :=
  ⨆ k : {k : ℕ // dist (u k) (u a) < 1 / ((j : ℝ) + 1)}, m (u k.1) x

private lemma waldSup_index_nonempty (a j : ℕ) :
    Nonempty {k : ℕ // dist (u k) (u a) < 1 / ((j : ℝ) + 1)} :=
  ⟨⟨a, by rw [dist_self]; positivity⟩⟩

private lemma bddAbove_waldSup (hbound : ∀ θ x, |m θ x| ≤ G x) (a j : ℕ) (x : α) :
    BddAbove (range fun k : {k : ℕ // dist (u k) (u a) < 1 / ((j : ℝ) + 1)} => m (u k.1) x) :=
  ⟨G x, by rintro _ ⟨k, rfl⟩; exact (abs_le.1 (hbound _ x)).2⟩

lemma le_waldSup (hu : DenseRange u) (hcont : ∀ x, Continuous fun θ => m θ x)
    (hbound : ∀ θ x, |m θ x| ≤ G x) {a j : ℕ} {θ : Θ} (hθ : dist θ (u a) < 1 / ((j : ℝ) + 1))
    (x : α) : m θ x ≤ waldSup m u a j x := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hev : ∀ᶠ θ' in 𝓝 θ, m θ x - ε < m θ' x ∧ dist θ' (u a) < 1 / ((j : ℝ) + 1) :=
    ((hcont x).continuousAt.eventually (lt_mem_nhds (by linarith))).and
      ((continuous_id.dist continuous_const).continuousAt.eventually (gt_mem_nhds hθ))
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hu.inter_nhds_nonempty hev
  have := le_ciSup (bddAbove_waldSup (u := u) hbound a j x) ⟨k, hk.2⟩
  simp only at this
  unfold waldSup
  linarith [hk.1]

lemma abs_waldSup_le (hbound : ∀ θ x, |m θ x| ≤ G x) (a j : ℕ) (x : α) :
    |waldSup m u a j x| ≤ G x := by
  have := waldSup_index_nonempty (u := u) a j
  refine abs_le.2 ⟨?_, ciSup_le fun k => (abs_le.1 (hbound _ x)).2⟩
  have h1 := (abs_le.1 (hbound (u a) x)).1
  have h2 := le_ciSup (bddAbove_waldSup (u := u) hbound a j x) ⟨a, by rw [dist_self]; positivity⟩
  simp only at h2
  unfold waldSup
  linarith

lemma measurable_waldSup (hmeas : ∀ θ, Measurable (m θ)) (a j : ℕ) :
    Measurable (waldSup m u a j) :=
  Measurable.iSup fun _ => hmeas _

/-- Shrinking balls around `θ`: the integrals of the local suprema converge to `E m(θ, X)`. -/
lemma exists_tendsto_integral_waldSup [IsFiniteMeasure μ] (hu : DenseRange u)
    (hcont : ∀ x, Continuous fun θ => m θ x) (hmeas : ∀ θ, Measurable (m θ))
    (hG : Integrable G μ) (hbound : ∀ θ x, |m θ x| ≤ G x) (θ : Θ) :
    ∃ a : ℕ → ℕ, (∀ j, dist θ (u (a j)) < 1 / ((j : ℝ) + 1) / 2) ∧
      Tendsto (fun j => ∫ x, waldSup m u (a j) j x ∂μ) atTop (𝓝 (∫ x, m θ x ∂μ)) := by
  choose a ha using fun j : ℕ => (Metric.denseRange_iff.1 hu) θ (1 / ((j : ℝ) + 1) / 2)
    (by positivity)
  refine ⟨a, ha, tendsto_integral_of_dominated_convergence G
    (fun j => (measurable_waldSup hmeas _ _).aestronglyMeasurable) hG
    (fun j => ae_of_all _ fun x => (Real.norm_eq_abs _).le.trans (abs_waldSup_le hbound _ _ x))
    (ae_of_all _ fun x => ?_)⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 (hcont x) θ (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hδ)
  refine ⟨N, fun j hj => ?_⟩
  have hrj : 1 / ((j : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
  have haj : dist (u (a j)) θ < δ := by
    rw [dist_comm]; linarith [ha j, one_div_pos.2 (show (0 : ℝ) < j + 1 by positivity)]
  have := waldSup_index_nonempty (u := u) (a j) j
  have hup : waldSup m u (a j) j x ≤ m θ x + ε / 2 := by
    refine ciSup_le fun k => ?_
    have hk : dist (u k.1) θ < δ := by
      have := dist_triangle (u k.1) (u (a j)) θ
      have h2 := ha j
      rw [dist_comm] at h2
      linarith [k.2]
    have := hδε (u k.1) hk
    rw [Real.dist_eq, abs_lt] at this
    linarith
  have hlow : m θ x - ε / 2 < waldSup m u (a j) j x := by
    have := hδε (u (a j)) haj
    rw [Real.dist_eq, abs_lt] at this
    have h2 := le_ciSup (bddAbove_waldSup (u := u) hbound (a j) j x) ⟨a j, by rw [dist_self]; positivity⟩
    simp only at h2
    unfold waldSup
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

variable [CompactSpace Θ]

/-- **Wald's consistency theorem.** Let `Θ` be a compact metric space and `X₀, X₁, …` iid with
law `μ`. Assume the criterion `m(θ, x)` is continuous in `θ`, measurable in `x`, dominated by an
integrable envelope `G`, and that `θ₀` is the unique maximizer of `θ ↦ E m(θ, X)`. Then almost
surely every sequence `θ̂ₙ` with `∑_{i<n} m(θ₀, Xᵢ) ≤ ∑_{i<n} m(θ̂ₙ, Xᵢ)` eventually (in
particular every sequence of maximizers of the empirical criterion) converges to `θ₀`. -/
theorem ae_tendsto_of_wald [IsProbabilityMeasure μ] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : ℕ → Ω → α} (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (hcont : ∀ x, Continuous fun θ => m θ x) (hmeas : ∀ θ, Measurable (m θ))
    (hG : Integrable G μ) (hbound : ∀ θ x, |m θ x| ≤ G x) {θ₀ : Θ}
    (hident : ∀ θ, θ ≠ θ₀ → ∫ x, m θ x ∂μ < ∫ x, m θ₀ x ∂μ) :
    ∀ᵐ ω ∂P, ∀ θhat : ℕ → Θ,
      (∀ᶠ n in atTop, ∑ i ∈ Finset.range n, m θ₀ (X i ω) ≤
        ∑ i ∈ Finset.range n, m (θhat n) (X i ω)) →
      Tendsto θhat atTop (𝓝 θ₀) := by
  have : Nonempty Θ := ⟨θ₀⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Θ
  have hint : ∀ θ, Integrable (m θ) μ := fun θ =>
    hG.mono' (hmeas θ).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).le.trans (hbound θ x))
  have hintw : ∀ a j, Integrable (waldSup m u a j) μ := fun a j =>
    hG.mono' (measurable_waldSup hmeas a j).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).le.trans (abs_waldSup_le hbound a j x))
  have h0 := ae_tendsto_avg_comp hX hind (hmeas θ₀) (hint θ₀)
  have hw : ∀ᵐ ω ∂P, ∀ a j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, waldSup m u a j (X i ω)) atTop
      (𝓝 (∫ x, waldSup m u a j x ∂μ)) :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun j =>
      ae_tendsto_avg_comp hX hind (measurable_waldSup hmeas a j) (hintw a j)
  filter_upwards [h0, hw] with ω h0 hw θhat hθ
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set K := {θ : Θ | ε ≤ dist θ θ₀}
  have hK : IsCompact K :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  set S := {p : ℕ × ℕ | ∫ x, waldSup m u p.1 p.2 x ∂μ < ∫ x, m θ₀ x ∂μ}
  have hcover : K ⊆ ⋃ p : S, Metric.ball (u p.1.1) (1 / ((p.1.2 : ℝ) + 1)) := by
    intro θ hθK
    have hne : θ ≠ θ₀ := by
      rintro rfl
      simp only [K, mem_ofPred_eq, dist_self] at hθK
      linarith
    obtain ⟨a, ha, htend⟩ := exists_tendsto_integral_waldSup hu hcont hmeas hG hbound θ
    obtain ⟨j, hj⟩ := (htend.eventually (gt_mem_nhds (hident θ hne))).exists
    refine mem_iUnion.2 ⟨⟨(a j, j), hj⟩, ?_⟩
    rw [Metric.mem_ball]
    have := ha j
    have : 0 < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (fun _ => Metric.isOpen_ball) hcover
  have hev : ∀ᶠ n : ℕ in atTop, ∀ p ∈ t, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      waldSup m u p.1.1 p.1.2 (X i ω) < (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, m θ₀ (X i ω) := by
    refine (t.eventually_all).2 fun p _ => ?_
    have := (hw p.1.1 p.1.2).sub h0
    have hneg : ∫ x, waldSup m u p.1.1 p.1.2 x ∂μ - ∫ x, m θ₀ x ∂μ < 0 := sub_neg.2 p.2
    filter_upwards [this.eventually (gt_mem_nhds hneg)] with n hn
    linarith
  filter_upwards [hev, hθ, eventually_gt_atTop 0] with n hn hθn hn0
  by_contra hfar
  have hmem : θhat n ∈ K := not_lt.1 hfar
  obtain ⟨p, hp, hball⟩ := mem_iUnion₂.1 (ht hmem)
  have hle : ∑ i ∈ Finset.range n, m (θhat n) (X i ω) ≤
      ∑ i ∈ Finset.range n, waldSup m u p.1.1 p.1.2 (X i ω) :=
    Finset.sum_le_sum fun i _ => le_waldSup hu hcont hbound (Metric.mem_ball.1 hball) _
  have hn' : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hn0)
  have := (mul_lt_mul_iff_right₀ hn').1 (hn p hp)
  linarith

end Wald

/-! ### Identifiability of the GPD family: the Kullback–Leibler inequality -/

section GPDIdentifiability

variable {ξ σ ξ₀ σ₀ x : ℝ}

lemma integrable_gpdDensity (hσ : 0 < σ) : Integrable (gpdDensity ξ σ) volume :=
  (integral_eq_one_of_eq_withDensity (gpdMeasure_eq_withDensity hσ) (gpdDensity_nonneg hσ ξ)
    (measurable_gpdDensity ξ σ).aestronglyMeasurable).1

lemma gpdDensity_pos (hξ : 0 ≤ ξ) (hσ : 0 < σ) (hx : 0 ≤ x) : 0 < gpdDensity ξ σ x := by
  have hu : 0 < 1 + ξ * x / σ := by positivity
  unfold gpdDensity
  rw [ite_eq_left ⟨hx, hu⟩]
  split_ifs
  · positivity
  · exact mul_pos (inv_pos.2 hσ) (rpow_pos_of_pos hu _)

lemma gpdDensity_of_neg (hx : x < 0) : gpdDensity ξ σ x = 0 := by
  simp [gpdDensity, not_le.2 hx]

/-- **Identifiability of the GPD family with positive shape**: two GPD laws with `ξ, ξ₀ > 0`
coincide only if their parameters do. -/
theorem gpd_params_eq_of_gpdMeasure_eq (hξ : 0 < ξ) (hσ : 0 < σ) (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (h : gpdMeasure ξ σ = gpdMeasure ξ₀ σ₀) : ξ = ξ₀ ∧ σ = σ₀ := by
  have hS : ∀ x, 0 ≤ x → gpdSurvival' ξ σ x = gpdSurvival' ξ₀ σ₀ x := fun x hx => by
    have := gpdMeasure_Ioi (ξ := ξ) hσ hx
    rw [h, gpdMeasure_Ioi hσ₀ hx] at this
    exact ((ENNReal.ofReal_eq_ofReal_iff (gpdSurvival'_nonneg _ _ _)
      (gpdSurvival'_nonneg _ _ _)).1 this).symm
  set f : ℝ → ℝ → ℝ → ℝ := fun ξ σ x => 1 / ξ * log (1 + ξ * x / σ)
  have hf : ∀ x, 0 < x → f ξ σ x = f ξ₀ σ₀ x := fun x hx => by
    have := hS x hx.le
    have h1 : 0 < 1 + ξ * x / σ := by positivity
    have h2 : 0 < 1 + ξ₀ * x / σ₀ := by positivity
    simp only [gpdSurvival', hξ.ne', hξ₀.ne', ↓reduceIte, max_eq_left h1.le,
      max_eq_left h2.le] at this
    have hl := congrArg log this
    rw [log_rpow h1, log_rpow h2] at hl
    simp only [f]
    linarith
  have hd : ∀ ξ σ x : ℝ, 0 < ξ → 0 < σ → 0 < x → HasDerivAt (f ξ σ) (1 / (σ + ξ * x)) x := by
    intro ξ σ x hξ hσ hx
    have h1 : 0 < 1 + ξ * x / σ := by positivity
    have := (((((hasDerivAt_id x).const_mul ξ).div_const σ).const_add 1).log h1.ne').const_mul
      (1 / ξ)
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  have heq : ∀ x : ℝ, 0 < x → 1 / (σ + ξ * x) = 1 / (σ₀ + ξ₀ * x) := fun x hx => by
    have hev : f ξ σ =ᶠ[𝓝 x] f ξ₀ σ₀ := by
      filter_upwards [lt_mem_nhds hx] with y hy
      exact hf y hy
    exact (hd ξ σ x hξ hσ hx).unique ((hd ξ₀ σ₀ x hξ₀ hσ₀ hx).congr_of_eventuallyEq hev)
  have e1 := heq 1 one_pos
  have e2 := heq 2 two_pos
  rw [div_eq_div_iff (by positivity) (by positivity)] at e1 e2
  constructor <;> linarith

/-- **The Kullback–Leibler inequality for the GPD family** (identifiability of the log-likelihood
criterion): for `ξ, ξ₀ > 0`, `(ξ, σ) ≠ (ξ₀, σ₀)`,
`E_{ξ₀,σ₀} log g_{ξ,σ}(X) < E_{ξ₀,σ₀} log g_{ξ₀,σ₀}(X)`. -/
theorem integral_log_gpdDensity_lt (hξ : 0 < ξ) (hσ : 0 < σ) (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hne : ¬ (ξ = ξ₀ ∧ σ = σ₀))
    (hi : Integrable (fun x => log (gpdDensity ξ σ x)) (gpdMeasure ξ₀ σ₀))
    (hi₀ : Integrable (fun x => log (gpdDensity ξ₀ σ₀ x)) (gpdMeasure ξ₀ σ₀)) :
    ∫ x, log (gpdDensity ξ σ x) ∂gpdMeasure ξ₀ σ₀ <
      ∫ x, log (gpdDensity ξ₀ σ₀ x) ∂gpdMeasure ξ₀ σ₀ := by
  have hμ := gpdMeasure_eq_withDensity (ξ := ξ₀) hσ₀
  have hm₀ : Measurable fun x => ENNReal.ofReal (gpdDensity ξ₀ σ₀ x) :=
    (measurable_gpdDensity _ _).ennreal_ofReal
  have hprod : ∀ x, gpdDensity ξ₀ σ₀ x * (gpdDensity ξ σ x / gpdDensity ξ₀ σ₀ x) =
      gpdDensity ξ σ x := fun x => by
    rcases lt_or_ge x 0 with hx | hx
    · simp [gpdDensity_of_neg hx]
    · rw [mul_div_cancel₀ _ (gpdDensity_pos hξ₀.le hσ₀ hx).ne']
  have hsmul : ∀ x, (ENNReal.ofReal (gpdDensity ξ₀ σ₀ x)).toReal •
      (gpdDensity ξ σ x / gpdDensity ξ₀ σ₀ x) = gpdDensity ξ σ x := fun x => by
    rw [ENNReal.toReal_ofReal (gpdDensity_nonneg hσ₀ _ x), smul_eq_mul, hprod]
  have hratio_int : Integrable (fun x => gpdDensity ξ σ x / gpdDensity ξ₀ σ₀ x)
      (gpdMeasure ξ₀ σ₀) := by
    rw [hμ, integrable_withDensity_iff_integrable_smul' hm₀
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact (integrable_gpdDensity (ξ := ξ) hσ).congr (ae_of_all _ fun x => (hsmul x).symm)
  have hratio : ∫ x, gpdDensity ξ σ x / gpdDensity ξ₀ σ₀ x ∂gpdMeasure ξ₀ σ₀ = 1 := by
    rw [hμ, integral_withDensity_eq_integral_toReal_smul hm₀
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [hsmul]
    exact integral_gpdDensity hσ
  have hA : Integrable (fun x => gpdDensity ξ σ x / gpdDensity ξ₀ σ₀ x - 1)
      (gpdMeasure ξ₀ σ₀) := hratio_int.sub (integrable_const 1)
  have hB : Integrable (fun x => log (gpdDensity ξ σ x) - log (gpdDensity ξ₀ σ₀ x))
      (gpdMeasure ξ₀ σ₀) := hi.sub hi₀
  have hh_int : Integrable (fun x => (gpdDensity ξ σ x / gpdDensity ξ₀ σ₀ x - 1) -
      (log (gpdDensity ξ σ x) - log (gpdDensity ξ₀ σ₀ x))) (gpdMeasure ξ₀ σ₀) := hA.sub hB
  have hh_nonneg : ∀ᵐ x ∂gpdMeasure ξ₀ σ₀, 0 ≤ (gpdDensity ξ σ x / gpdDensity ξ₀ σ₀ x - 1) -
      (log (gpdDensity ξ σ x) - log (gpdDensity ξ₀ σ₀ x)) := by
    filter_upwards [ae_gpdMeasure hσ₀] with x hx
    have hg := gpdDensity_pos hξ.le hσ hx.1.le
    have hg₀ := gpdDensity_pos hξ₀.le hσ₀ hx.1.le
    have := log_le_sub_one_of_pos (div_pos hg hg₀)
    rw [log_div hg.ne' hg₀.ne'] at this
    linarith
  have hpos : 0 < ∫ x, (gpdDensity ξ σ x / gpdDensity ξ₀ σ₀ x - 1) -
      (log (gpdDensity ξ σ x) - log (gpdDensity ξ₀ σ₀ x)) ∂gpdMeasure ξ₀ σ₀ := by
    rw [integral_pos_iff_support_of_nonneg_ae hh_nonneg hh_int, pos_iff_ne_zero]
    intro hzero
    have hae : ∀ᵐ x ∂gpdMeasure ξ₀ σ₀, (gpdDensity ξ σ x / gpdDensity ξ₀ σ₀ x - 1) -
        (log (gpdDensity ξ σ x) - log (gpdDensity ξ₀ σ₀ x)) = 0 := by
      rw [ae_iff]; simpa [Function.support] using hzero
    have hae2 : ∀ᵐ x ∂gpdMeasure ξ₀ σ₀, gpdDensity ξ σ x = gpdDensity ξ₀ σ₀ x := by
      filter_upwards [hae, ae_gpdMeasure hσ₀] with x hx hx'
      by_contra hneq
      have hg := gpdDensity_pos hξ.le hσ hx'.1.le
      have hg₀ := gpdDensity_pos hξ₀.le hσ₀ hx'.1.le
      have := log_lt_sub_one_of_pos (div_pos hg hg₀)
        (fun h1 => hneq ((div_eq_one_iff_eq hg₀.ne').1 h1))
      rw [log_div hg.ne' hg₀.ne'] at this
      linarith
    have hleb : ∀ᵐ x ∂volume, gpdDensity ξ σ x = gpdDensity ξ₀ σ₀ x := by
      rw [ae_iff] at hae2 ⊢
      rw [hμ, withDensity_apply_eq_zero' hm₀.aemeasurable] at hae2
      refine measure_mono_null ?_ hae2
      intro x hx
      refine ⟨?_, hx⟩
      simp only [mem_ofPred_eq] at hx ⊢
      rcases lt_or_ge x 0 with hx0 | hx0
      · exact absurd (by simp [gpdDensity_of_neg hx0]) hx
      · exact (ENNReal.ofReal_pos.2 (gpdDensity_pos hξ₀.le hσ₀ hx0)).ne'
    refine hne (gpd_params_eq_of_gpdMeasure_eq hξ hσ hξ₀ hσ₀ ?_)
    rw [gpdMeasure_eq_withDensity hσ, hμ]
    exact withDensity_congr_ae (hleb.mono fun x hx => by simp only; rw [hx])
  rw [integral_sub hA hB, integral_sub hratio_int (integrable_const 1), integral_sub hi hi₀,
    hratio, integral_const, probReal_univ, one_smul] at hpos
  linarith

end GPDIdentifiability

/-! ### Wald consistency of the joint GPD maximum likelihood estimator -/

section GPDWald

/-- The GPD log-density is continuous in the parameters `(ξ, σ)` on `{ξ > 0, σ > 0}`. -/
lemma continuousOn_log_gpdDensity (x : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => log (gpdDensity p.1 p.2 x)) {p | 0 < p.1 ∧ 0 < p.2} := by
  rcases lt_or_ge x 0 with hx | hx
  · refine (continuousOn_const (c := (0 : ℝ))).congr fun p _ => ?_
    simp only [gpdDensity_of_neg hx, log_zero]
  · have hu : ∀ p ∈ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2}, 0 < 1 + p.1 * x / p.2 := fun p hp => by
      have := hp.1; have := hp.2; positivity
    refine ContinuousOn.congr (f := fun p : ℝ × ℝ => -log p.2 - (1 / p.1 + 1) *
      log (1 + p.1 * x / p.2)) ?_ fun p hp => log_gpdDensity hp.2 hp.1.ne' hx (hu p hp)
    refine (continuous_snd.continuousOn.log fun p hp => hp.2.ne').neg.sub
      (((continuousOn_const.div continuous_fst.continuousOn fun p hp => hp.1.ne').add
        continuousOn_const).mul (ContinuousOn.log ?_ fun p hp => (hu p hp).ne'))
    exact continuousOn_const.add ((continuous_fst.continuousOn.mul continuousOn_const).div
      continuous_snd.continuousOn fun p hp => hp.2.ne')

variable {K : Set (ℝ × ℝ)}

/-- **Existence of the joint MLE on a compact parameter set.** -/
theorem exists_isMaxOn_gpdLogLik (hK : IsCompact K) (hKpos : ∀ p ∈ K, 0 < p.1 ∧ 0 < p.2)
    (hne : K.Nonempty) {n : ℕ} (x : Fin n → ℝ) :
    ∃ θ ∈ K, IsMaxOn (fun p : ℝ × ℝ => gpdLogLik p.1 p.2 x) K θ :=
  hK.exists_isMaxOn hne (continuousOn_finsetSum _ fun i _ =>
    (continuousOn_log_gpdDensity (x i)).mono fun p hp => hKpos p hp)

/-- Uniform bounds for the parameters on a compact subset of `{ξ > 0, σ > 0}`. -/
private lemma exists_bounds (hK : IsCompact K) (hKpos : ∀ p ∈ K, 0 < p.1 ∧ 0 < p.2)
    (hne : K.Nonempty) :
    ∃ c C : ℝ, 0 < c ∧ ∀ p ∈ K, c ≤ p.1 ∧ p.1 ≤ C ∧ c ≤ p.2 ∧ p.2 ≤ C := by
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne
    (continuous_fst.min continuous_snd : Continuous fun p : ℝ × ℝ => min p.1 p.2).continuousOn
  obtain ⟨p₁, -, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_fst.max continuous_snd : Continuous fun p : ℝ × ℝ => max p.1 p.2).continuousOn
  refine ⟨min p₀.1 p₀.2, max p₁.1 p₁.2, lt_min (hKpos p₀ hp₀).1 (hKpos p₀ hp₀).2,
    fun p hp => ?_⟩
  have h1 : min p₀.1 p₀.2 ≤ min p.1 p.2 := hmin hp
  have h2 : max p.1 p.2 ≤ max p₁.1 p₁.2 := hmax hp
  exact ⟨h1.trans (min_le_left _ _), (le_max_left _ _).trans h2, h1.trans (min_le_right _ _),
    (le_max_right _ _).trans h2⟩

/-- The integrable envelope `|log c| + |log C| + (1/c + 1) log(1 + (C/c)|x|)`. -/
private lemma abs_log_gpdDensity_le {c C ξ σ : ℝ} (hc : 0 < c) (hξ : c ≤ ξ) (hξC : ξ ≤ C)
    (hσ : c ≤ σ) (hσC : σ ≤ C) (x : ℝ) :
    |log (gpdDensity ξ σ x)| ≤ |log c| + |log C| + (1 / c + 1) * log (1 + C / c * |x|) := by
  have hξ0 : 0 < ξ := hc.trans_le hξ
  have hσ0 : 0 < σ := hc.trans_le hσ
  have hC : 0 < C := hσ0.trans_le hσC
  have hL0 : 0 ≤ log (1 + C / c * |x|) := by
    have : 0 ≤ C / c * |x| := by positivity
    exact log_nonneg (by linarith)
  rcases lt_or_ge x 0 with hx | hx
  · rw [gpdDensity_of_neg hx, log_zero, abs_zero]
    have := abs_nonneg (log c); have := abs_nonneg (log C)
    have : 0 ≤ (1 / c + 1) * log (1 + C / c * |x|) := mul_nonneg (by positivity) hL0
    linarith
  have hu : 0 < 1 + ξ * x / σ := by positivity
  rw [log_gpdDensity hσ0 hξ0.ne' hx hu]
  have hlogσ : |log σ| ≤ |log c| + |log C| := by
    have h1 := log_le_log hc hσ
    have h2 := log_le_log hσ0 hσC
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (log c), le_abs_self (log C), abs_nonneg (log c),
      abs_nonneg (log C)]
  have hL : 0 ≤ log (1 + ξ * x / σ) := by
    have : 0 ≤ ξ * x / σ := by positivity
    exact log_nonneg (by linarith)
  have hLle : log (1 + ξ * x / σ) ≤ log (1 + C / c * |x|) := by
    refine log_le_log hu ?_
    rw [abs_of_nonneg hx]
    have : ξ * x / σ ≤ C / c * x := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hσ0 hc]
      have : ξ * x * c ≤ C * x * σ := by
        have := mul_le_mul (mul_le_mul_of_nonneg_right hξC hx) hσ (by linarith)
          (by positivity)
        linarith
      linarith
    linarith
  have hcoef : 1 / ξ + 1 ≤ 1 / c + 1 := by
    have := one_div_le_one_div_of_le hc hξ
    linarith
  have hprod : (1 / ξ + 1) * log (1 + ξ * x / σ) ≤ (1 / c + 1) * log (1 + C / c * |x|) :=
    mul_le_mul hcoef hLle hL (by positivity)
  have hprod0 : 0 ≤ (1 / ξ + 1) * log (1 + ξ * x / σ) := mul_nonneg (by positivity) hL
  calc |-log σ - (1 / ξ + 1) * log (1 + ξ * x / σ)|
      ≤ |log σ| + (1 / ξ + 1) * log (1 + ξ * x / σ) := by
        rw [sub_eq_add_neg, ← neg_add]
        rw [abs_neg]
        exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hprod0])
    _ ≤ _ := by linarith

/-- The envelope is integrable under `GPD(ξ₀, σ₀)`, `ξ₀ > 0`: `log(1 + A X) ≤ log(1 + B) + ξ₀ E`
in the exponential representation `X = σ₀ (e^{ξ₀ E} - 1)/ξ₀`. -/
private lemma integrable_log_one_add_mul_abs {ξ₀ σ₀ A : ℝ} (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hA : 0 ≤ A) : Integrable (fun x => log (1 + A * |x|)) (gpdMeasure ξ₀ σ₀) := by
  have hmeas : Measurable fun x : ℝ => log (1 + A * |x|) := by fun_prop
  rw [integrable_gpdMeasure_iff hmeas]
  set B := A * σ₀ / ξ₀
  have hB : 0 ≤ B := by positivity
  refine Integrable.mono' ((integrable_const (log (1 + B))).add
    ((integrable_pow_expMeasure 1).const_mul ξ₀)) (hmeas.comp
      (measurable_gpdTransform ξ₀ σ₀)).aestronglyMeasurable ?_
  filter_upwards [ae_pos_expMeasure] with t ht
  have hT := gpdTransform_pos (ξ := ξ₀) hσ₀ ht
  simp only [gpdTransform, hξ₀.ne', ↓reduceIte] at hT ⊢
  have hT' : 0 ≤ σ₀ * (exp (ξ₀ * t) - 1) / ξ₀ := hT.le
  rw [abs_of_nonneg hT', Real.norm_eq_abs, abs_of_nonneg (log_nonneg (by nlinarith))]
  simp only [Pi.add_apply, pow_one]
  have he : 1 ≤ exp (ξ₀ * t) := one_le_exp (by positivity)
  have hle : 1 + A * (σ₀ * (exp (ξ₀ * t) - 1) / ξ₀) ≤ (1 + B) * exp (ξ₀ * t) := by
    have : A * (σ₀ * (exp (ξ₀ * t) - 1) / ξ₀) = B * (exp (ξ₀ * t) - 1) := by
      simp only [B]; ring
    rw [this]
    nlinarith
  calc log (1 + A * (σ₀ * (exp (ξ₀ * t) - 1) / ξ₀)) ≤ log ((1 + B) * exp (ξ₀ * t)) :=
        log_le_log (by nlinarith) hle
    _ = log (1 + B) + ξ₀ * t := by
        rw [log_mul (by positivity) (exp_pos _).ne', log_exp]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- **Wald consistency of the joint GPD maximum likelihood estimator.** Let `K` be a compact
set of parameters `(ξ, σ)` with `ξ > 0`, `σ > 0`, containing the true parameter `θ₀`, and let
`X₀, X₁, …` be iid `GPD(θ₀)`. Almost surely, every sequence `θ̂ₙ ∈ K` of maximizers of the
GPD log-likelihood over `K` (more generally, every `θ̂ₙ ∈ K` with `ℓₙ(θ₀) ≤ ℓₙ(θ̂ₙ)`)
converges to `θ₀`. Maximizers exist by `exists_isMaxOn_gpdLogLik`. -/
theorem ae_tendsto_gpdMLE (hK : IsCompact K) (hKpos : ∀ p ∈ K, 0 < p.1 ∧ 0 < p.2)
    {θ₀ : ℝ × ℝ} (hθ₀ : θ₀ ∈ K) (hX : ∀ i, HasLaw (X i) (gpdMeasure θ₀.1 θ₀.2) P)
    (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, ∀ θhat : ℕ → ℝ × ℝ, (∀ n, θhat n ∈ K) →
      (∀ᶠ n in atTop, gpdLogLik θ₀.1 θ₀.2 (fun i : Fin n => X i ω) ≤
        gpdLogLik (θhat n).1 (θhat n).2 (fun i : Fin n => X i ω)) →
      Tendsto θhat atTop (𝓝 θ₀) := by
  obtain ⟨c, C, hc, hb⟩ := exists_bounds hK hKpos ⟨θ₀, hθ₀⟩
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  set m : K → ℝ → ℝ := fun θ x => log (gpdDensity θ.1.1 θ.1.2 x)
  set G : ℝ → ℝ := fun x => |log c| + |log C| + (1 / c + 1) * log (1 + C / c * |x|)
  have hθ₀pos := hKpos θ₀ hθ₀
  have hG : Integrable G (gpdMeasure θ₀.1 θ₀.2) :=
    (integrable_const _).add ((integrable_log_one_add_mul_abs hθ₀pos.1 hθ₀pos.2
      (div_nonneg ((hc.trans_le (hb θ₀ hθ₀).1).le.trans (hb θ₀ hθ₀).2.1) hc.le)).const_mul _)
  have hbound : ∀ θ x, |m θ x| ≤ G x := fun θ x => by
    obtain ⟨h1, h2, h3, h4⟩ := hb θ.1 θ.2
    exact abs_log_gpdDensity_le hc h1 h2 h3 h4 x
  have hcont : ∀ x, Continuous fun θ => m θ x := fun x =>
    (continuousOn_log_gpdDensity x).comp_continuous continuous_subtype_val
      fun θ => hKpos θ.1 θ.2
  have hmeas : ∀ θ, Measurable (m θ) := fun θ => (measurable_gpdDensity _ _).log
  have hint : ∀ θ, Integrable (m θ) (gpdMeasure θ₀.1 θ₀.2) := fun θ =>
    hG.mono' (hmeas θ).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).le.trans (hbound θ x))
  have hident : ∀ θ : K, θ ≠ ⟨θ₀, hθ₀⟩ → ∫ x, m θ x ∂gpdMeasure θ₀.1 θ₀.2 <
      ∫ x, m ⟨θ₀, hθ₀⟩ x ∂gpdMeasure θ₀.1 θ₀.2 := fun θ hne =>
    integral_log_gpdDensity_lt (hKpos θ.1 θ.2).1 (hKpos θ.1 θ.2).2 hθ₀pos.1 hθ₀pos.2
      (fun h => hne (Subtype.ext (Prod.ext h.1 h.2))) (hint θ) (hint ⟨θ₀, hθ₀⟩)
  filter_upwards [ae_tendsto_of_wald hX hind hcont hmeas hG hbound hident] with ω hω θhat hθK hθ
  have := hω (fun n => ⟨θhat n, hθK n⟩) (hθ.mono fun n hn => by
    rw [gpdLogLik, gpdLogLik,
      Fin.sum_univ_eq_sum_range (fun i => log (gpdDensity θ₀.1 θ₀.2 (X i ω))) n,
      Fin.sum_univ_eq_sum_range (fun i => log (gpdDensity (θhat n).1 (θhat n).2 (X i ω))) n] at hn
    exact hn)
  exact (continuous_subtype_val.tendsto _).comp this

end GPDWald

end ExtremeValueTheory
