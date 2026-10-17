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

end ExtremeValueTheory
