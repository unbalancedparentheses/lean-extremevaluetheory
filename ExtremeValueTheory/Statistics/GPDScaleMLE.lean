/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDLikelihoodNormality

/-!
# A measurable scale MLE for the GPD with known shape

For a known shape `ξ > -1` the scale score `σ ↦ ∑ᵢ xᵢ / (σ + ξ xᵢ)` is strictly decreasing on
the admissible scales, so the root of the likelihood equation `(1 + ξ) ∑ᵢ xᵢ / (σ + ξ xᵢ) = n`
is the supremum of the admissible scales at which the left side is still `≥ n`. Restricting the
supremum to rational scales gives an explicitly measurable function of the sample:

  `σ̂ₙ(x) = ⨆_{q ∈ ℚ} (q if q is admissible and (1 + ξ) ∑ᵢ xᵢ / (q + ξ xᵢ) ≥ n, else 0)`.

## Main results

* `ExtremeValueTheory.measurable_gpdScaleMLE`: `σ̂ₙ` is a measurable function of the sample.
* `ExtremeValueTheory.gpdScaleMLE_eq_of_root`: whenever the likelihood equation has an admissible
  root (always, for positive observations, `exists_gpdScaleScore_eq`), `σ̂ₙ` is that root.
* `ExtremeValueTheory.ae_gpdScaleMLE_isMLE`: for iid `GPD(ξ, σ₀)` data, almost surely, for every
  `n ≥ 1`, `σ̂ₙ` is the unique admissible root of the likelihood equation and the unique
  maximizer of the likelihood.
* `ExtremeValueTheory.ae_tendsto_gpdScaleMLE'`: strong consistency of `σ̂ₙ`.
* `ExtremeValueTheory.tendstoInDistribution_gpdScaleMLE'`: **asymptotic normality**
  `√n (σ̂ₙ - σ₀) ⇒ N(0, σ₀² (1 + 2ξ))` for `ξ > -1/2`, `ξ ≠ 0`, with no measurability or root
  hypothesis left on the estimator.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

section Selection

variable {ξ : ℝ} {n : ℕ}

open Classical in
/-- The `q`-th term of the supremum defining the scale MLE. -/
noncomputable def gpdScaleMLETerm (ξ : ℝ) (q : ℚ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  if (q : ℝ) ∈ gpdScaleDomain ξ x ∧ (n : ℝ) ≤ (1 + ξ) * gpdScaleScore ξ q x then q else 0

/-- **The scale MLE** for a known shape `ξ`: the supremum over rational admissible scales `q` at
which the likelihood equation's left side `(1 + ξ) ∑ᵢ xᵢ / (q + ξ xᵢ)` is still `≥ n`. By
`gpdScaleMLE_eq_of_root` it is the root of the likelihood equation whenever there is one. -/
noncomputable def gpdScaleMLE (ξ : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ⨆ q : ℚ, gpdScaleMLETerm ξ q x

lemma measurable_gpdScaleMLETerm (ξ : ℝ) (q : ℚ) (n : ℕ) :
    Measurable (gpdScaleMLETerm ξ q : (Fin n → ℝ) → ℝ) := by
  classical
  have hdom : MeasurableSet {x : Fin n → ℝ | (q : ℝ) ∈ gpdScaleDomain ξ x} := by
    have : {x : Fin n → ℝ | (q : ℝ) ∈ gpdScaleDomain ξ x} =
        {_x | (0 : ℝ) < q} ∩ ⋂ i, {x | 0 < (q : ℝ) + ξ * x i} := by
      ext x; simp [gpdScaleDomain]
    rw [this]
    refine (MeasurableSet.const _).inter (MeasurableSet.iInter fun i => ?_)
    exact measurableSet_lt measurable_const (by fun_prop)
  have hle : MeasurableSet {x : Fin n → ℝ | (n : ℝ) ≤ (1 + ξ) * gpdScaleScore ξ q x} :=
    measurableSet_le measurable_const (by unfold gpdScaleScore; fun_prop)
  unfold gpdScaleMLETerm
  exact Measurable.ite (p := fun x : Fin n → ℝ => (q : ℝ) ∈ gpdScaleDomain ξ x ∧
    (n : ℝ) ≤ (1 + ξ) * gpdScaleScore ξ q x) (hdom.inter hle) measurable_const measurable_const

/-- **The scale MLE is a measurable function of the sample.** -/
theorem measurable_gpdScaleMLE (ξ : ℝ) (n : ℕ) :
    Measurable (gpdScaleMLE ξ : (Fin n → ℝ) → ℝ) :=
  Measurable.iSup fun q => measurable_gpdScaleMLETerm ξ q n

/-- **The scale MLE is the root of the likelihood equation**, whenever there is an admissible
root (for positive observations and `ξ > -1`). -/
theorem gpdScaleMLE_eq_of_root (hn : 0 < n) {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) {σ : ℝ}
    (hσ : σ ∈ gpdScaleDomain ξ x) (hroot : (1 + ξ) * gpdScaleScore ξ σ x = n)
    (hξ1 : -1 < ξ) : gpdScaleMLE ξ x = σ := by
  have h1ξ : 0 < 1 + ξ := by linarith
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun q => ?_) (fun w hw => ?_)
  · unfold gpdScaleMLETerm
    split_ifs with h
    · by_contra hlt
      replace hlt := not_le.1 hlt
      have := mul_lt_mul_of_pos_left (gpdScaleScore_strictAnti hn hx hσ hlt) h1ξ
      linarith [h.2]
    · exact hσ.1.le
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_mem_gpdScaleDomain hσ)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hw (sub_lt_self σ hε))
    have hqdom : (q : ℝ) ∈ gpdScaleDomain ξ x := hball (by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [le_max_right w (σ - ε)])
    refine ⟨q, ?_⟩
    have hterm : gpdScaleMLETerm ξ q x = q := by
      unfold gpdScaleMLETerm
      rw [ite_eq_left (show _ ∧ _ from ⟨hqdom, ?_⟩)]
      have := mul_lt_mul_of_pos_left (gpdScaleScore_strictAnti hn hx hqdom hq2) h1ξ
      linarith
    rw [hterm]
    exact lt_of_le_of_lt (le_max_left _ _) hq1

/-- For a sample of positive observations, `σ̂ₙ` is admissible and solves the likelihood
equation. -/
theorem gpdScaleMLE_mem_and_root (hξ1 : -1 < ξ) (hξ : ξ ≠ 0) (hn : 0 < n) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) :
    gpdScaleMLE ξ x ∈ gpdScaleDomain ξ x ∧ (1 + ξ) * gpdScaleScore ξ (gpdScaleMLE ξ x) x = n := by
  obtain ⟨σ, hσ, hroot⟩ := exists_gpdScaleScore_eq hξ1 hξ hn hx
  rw [gpdScaleMLE_eq_of_root hn hx hσ hroot hξ1]
  exact ⟨hσ, hroot⟩

end Selection

section Asymptotics

variable {ξ σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} {X : ℕ → Ω → ℝ}

lemma ae_forall_pos_of_gpd (hσ₀ : 0 < σ₀) (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) :
    ∀ᵐ ω ∂P, ∀ i, 0 < X i ω := ae_all_iff.2 fun i =>
  (ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gpdMeasure hσ₀)).mono fun _ h => h.1

/-- The scale MLE built from the first `n` observations is almost everywhere measurable. -/
lemma aemeasurable_gpdScaleMLE_comp (hX : ∀ i, AEMeasurable (X i) P) (n : ℕ) :
    AEMeasurable (fun ω => gpdScaleMLE ξ (fun i : Fin n => X i ω)) P :=
  (measurable_gpdScaleMLE ξ n).comp_aemeasurable (AEMeasurable.of_eval fun i => hX i)

/-- **The measurable scale MLE is the MLE, almost surely.** For iid `GPD(ξ, σ₀)` data with known
shape `ξ > -1`, `ξ ≠ 0`, almost surely, for every `n ≥ 1`, `σ̂ₙ = gpdScaleMLE ξ (X₀, …, X_{n-1})`
is admissible, solves the likelihood equation, is its only admissible root, and is the unique
maximizer of the likelihood over the admissible scales. -/
theorem ae_gpdScaleMLE_isMLE (hξ1 : -1 < ξ) (hξ : ξ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) :
    ∀ᵐ ω ∂P, ∀ n, 0 < n →
      gpdScaleMLE ξ (fun i : Fin n => X i ω) ∈ gpdScaleDomain ξ (fun i : Fin n => X i ω) ∧
      (1 + ξ) * gpdScaleScore ξ (gpdScaleMLE ξ (fun i : Fin n => X i ω))
        (fun i : Fin n => X i ω) = n ∧
      (∀ τ ∈ gpdScaleDomain ξ (fun i : Fin n => X i ω),
        (1 + ξ) * gpdScaleScore ξ τ (fun i : Fin n => X i ω) = n →
          τ = gpdScaleMLE ξ (fun i : Fin n => X i ω)) ∧
      (∀ τ ∈ gpdScaleDomain ξ (fun i : Fin n => X i ω),
        τ ≠ gpdScaleMLE ξ (fun i : Fin n => X i ω) →
          gpdLogLik ξ τ (fun i : Fin n => X i ω) <
            gpdLogLik ξ (gpdScaleMLE ξ (fun i : Fin n => X i ω)) (fun i : Fin n => X i ω)) := by
  filter_upwards [ae_forall_pos_of_gpd hσ₀ hX] with ω hω n hn
  have hx : ∀ i : Fin n, 0 < X i ω := fun i => hω i
  obtain ⟨hmem, hroot⟩ := gpdScaleMLE_mem_and_root hξ1 hξ hn hx
  exact ⟨hmem, hroot, fun τ hτ hτe => gpdScaleScore_root_unique hξ1 hn hx hτ hmem hτe hroot,
    fun τ hτ hne => gpdLogLik_lt_of_score_eq hξ1 hξ hn hx hmem hroot hτ hne⟩

/-- **Strong consistency of the measurable scale MLE.** -/
theorem ae_tendsto_gpdScaleMLE' [IsProbabilityMeasure P] (hξ1 : -1 < ξ) (hξ : ξ ≠ 0)
    (hσ₀ : 0 < σ₀) (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => gpdScaleMLE ξ (fun i : Fin n => X i ω)) atTop (𝓝 σ₀) := by
  filter_upwards [ae_tendsto_gpdScaleMLE hξ1 hξ hσ₀ hX hind, ae_gpdScaleMLE_isMLE hξ1 hξ hσ₀ hX]
    with ω hω hmle
  exact hω _ ((eventually_gt_atTop 0).mono fun n hn => ⟨(hmle n hn).1, (hmle n hn).2.1⟩)

/-- **Asymptotic normality of the GPD scale MLE for a known shape**, for the measurable estimator
`σ̂ₙ = gpdScaleMLE ξ (X₀, …, X_{n-1})`. Let `X₀, X₁, …` be iid `GPD(ξ, σ₀)` with known shape
`-1/2 < ξ`, `ξ ≠ 0`. Then `√n (σ̂ₙ - σ₀) ⇒ N(0, σ₀² (1 + 2ξ))`. -/
theorem tendstoInDistribution_gpdScaleMLE' [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ₀) P) (hind : iIndepFun X P)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (σ₀ ^ 2 * (1 + 2 * ξ)).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) * (gpdScaleMLE ξ (fun i : Fin n => X i ω) - σ₀)) atTop Z
      (fun _ => P) P' := by
  have hξ1 : -1 < ξ := by linarith
  refine tendstoInDistribution_gpdScaleMLE hξ hξ0 hσ₀ hX hind
    (fun n => aemeasurable_gpdScaleMLE_comp (fun i => (hX i).aemeasurable) n) ?_ hZ
  filter_upwards [ae_gpdScaleMLE_isMLE hξ1 hξ0 hσ₀ hX] with ω hmle
  exact (eventually_gt_atTop 0).mono fun n hn => ⟨(hmle n hn).1, (hmle n hn).2.1⟩

end Asymptotics

end ExtremeValueTheory
