/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDFisherInformation
import ExtremeValueTheory.Statistics.ExtremeQuantileSecondOrder
import ExtremeValueTheory.Statistics.GPDJointMLE

/-!
# Joint asymptotic normality of the GPD maximum likelihood estimator, `ξ₀ > 0`

Let `X₀, X₁, …` be iid `GPD(ξ₀, σ₀)` with `ξ₀ > 0`. We prove

  `√n (θ̂ₙ - θ₀) ⇒ N(0, I(θ₀)⁻¹)`, `I(ξ, σ)⁻¹ = (1 + ξ) [[1 + ξ, -σ], [-σ, 2σ²]]`,

for every measurable, strongly consistent sequence `θ̂ₙ` of roots of the likelihood equations
(`tendstoInDistribution_gpdJointMLE`), and hence for measurable maximizers of the likelihood over
a compact parameter set containing `θ₀` in its interior (`tendstoInDistribution_gpdMLE`, using
the consistency theorem `ae_tendsto_gpdMLE'`).

## Proof

* *Lipschitz control of the Hessian* (`exists_gpdHess_lipschitz`). On the neighbourhood
  `gpdNbhd ξ₀ σ₀ = {|ξ - ξ₀| ≤ ξ₀/8, |σ - σ₀| ≤ σ₀/8}` the Hessian entries are smooth functions of
  `(ξ, σ, w)`, `w = x/(σ + ξ x) ∈ [0, 2/ξ₀]`, plus (for `∂²_ξ`) a multiple of
  `log(1 + ξ x/σ)`. Since `w` and the logarithm are Lipschitz in `θ` uniformly in `x ≥ 0`
  (`abs_gpdW_sub_le`, `abs_log_sub_le`) and `C¹` functions are Lipschitz on compact convex sets,
  `|H(θ, x) - H(θ₀, x)| ≤ K |θ - θ₀|₁ (1 + log(1 + ξ₀ x/σ₀))`.
* *Exact expansion* (`gpdScore_sub_eq_segHess`). By the fundamental theorem of calculus along
  the segment from `θ₀` to `θ`, `∇ℓ(θ, x) - ∇ℓ(θ₀, x) = H̄(θ, x)(θ - θ₀)` with `H̄` the
  (measurable, `measurable_segHess`) average of the Hessian along the segment.
* *Convergence of the observed information* (`tendsto_avg_segHess`). By the strong law and the
  Lipschitz control, `n⁻¹ ∑ H̄(θ̂ₙ, Xᵢ) → E H(θ₀, X) = -I(θ₀)` almost surely.
* *Conclusion.* At a root, `Sₙ = -Bₙ Tₙ` with `Sₙ = n^{-1/2} ∑ ∇ℓ(θ₀; Xᵢ)`,
  `Tₙ = √n (θ̂ₙ - θ₀)` and `Bₙ → -I(θ₀)`. Solving the `2 × 2` system,
  `Tₙ - I⁻¹ Sₙ = Mₙ Sₙ` with `Mₙ → 0` almost surely, and `Sₙ` is bounded in probability, so
  `Tₙ - I⁻¹ Sₙ → 0` in probability. The CLT for `I⁻¹ Sₙ` (`tendstoInDistribution_gpdScoreLin`,
  Cramér–Wold) gives the limit `N(0, I⁻¹ I I⁻¹) = N(0, I⁻¹)`.

The restriction `ξ₀ > 0` is used only for the uniform Lipschitz control of the Hessian (for
`ξ₀ < 0` the support `[0, -σ/ξ]` moves with the parameter and `w` is unbounded near the endpoint);
the score CLT and the information identity hold for all `ξ₀ > -1/2`, `ξ₀ ≠ 0`
(`ExtremeValueTheory.Statistics.GPDFisherInformation`).

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §4.3.3.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §5.3.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### Lipschitz control of the Hessian near the true parameter -/

section Lipschitz

variable {ξ₀ σ₀ : ℝ}

/-- The closed neighbourhood `|ξ - ξ₀| ≤ ξ₀/8`, `|σ - σ₀| ≤ σ₀/8` of the true parameter, on
which the Hessian of the log-density is Lipschitz in the parameter, uniformly in the data. -/
noncomputable def gpdNbhd (ξ₀ σ₀ : ℝ) : Set (ℝ × ℝ) :=
  Icc (ξ₀ - ξ₀ / 8) (ξ₀ + ξ₀ / 8) ×ˢ Icc (σ₀ - σ₀ / 8) (σ₀ + σ₀ / 8)

lemma convex_gpdNbhd : Convex ℝ (gpdNbhd ξ₀ σ₀) := (convex_Icc _ _).prod (convex_Icc _ _)

lemma gpdNbhd_mem_nhds (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀) : gpdNbhd ξ₀ σ₀ ∈ 𝓝 (ξ₀, σ₀) :=
  prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
    (Icc_mem_nhds (by linarith) (by linarith))

lemma abs_sub_le_of_mem_gpdNbhd {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) :
    |θ.1 - ξ₀| ≤ ξ₀ / 8 ∧ |θ.2 - σ₀| ≤ σ₀ / 8 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
  exact ⟨abs_sub_le_iff.2 ⟨by linarith, by linarith⟩, abs_sub_le_iff.2 ⟨by linarith, by linarith⟩⟩

/-- The `L¹` distance `ρ(θ) = |ξ - ξ₀| + |σ - σ₀|` to the true parameter. -/
noncomputable def gpdDist (ξ₀ σ₀ : ℝ) (θ : ℝ × ℝ) : ℝ := |θ.1 - ξ₀| + |θ.2 - σ₀|

lemma gpdDist_nonneg (θ : ℝ × ℝ) : 0 ≤ gpdDist ξ₀ σ₀ θ := by unfold gpdDist; positivity

/-- `w(θ, x) = x / (σ + ξ x)`. -/
noncomputable def gpdW (θ : ℝ × ℝ) (x : ℝ) : ℝ := x / (θ.2 + θ.1 * x)

lemma log_le_two_mul_abs_sub_one {u : ℝ} (hu : 1 / 2 ≤ u) : |log u| ≤ 2 * |u - 1| := by
  have hu0 : 0 < u := by linarith
  rw [abs_le]
  constructor
  · have h := log_le_sub_one_of_pos (inv_pos.2 hu0)
    rw [log_inv] at h
    have : u⁻¹ - 1 ≤ 2 * |u - 1| := by
      rcases le_or_gt 1 u with h1 | h1
      · have : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
        nlinarith [abs_nonneg (u - 1)]
      · rw [abs_of_neg (by linarith)]
        rw [inv_eq_one_div, div_sub_one hu0.ne', div_le_iff₀ hu0]
        nlinarith
    linarith
  · have := log_le_sub_one_of_pos hu0
    nlinarith [le_abs_self (u - 1), abs_nonneg (u - 1)]

variable (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
include hξ₀ hσ₀

omit hξ₀ hσ₀ in
lemma pos_of_mem_gpdNbhd {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) :
    7 * ξ₀ / 8 ≤ θ.1 ∧ θ.1 ≤ 9 * ξ₀ / 8 ∧ 7 * σ₀ / 8 ≤ θ.2 ∧ θ.2 ≤ 9 * σ₀ / 8 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma gpdW_nonneg_le {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gpdW θ x ∧ gpdW θ x ≤ 1 / θ.1 := by
  obtain ⟨h1, -, h3, -⟩ := pos_of_mem_gpdNbhd hθ
  have hξ : 0 < θ.1 := by linarith
  have hσ : 0 < θ.2 := by linarith
  unfold gpdW
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ (by positivity) hξ]
  nlinarith

lemma mem_gpdNbhd_self : (ξ₀, σ₀) ∈ gpdNbhd ξ₀ σ₀ :=
  ⟨⟨by simp; linarith, by simp; linarith⟩, by simp; linarith, by simp; linarith⟩

/-- `|w(θ, x) - w(θ₀, x)| ≤ C_w ρ(θ)`, uniformly in `x ≥ 0`. -/
lemma abs_gpdW_sub_le {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) :
    |gpdW θ x - gpdW (ξ₀, σ₀) x| ≤
      (2 / (ξ₀ * σ₀) + 2 / ξ₀ ^ 2) * gpdDist ξ₀ σ₀ θ := by
  obtain ⟨h1, -, h3, -⟩ := pos_of_mem_gpdNbhd hθ
  have hξ : 0 < θ.1 := by linarith
  have hσ : 0 < θ.2 := by linarith
  have hd : 0 < θ.2 + θ.1 * x := by positivity
  have hd₀ : 0 < σ₀ + ξ₀ * x := by positivity
  obtain ⟨hw0, hw1⟩ := gpdW_nonneg_le hξ₀ hσ₀ hθ hx
  obtain ⟨hv0, hv1⟩ := gpdW_nonneg_le hξ₀ hσ₀ (mem_gpdNbhd_self hξ₀ hσ₀) hx
  simp only at hv1
  have key : gpdW θ x - gpdW (ξ₀, σ₀) x = (σ₀ - θ.2) * gpdW θ x * (1 / (σ₀ + ξ₀ * x)) +
      (ξ₀ - θ.1) * gpdW θ x * gpdW (ξ₀, σ₀) x := by
    unfold gpdW; simp only; field_simp; ring
  have hi : 1 / θ.1 ≤ 2 / ξ₀ := by rw [div_le_div_iff₀ hξ hξ₀]; linarith
  have hj : 1 / (σ₀ + ξ₀ * x) ≤ 1 / σ₀ := one_div_le_one_div_of_le hσ₀ (by nlinarith)
  have hj0 : 0 ≤ 1 / (σ₀ + ξ₀ * x) := by positivity
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hj0,
    abs_of_nonneg hv0, abs_sub_comm σ₀, abs_sub_comm ξ₀]
  unfold gpdDist
  have ha := abs_nonneg (θ.1 - ξ₀)
  have hb := abs_nonneg (θ.2 - σ₀)
  have e1 : |θ.2 - σ₀| * gpdW θ x * (1 / (σ₀ + ξ₀ * x)) ≤ |θ.2 - σ₀| * (2 / ξ₀) * (1 / σ₀) := by
    gcongr; exact hw1.trans hi
  have e2 : |θ.1 - ξ₀| * gpdW θ x * gpdW (ξ₀, σ₀) x ≤ |θ.1 - ξ₀| * (2 / ξ₀) * (1 / ξ₀) := by
    gcongr; exact hw1.trans hi
  have e3 : |θ.2 - σ₀| * (2 / ξ₀) * (1 / σ₀) = 2 / (ξ₀ * σ₀) * |θ.2 - σ₀| := by
    field_simp
  have e4 : |θ.1 - ξ₀| * (2 / ξ₀) * (1 / ξ₀) = 2 / ξ₀ ^ 2 * |θ.1 - ξ₀| := by
    field_simp
  have : 0 ≤ 2 / (ξ₀ * σ₀) := by positivity
  have : 0 ≤ 2 / ξ₀ ^ 2 := by positivity
  nlinarith

/-- `|log(1 + ξ x/σ) - log(1 + ξ₀ x/σ₀)| ≤ C_L ρ(θ)`, uniformly in `x ≥ 0`. -/
lemma abs_log_sub_le {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) :
    |log (1 + θ.1 * x / θ.2) - log (1 + ξ₀ * x / σ₀)| ≤
      (4 / ξ₀ + 4 / σ₀) * gpdDist ξ₀ σ₀ θ := by
  obtain ⟨h1, -, h3, -⟩ := pos_of_mem_gpdNbhd hθ
  obtain ⟨hθ1, hθ2⟩ := abs_sub_le_of_mem_gpdNbhd hθ
  have hξ : 0 < θ.1 := by linarith
  have hσ : 0 < θ.2 := by linarith
  have hA : 0 < 1 + θ.1 * x / θ.2 := by positivity
  have hB : 0 < 1 + ξ₀ * x / σ₀ := by positivity
  set u := (1 + θ.1 * x / θ.2) / (1 + ξ₀ * x / σ₀)
  set q := x / (σ₀ + ξ₀ * x)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / ξ₀ := by
    rw [div_le_div_iff₀ (by positivity) hξ₀]; nlinarith
  have hu1 : u - 1 = (σ₀ * (θ.1 - ξ₀) - ξ₀ * (θ.2 - σ₀)) / θ.2 * q := by
    simp only [u, q]; field_simp; ring
  have hi : 1 / θ.2 ≤ 2 / σ₀ := by rw [div_le_div_iff₀ hσ hσ₀]; linarith
  have hbound : |u - 1| ≤ (σ₀ * |θ.1 - ξ₀| + ξ₀ * |θ.2 - σ₀|) * (2 / σ₀) * (1 / ξ₀) := by
    rw [hu1, abs_mul, abs_div, abs_of_pos hσ, abs_of_nonneg hq0]
    have hn : |σ₀ * (θ.1 - ξ₀) - ξ₀ * (θ.2 - σ₀)| ≤ σ₀ * |θ.1 - ξ₀| + ξ₀ * |θ.2 - σ₀| := by
      refine (abs_sub _ _).trans ?_
      simp only [abs_mul, abs_of_pos hσ₀, abs_of_pos hξ₀, le_refl]
    have : |σ₀ * (θ.1 - ξ₀) - ξ₀ * (θ.2 - σ₀)| / θ.2 ≤
        (σ₀ * |θ.1 - ξ₀| + ξ₀ * |θ.2 - σ₀|) * (2 / σ₀) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hn hi (by positivity) (by positivity)
    exact mul_le_mul this hq1 hq0 (by positivity)
  have hsimp : (σ₀ * |θ.1 - ξ₀| + ξ₀ * |θ.2 - σ₀|) * (2 / σ₀) * (1 / ξ₀) =
      2 / ξ₀ * |θ.1 - ξ₀| + 2 / σ₀ * |θ.2 - σ₀| := by field_simp
  rw [hsimp] at hbound
  have hsmall : 2 / ξ₀ * |θ.1 - ξ₀| + 2 / σ₀ * |θ.2 - σ₀| ≤ 1 / 2 := by
    have e1 : 2 / ξ₀ * |θ.1 - ξ₀| ≤ 2 / ξ₀ * (ξ₀ / 8) := by gcongr
    have e2 : 2 / σ₀ * |θ.2 - σ₀| ≤ 2 / σ₀ * (σ₀ / 8) := by gcongr
    have e3 : 2 / ξ₀ * (ξ₀ / 8) = 1 / 4 := by field_simp; ring
    have e4 : 2 / σ₀ * (σ₀ / 8) = 1 / 4 := by field_simp; ring
    linarith
  have hu : 1 / 2 ≤ u := by
    have := (abs_le.1 (hbound.trans hsmall)).1
    linarith
  rw [← log_div hA.ne' hB.ne']
  refine (log_le_two_mul_abs_sub_one hu).trans ?_
  unfold gpdDist
  have : 2 * (2 / ξ₀ * |θ.1 - ξ₀| + 2 / σ₀ * |θ.2 - σ₀|) ≤
      (4 / ξ₀ + 4 / σ₀) * (|θ.1 - ξ₀| + |θ.2 - σ₀|) := by
    have : 0 ≤ 4 / ξ₀ * |θ.2 - σ₀| + 4 / σ₀ * |θ.1 - ξ₀| := by positivity
    have e : (4 / ξ₀ + 4 / σ₀) * (|θ.1 - ξ₀| + |θ.2 - σ₀|) =
        2 * (2 / ξ₀ * |θ.1 - ξ₀| + 2 / σ₀ * |θ.2 - σ₀|) +
          (4 / ξ₀ * |θ.2 - σ₀| + 4 / σ₀ * |θ.1 - ξ₀|) := by ring
    linarith
  linarith

lemma log_one_add_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ log (1 + ξ₀ * x / σ₀) :=
  log_nonneg (by have : 0 ≤ ξ₀ * x / σ₀ := by positivity
                 linarith)

/-- The compact convex box of values of `(ξ, σ, w(θ, x))`, `θ ∈ gpdNbhd ξ₀ σ₀`, `x ≥ 0`. -/
noncomputable def gpdBox (ξ₀ σ₀ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc (ξ₀ / 2) (2 * ξ₀) ×ˢ (Icc (σ₀ / 2) (2 * σ₀) ×ˢ Icc 0 (2 / ξ₀))

lemma mem_gpdBox {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) :
    (θ.1, θ.2, gpdW θ x) ∈ gpdBox ξ₀ σ₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := pos_of_mem_gpdNbhd hθ
  obtain ⟨hw0, hw1⟩ := gpdW_nonneg_le hξ₀ hσ₀ hθ hx
  have hi : 1 / θ.1 ≤ 2 / ξ₀ := by rw [div_le_div_iff₀ (by linarith) hξ₀]; linarith
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hw0, hw1.trans hi⟩

omit hξ₀ hσ₀ in
lemma dist_triple_le (p q : ℝ × ℝ × ℝ) :
    dist p q ≤ |p.1 - q.1| + |p.2.1 - q.2.1| + |p.2.2 - q.2.2| := by
  simp only [Prod.dist_eq, Real.dist_eq]
  have := abs_nonneg (p.1 - q.1); have := abs_nonneg (p.2.1 - q.2.1)
  have := abs_nonneg (p.2.2 - q.2.2)
  exact max_le (by linarith) (max_le (by linarith) (by linarith))

/-- A `C¹` function of `(ξ, σ, w)` on the box is Lipschitz in `θ` along `w(θ, x)`, uniformly in
`x ≥ 0`. -/
lemma exists_lipschitz_gpdBox {F : ℝ × ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ 1 F (gpdBox ξ₀ σ₀)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ ∈ gpdNbhd ξ₀ σ₀, ∀ x, 0 ≤ x →
      |F (θ.1, θ.2, gpdW θ x) - F (ξ₀, σ₀, gpdW (ξ₀, σ₀) x)| ≤ K * gpdDist ξ₀ σ₀ θ := by
  have hc : IsCompact (gpdBox ξ₀ σ₀) := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hv : Convex ℝ (gpdBox ξ₀ σ₀) :=
    (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))
  obtain ⟨K, hK⟩ := hF.exists_lipschitzOnWith one_ne_zero hv hc
  set Cw := 2 / (ξ₀ * σ₀) + 2 / ξ₀ ^ 2
  have hCw : 0 ≤ Cw := by positivity
  refine ⟨K * (1 + Cw), by positivity, fun θ hθ x hx => ?_⟩
  have h := hK.dist_le_mul _ (mem_gpdBox hξ₀ hσ₀ hθ hx) _
    (mem_gpdBox hξ₀ hσ₀ (mem_gpdNbhd_self hξ₀ hσ₀) hx)
  rw [Real.dist_eq] at h
  refine h.trans ?_
  have hd := dist_triple_le (θ.1, θ.2, gpdW θ x) (ξ₀, σ₀, gpdW (ξ₀, σ₀) x)
  simp only at hd
  have hw := abs_gpdW_sub_le hξ₀ hσ₀ hθ hx
  have : dist (θ.1, θ.2, gpdW θ x) (ξ₀, σ₀, gpdW (ξ₀, σ₀) x) ≤ (1 + Cw) * gpdDist ξ₀ σ₀ θ := by
    unfold gpdDist at hw ⊢
    linarith
  calc (K : ℝ) * dist (θ.1, θ.2, gpdW θ x) (ξ₀, σ₀, gpdW (ξ₀, σ₀) x)
      ≤ K * ((1 + Cw) * gpdDist ξ₀ σ₀ θ) := by gcongr
    _ = K * (1 + Cw) * gpdDist ξ₀ σ₀ θ := by ring

/-- **The Hessian of the GPD log-density is Lipschitz near `θ₀`**, with a Lipschitz constant
growing like `log(1 + ξ₀ x/σ₀)` in the data: for `θ ∈ gpdNbhd ξ₀ σ₀` and `x ≥ 0`,
`|H(θ, x) - H(θ₀, x)| ≤ K ρ(θ) (1 + log(1 + ξ₀ x/σ₀))` entrywise. -/
theorem exists_gpdHess_lipschitz :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ ∈ gpdNbhd ξ₀ σ₀, ∀ x, 0 ≤ x →
      |gpdHessXiXi θ.1 θ.2 x - gpdHessXiXi ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessXiSigma θ.1 θ.2 x - gpdHessXiSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessSigmaSigma θ.1 θ.2 x - gpdHessSigmaSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) := by
  have hbox : ∀ p ∈ gpdBox ξ₀ σ₀, 0 < p.1 ∧ 0 < p.2.1 := fun p hp => by
    obtain ⟨⟨h1, -⟩, ⟨h2, -⟩, -⟩ := hp
    exact ⟨by linarith, by linarith⟩
  have c0 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => -2 / p.1 ^ 3) (gpdBox ξ₀ σ₀) := by
    fun_prop (disch := intro p hp; have := (hbox p hp).1; positivity)
  have c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => 2 * p.2.2 / p.1 ^ 2 + (1 / p.1 + 1) * p.2.2 ^ 2)
      (gpdBox ξ₀ σ₀) := by
    fun_prop (disch := intro p hp; have := (hbox p hp).1; positivity)
  have c2 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => (p.2.2 - (1 + p.1) * p.2.2 ^ 2) / p.2.1)
      (gpdBox ξ₀ σ₀) := by
    fun_prop (disch := intro p hp; have := (hbox p hp).2; positivity)
  have c3 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
      (1 - 2 * (1 + p.1) * p.2.2 + p.1 * (1 + p.1) * p.2.2 ^ 2) / p.2.1 ^ 2) (gpdBox ξ₀ σ₀) := by
    fun_prop (disch := intro p hp; have := (hbox p hp).2; positivity)
  obtain ⟨K0, hK0, h0⟩ := exists_lipschitz_gpdBox hξ₀ hσ₀ c0
  obtain ⟨K1, hK1, h1⟩ := exists_lipschitz_gpdBox hξ₀ hσ₀ c1
  obtain ⟨K2, hK2, h2⟩ := exists_lipschitz_gpdBox hξ₀ hσ₀ c2
  obtain ⟨K3, hK3, h3⟩ := exists_lipschitz_gpdBox hξ₀ hσ₀ c3
  set CL := 4 / ξ₀ + 4 / σ₀
  have hCL : 0 ≤ CL := by positivity
  refine ⟨16 / ξ₀ ^ 3 * CL + K0 + K1 + K2 + K3, by positivity, fun θ hθ x hx => ?_⟩
  have hρ := gpdDist_nonneg (ξ₀ := ξ₀) (σ₀ := σ₀) θ
  have hL₀ := log_one_add_nonneg hξ₀ hσ₀ hx
  set ρ := gpdDist ξ₀ σ₀ θ
  set L₀ := log (1 + ξ₀ * x / σ₀)
  have hρL : ρ ≤ ρ * (1 + L₀) := le_mul_of_one_le_right hρ (by linarith)
  have hρL' : ρ * L₀ ≤ ρ * (1 + L₀) := mul_le_mul_of_nonneg_left (by linarith) hρ
  have hK : ∀ k : ℝ, 0 ≤ k → k ≤ 16 / ξ₀ ^ 3 * CL + K0 + K1 + K2 + K3 →
      k * ρ ≤ (16 / ξ₀ ^ 3 * CL + K0 + K1 + K2 + K3) * ρ * (1 + L₀) := fun k hk hkK => by
    calc k * ρ ≤ (16 / ξ₀ ^ 3 * CL + K0 + K1 + K2 + K3) * ρ := by gcongr
      _ ≤ _ := by rw [mul_assoc]; gcongr
  have h16 : 0 ≤ 16 / ξ₀ ^ 3 * CL := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- the `ξξ` entry carries the logarithm
    have e : ∀ ξ σ : ℝ, gpdHessXiXi ξ σ x = (-2 / ξ ^ 3) * log (1 + ξ * x / σ) +
        (2 * gpdW (ξ, σ) x / ξ ^ 2 + (1 / ξ + 1) * gpdW (ξ, σ) x ^ 2) := fun ξ σ => by
      unfold gpdHessXiXi gpdW; simp only; ring
    rw [e, e]
    obtain ⟨hξ1, -, -, -⟩ := pos_of_mem_gpdNbhd hθ
    have hξ : 0 < θ.1 := by linarith
    have hF0 : |-2 / θ.1 ^ 3| ≤ 16 / ξ₀ ^ 3 := by
      rw [abs_div, abs_neg, abs_two, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      have : ξ₀ ^ 3 ≤ (2 * θ.1) ^ 3 := pow_le_pow_left₀ hξ₀.le (by linarith) 3
      nlinarith
    have hlog := abs_log_sub_le hξ₀ hσ₀ hθ hx
    have hA := h0 θ hθ x hx
    have hB := h1 θ hθ x hx
    simp only at hA hB
    have split : (-2 / θ.1 ^ 3) * log (1 + θ.1 * x / θ.2) +
        (2 * gpdW (θ.1, θ.2) x / θ.1 ^ 2 + (1 / θ.1 + 1) * gpdW (θ.1, θ.2) x ^ 2) -
        ((-2 / ξ₀ ^ 3) * L₀ + (2 * gpdW (ξ₀, σ₀) x / ξ₀ ^ 2 +
          (1 / ξ₀ + 1) * gpdW (ξ₀, σ₀) x ^ 2)) =
        (-2 / θ.1 ^ 3) * (log (1 + θ.1 * x / θ.2) - L₀) + (-2 / θ.1 ^ 3 - -2 / ξ₀ ^ 3) * L₀ +
        ((2 * gpdW θ x / θ.1 ^ 2 + (1 / θ.1 + 1) * gpdW θ x ^ 2) -
          (2 * gpdW (ξ₀, σ₀) x / ξ₀ ^ 2 + (1 / ξ₀ + 1) * gpdW (ξ₀, σ₀) x ^ 2)) := by
      simp only [Prod.mk.eta]; ring
    rw [split]
    have t1 : |(-2 / θ.1 ^ 3) * (log (1 + θ.1 * x / θ.2) - L₀)| ≤ 16 / ξ₀ ^ 3 * CL * ρ := by
      rw [abs_mul, mul_assoc]
      exact mul_le_mul hF0 hlog (abs_nonneg _) (by positivity)
    have t2 : |(-2 / θ.1 ^ 3 - -2 / ξ₀ ^ 3) * L₀| ≤ K0 * ρ * L₀ := by
      rw [abs_mul, abs_of_nonneg hL₀]
      exact mul_le_mul_of_nonneg_right hA hL₀
    have t3 := hB
    have := abs_add_three ((-2 / θ.1 ^ 3) * (log (1 + θ.1 * x / θ.2) - L₀))
      ((-2 / θ.1 ^ 3 - -2 / ξ₀ ^ 3) * L₀)
      ((2 * gpdW θ x / θ.1 ^ 2 + (1 / θ.1 + 1) * gpdW θ x ^ 2) -
          (2 * gpdW (ξ₀, σ₀) x / ξ₀ ^ 2 + (1 / ξ₀ + 1) * gpdW (ξ₀, σ₀) x ^ 2))
    have hsum : 16 / ξ₀ ^ 3 * CL * ρ + K0 * ρ * L₀ + K1 * ρ ≤
        (16 / ξ₀ ^ 3 * CL + K0 + K1 + K2 + K3) * ρ * (1 + L₀) := by
      have := mul_le_mul_of_nonneg_left hρL (add_nonneg h16 hK1)
      have := mul_le_mul_of_nonneg_left hρL' hK0
      have : 0 ≤ (K0 * ρ + K2 * ρ + K3 * ρ) * (1 + L₀) + (16 / ξ₀ ^ 3 * CL + K1) * ρ * L₀ := by
        positivity
      nlinarith
    linarith
  · have e : ∀ ξ σ : ℝ, gpdHessXiSigma ξ σ x =
        (gpdW (ξ, σ) x - (1 + ξ) * gpdW (ξ, σ) x ^ 2) / σ := fun ξ σ => rfl
    rw [e, e]
    have := h2 θ hθ x hx
    simp only at this
    exact this.trans (hK K2 hK2 (by linarith))
  · have e : ∀ ξ σ : ℝ, gpdHessSigmaSigma ξ σ x =
        (1 - 2 * (1 + ξ) * gpdW (ξ, σ) x + ξ * (1 + ξ) * gpdW (ξ, σ) x ^ 2) / σ ^ 2 :=
      fun ξ σ => rfl
    rw [e, e]
    have := h3 θ hθ x hx
    simp only at this
    exact this.trans (hK K3 hK3 (by linarith))

end Lipschitz

/-! ### The score along a segment in parameter space -/

section Segment

variable {ξ σ a b x s : ℝ}

/-- The derivative of the shape score along the line `s ↦ (ξ + s a, σ + s b)`. -/
theorem hasDerivAt_gpdScoreXi_line (hξ : ξ + s * a ≠ 0) (hσ : 0 < σ + s * b)
    (hu : 0 < (σ + s * b) + (ξ + s * a) * x) :
    HasDerivAt (fun s => gpdScoreXi (ξ + s * a) (σ + s * b) x)
      (a * gpdHessXiXi (ξ + s * a) (σ + s * b) x +
        b * gpdHessXiSigma (ξ + s * a) (σ + s * b) x) s := by
  have hu' := one_add_mul_div_pos hσ hu
  have hA : HasDerivAt (fun s => ξ + s * a) a s := by
    simpa using ((hasDerivAt_id s).mul_const a).const_add ξ
  have hB : HasDerivAt (fun s => σ + s * b) b s := by
    simpa using ((hasDerivAt_id s).mul_const b).const_add σ
  have hR : HasDerivAt (fun s => (ξ + s * a) * x / (σ + s * b))
      ((a * x * (σ + s * b) - (ξ + s * a) * x * b) / (σ + s * b) ^ 2) s :=
    (hA.mul_const x).div hB hσ.ne'
  have hL : HasDerivAt (fun s => log (1 + (ξ + s * a) * x / (σ + s * b)))
      (((a * x * (σ + s * b) - (ξ + s * a) * x * b) / (σ + s * b) ^ 2) /
        (1 + (ξ + s * a) * x / (σ + s * b))) s :=
    (hR.const_add 1).log hu'.ne'
  have hS : HasDerivAt (fun s => (ξ + s * a) ^ 2) (2 * (ξ + s * a) * a) s := by
    convert hA.mul hA using 1
    · funext s; simp only [Pi.mul_apply]; ring
    · ring
  have hD : HasDerivAt (fun s => (σ + s * b) + (ξ + s * a) * x) (b + a * x) s :=
    hB.add (hA.mul_const x)
  have hW : HasDerivAt (fun s => x / ((σ + s * b) + (ξ + s * a) * x))
      (-(x * (b + a * x)) / ((σ + s * b) + (ξ + s * a) * x) ^ 2) s := by
    have := (hasDerivAt_const s x).div hD hu.ne'
    exact this.congr_deriv (by ring)
  have hI : HasDerivAt (fun s => 1 / (ξ + s * a) + 1) (-(a / (ξ + s * a) ^ 2)) s := by
    have := (hA.inv hξ).add_const 1
    exact (this.congr_deriv (by ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => by simp [one_div])
  have := (hL.div hS (pow_ne_zero 2 hξ)).sub (hI.mul hW)
  unfold gpdScoreXi gpdHessXiXi gpdHessXiSigma
  refine this.congr_deriv ?_
  generalize ξ + s * a = p at hξ hu hu' ⊢
  generalize σ + s * b = q at hσ hu hu' ⊢
  have := hσ.ne'
  have h1 : q + p * x ≠ 0 := hu.ne'
  have h2 : x * p + q ≠ 0 := by rw [add_comm, mul_comm]; exact h1
  have h3 : p * x + q ≠ 0 := by rw [add_comm]; exact h1
  have h4 : q + x * p ≠ 0 := by rw [mul_comm]; exact h1
  field_simp
  ring

/-- The derivative of the scale score along the line `s ↦ (ξ + s a, σ + s b)`. -/
theorem hasDerivAt_gpdScoreSigma_line (hσ : 0 < σ + s * b)
    (hu : 0 < (σ + s * b) + (ξ + s * a) * x) :
    HasDerivAt (fun s => gpdScoreSigma (ξ + s * a) (σ + s * b) x)
      (a * gpdHessXiSigma (ξ + s * a) (σ + s * b) x +
        b * gpdHessSigmaSigma (ξ + s * a) (σ + s * b) x) s := by
  have hA : HasDerivAt (fun s => ξ + s * a) a s := by
    simpa using ((hasDerivAt_id s).mul_const a).const_add ξ
  have hB : HasDerivAt (fun s => σ + s * b) b s := by
    simpa using ((hasDerivAt_id s).mul_const b).const_add σ
  have hD : HasDerivAt (fun s => (σ + s * b) + (ξ + s * a) * x) (b + a * x) s :=
    hB.add (hA.mul_const x)
  have hW : HasDerivAt (fun s => x / ((σ + s * b) + (ξ + s * a) * x))
      (-(x * (b + a * x)) / ((σ + s * b) + (ξ + s * a) * x) ^ 2) s := by
    have := (hasDerivAt_const s x).div hD hu.ne'
    exact this.congr_deriv (by ring)
  have := ((((hA.const_add 1).mul hW).sub_const 1).div hB hσ.ne')
  unfold gpdScoreSigma gpdHessXiSigma gpdHessSigmaSigma
  refine this.congr_deriv ?_
  simp only [Pi.mul_apply]
  generalize ξ + s * a = p at hu ⊢
  generalize σ + s * b = q at hσ hu ⊢
  have := hσ.ne'
  have h1 : q + p * x ≠ 0 := hu.ne'
  have h2 : x * p + q ≠ 0 := by rw [add_comm, mul_comm]; exact h1
  have h3 : p * x + q ≠ 0 := by rw [add_comm]; exact h1
  have h4 : q + x * p ≠ 0 := by rw [mul_comm]; exact h1
  field_simp
  ring

/-- A measurable function on `[0, 1]` within `C` of a constant `c` is interval integrable and
its integral is within `C` of `c`. -/
lemma intervalIntegrable_and_abs_integral_sub_le {f : ℝ → ℝ} (hf : Measurable f) {c C : ℝ}
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, |f s - c| ≤ C) :
    IntervalIntegrable f volume 0 1 ∧ |(∫ s in (0 : ℝ)..1, f s) - c| ≤ C := by
  have hI : ∀ s ∈ Set.uIoc (0 : ℝ) 1, s ∈ Icc (0 : ℝ) 1 := fun s hs => by
    rw [uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le, hs.2⟩
  have hint : IntervalIntegrable f volume 0 1 := by
    refine (intervalIntegrable_const (c := |c| + C)).mono_fun' hf.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun s hs => ?_)
    have h := hb s (hI s hs)
    simp only [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (f s) c
    linarith
  refine ⟨hint, ?_⟩
  have e : (∫ s in (0 : ℝ)..1, f s) - c = ∫ s in (0 : ℝ)..1, (f s - c) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun s => f s - c) (C := C) fun s hs => by rw [Real.norm_eq_abs]; exact hb s (hI s hs)
  simpa using this

end Segment

/-! ### The exact expansion of the score around the true parameter -/

section Expansion

variable {ξ₀ σ₀ : ℝ}

/-- The Hessian entry `H` averaged along the segment from `θ₀ = (ξ₀, σ₀)` to `θ`. -/
noncomputable def segHess (H : ℝ → ℝ → ℝ → ℝ) (ξ₀ σ₀ : ℝ) (θ : ℝ × ℝ) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x

variable (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
include hξ₀ hσ₀

lemma segment_mem_gpdNbhd {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀)) ∈ gpdNbhd ξ₀ σ₀ := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
  obtain ⟨hs0, hs1⟩ := hs
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [mul_nonneg hs0 (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hs1) hξ₀.le]
  · nlinarith [mul_nonneg hs0 (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 hs1) hξ₀.le]
  · nlinarith [mul_nonneg hs0 (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 hs1) hσ₀.le]
  · nlinarith [mul_nonneg hs0 (sub_nonneg.2 h4), mul_nonneg (sub_nonneg.2 hs1) hσ₀.le]

omit hξ₀ hσ₀ in
lemma gpdDist_segment (θ : ℝ × ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    gpdDist ξ₀ σ₀ (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀)) ≤ gpdDist ξ₀ σ₀ θ := by
  unfold gpdDist
  simp only [add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
  have := abs_nonneg (θ.1 - ξ₀); have := abs_nonneg (θ.2 - σ₀)
  nlinarith [hs.2]

/-- **The exact expansion of the score.** Given the Lipschitz control `hK` of the Hessian, for
`θ ∈ gpdNbhd ξ₀ σ₀` and `x ≥ 0` the segment averages of the Hessian are within
`K ρ(θ) (1 + log(1 + ξ₀ x/σ₀))` of the Hessian at `θ₀`, and
`∇ℓ(θ, x) - ∇ℓ(θ₀, x) = H̄(θ, x) (θ - θ₀)` with `H̄` the segment average. -/
theorem gpdScore_sub_eq_segHess {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ θ ∈ gpdNbhd ξ₀ σ₀, ∀ x, 0 ≤ x →
      |gpdHessXiXi θ.1 θ.2 x - gpdHessXiXi ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessXiSigma θ.1 θ.2 x - gpdHessXiSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessSigmaSigma θ.1 θ.2 x - gpdHessSigmaSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)))
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) :
    gpdScoreXi θ.1 θ.2 x - gpdScoreXi ξ₀ σ₀ x =
        (θ.1 - ξ₀) * segHess gpdHessXiXi ξ₀ σ₀ θ x +
          (θ.2 - σ₀) * segHess gpdHessXiSigma ξ₀ σ₀ θ x ∧
    gpdScoreSigma θ.1 θ.2 x - gpdScoreSigma ξ₀ σ₀ x =
        (θ.1 - ξ₀) * segHess gpdHessXiSigma ξ₀ σ₀ θ x +
          (θ.2 - σ₀) * segHess gpdHessSigmaSigma ξ₀ σ₀ θ x ∧
    |segHess gpdHessXiXi ξ₀ σ₀ θ x - gpdHessXiXi ξ₀ σ₀ x| ≤
        K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
    |segHess gpdHessXiSigma ξ₀ σ₀ θ x - gpdHessXiSigma ξ₀ σ₀ x| ≤
        K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
    |segHess gpdHessSigmaSigma ξ₀ σ₀ θ x - gpdHessSigmaSigma ξ₀ σ₀ x| ≤
        K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) := by
  set a := θ.1 - ξ₀
  set b := θ.2 - σ₀
  have hL₀ := log_one_add_nonneg hξ₀ hσ₀ hx
  -- bounds along the segment
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1,
      |gpdHessXiXi (ξ₀ + s * a) (σ₀ + s * b) x - gpdHessXiXi ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessXiSigma (ξ₀ + s * a) (σ₀ + s * b) x - gpdHessXiSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessSigmaSigma (ξ₀ + s * a) (σ₀ + s * b) x - gpdHessSigmaSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) := fun s hs => by
    have hmem := segment_mem_gpdNbhd hξ₀ hσ₀ hθ hs
    have hd := gpdDist_segment (ξ₀ := ξ₀) (σ₀ := σ₀) θ hs
    have hmono : K * gpdDist ξ₀ σ₀ (ξ₀ + s * a, σ₀ + s * b) * (1 + log (1 + ξ₀ * x / σ₀)) ≤
        K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) := by gcongr
    obtain ⟨h1, h2, h3⟩ := hK _ hmem x hx
    exact ⟨h1.trans hmono, h2.trans hmono, h3.trans hmono⟩
  obtain ⟨iXX, bXX⟩ := intervalIntegrable_and_abs_integral_sub_le
    (f := fun s => gpdHessXiXi (ξ₀ + s * a) (σ₀ + s * b) x)
    (by unfold gpdHessXiXi; fun_prop) fun s hs => (hseg s hs).1
  obtain ⟨iXS, bXS⟩ := intervalIntegrable_and_abs_integral_sub_le
    (f := fun s => gpdHessXiSigma (ξ₀ + s * a) (σ₀ + s * b) x)
    (by unfold gpdHessXiSigma; fun_prop) fun s hs => (hseg s hs).2.1
  obtain ⟨iSS, bSS⟩ := intervalIntegrable_and_abs_integral_sub_le
    (f := fun s => gpdHessSigmaSigma (ξ₀ + s * a) (σ₀ + s * b) x)
    (by unfold gpdHessSigmaSigma; fun_prop) fun s hs => (hseg s hs).2.2
  -- positivity along the segment
  have hpos : ∀ s ∈ uIcc (0 : ℝ) 1, ξ₀ + s * a ≠ 0 ∧ 0 < σ₀ + s * b ∧
      0 < (σ₀ + s * b) + (ξ₀ + s * a) * x := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    obtain ⟨h1, -, h3, -⟩ := pos_of_mem_gpdNbhd (segment_mem_gpdNbhd hξ₀ hσ₀ hθ hs)
    simp only at h1 h3
    have h5 : 0 < ξ₀ + s * a := by linarith
    have h6 : 0 < σ₀ + s * b := by linarith
    have h7 : 0 ≤ (ξ₀ + s * a) * x := by positivity
    exact ⟨h5.ne', h6, by linarith⟩
  have e1 : ξ₀ + 1 * a = θ.1 := by simp [a]
  have e2 : σ₀ + 1 * b = θ.2 := by simp [b]
  refine ⟨?_, ?_, bXX, bXS, bSS⟩
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => gpdScoreXi (ξ₀ + s * a) (σ₀ + s * b) x)
      (fun s hs => hasDerivAt_gpdScoreXi_line (hpos s hs).1 (hpos s hs).2.1 (hpos s hs).2.2)
      ((iXX.const_mul a).add (iXS.const_mul b))
    rw [intervalIntegral.integral_add (iXX.const_mul a) (iXS.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
    simp only [e1, e2, zero_mul, add_zero] at hftc
    rw [← hftc]
    rfl
  · have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => gpdScoreSigma (ξ₀ + s * a) (σ₀ + s * b) x)
      (fun s hs => hasDerivAt_gpdScoreSigma_line (hpos s hs).2.1 (hpos s hs).2.2)
      ((iXS.const_mul a).add (iSS.const_mul b))
    rw [intervalIntegral.integral_add (iXS.const_mul a) (iSS.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
    simp only [e1, e2, zero_mul, add_zero] at hftc
    rw [← hftc]
    rfl

omit hξ₀ hσ₀ in
/-- The segment average of a jointly measurable Hessian entry is jointly measurable in the
parameter and the observation. -/
lemma measurable_segHess {H : ℝ → ℝ → ℝ → ℝ}
    (hH : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) :
    Measurable fun p : (ℝ × ℝ) × ℝ => segHess H ξ₀ σ₀ p.1 p.2 := by
  have : (fun p : (ℝ × ℝ) × ℝ => segHess H ξ₀ σ₀ p.1 p.2) = fun p =>
      ∫ s, H (ξ₀ + s * (p.1.1 - ξ₀)) (σ₀ + s * (p.1.2 - σ₀)) p.2 ∂(volume.restrict (Ioc 0 1)) := by
    funext p
    rw [segHess, intervalIntegral.integral_of_le zero_le_one]
  rw [this]
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right
    (f := fun p : (ℝ × ℝ) × ℝ => fun s : ℝ => H (ξ₀ + s * (p.1.1 - ξ₀)) (σ₀ + s * (p.1.2 - σ₀)) p.2)
    ?_
  refine Measurable.stronglyMeasurable ?_
  exact hH.comp (f := fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
    (ξ₀ + q.2 * (q.1.1.1 - ξ₀), σ₀ + q.2 * (q.1.1.2 - σ₀), q.1.2)) (by fun_prop)

omit hξ₀ hσ₀ in
lemma measurable_gpdHessXiXi₃ : Measurable fun q : ℝ × ℝ × ℝ => gpdHessXiXi q.1 q.2.1 q.2.2 := by
  unfold gpdHessXiXi; fun_prop

omit hξ₀ hσ₀ in
lemma measurable_gpdHessXiSigma₃ :
    Measurable fun q : ℝ × ℝ × ℝ => gpdHessXiSigma q.1 q.2.1 q.2.2 := by
  unfold gpdHessXiSigma; fun_prop

omit hξ₀ hσ₀ in
lemma measurable_gpdHessSigmaSigma₃ :
    Measurable fun q : ℝ × ℝ × ℝ => gpdHessSigmaSigma q.1 q.2.1 q.2.2 := by
  unfold gpdHessSigmaSigma; fun_prop

/-- **Convergence of the averaged segment Hessian** (deterministic): if `θₙ → θ₀`, the empirical
mean of `H(θ₀, xᵢ)` tends to `m` and that of `log(1 + ξ₀ xᵢ/σ₀)` converges, and `H` satisfies the
Lipschitz control along segments, then the empirical mean of the segment averages
`H̄(θₙ, xᵢ)` tends to `m` as well. -/
theorem tendsto_avg_segHess {H : ℝ → ℝ → ℝ → ℝ} {K : ℝ}
    (hK : ∀ θ ∈ gpdNbhd ξ₀ σ₀, ∀ x, 0 ≤ x → |segHess H ξ₀ σ₀ θ x - H ξ₀ σ₀ x| ≤
      K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)))
    {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {θs : ℕ → ℝ × ℝ} (hθ : Tendsto θs atTop (𝓝 (ξ₀, σ₀)))
    {m ℓ : ℝ} (hm : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (x i))
      atTop (𝓝 m))
    (hℓ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, log (1 + ξ₀ * x i / σ₀))
      atTop (𝓝 ℓ)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess H ξ₀ σ₀ (θs n) (x i))
      atTop (𝓝 m) := by
  have hρ : Tendsto (fun n => gpdDist ξ₀ σ₀ (θs n)) atTop (𝓝 0) := by
    have hc : Continuous (gpdDist ξ₀ σ₀) := by unfold gpdDist; fun_prop
    have := (hc.tendsto (ξ₀, σ₀)).comp hθ
    rwa [show gpdDist ξ₀ σ₀ (ξ₀, σ₀) = 0 by simp [gpdDist]] at this
  have hbound : Tendsto (fun n : ℕ => K * gpdDist ξ₀ σ₀ (θs n) *
      (1 + (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, log (1 + ξ₀ * x i / σ₀))) atTop (𝓝 0) := by
    have := ((hρ.const_mul K).mul (hℓ.const_add 1))
    simpa using this
  have hdiff : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess H ξ₀ σ₀ (θs n) (x i)
      - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (x i)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hθ.eventually (gpdNbhd_mem_nhds hξ₀ hσ₀), eventually_gt_atTop 0]
      with n hn hn0
    rw [Real.norm_eq_abs, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
      abs_of_pos (inv_pos.2 (Nat.cast_pos.2 hn0))]
    refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
      (inv_pos.2 (Nat.cast_pos.2 hn0)).le).trans ?_
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hsum : ∑ i ∈ Finset.range n, |segHess H ξ₀ σ₀ (θs n) (x i) - H ξ₀ σ₀ (x i)| ≤
        ∑ i ∈ Finset.range n, K * gpdDist ξ₀ σ₀ (θs n) * (1 + log (1 + ξ₀ * x i / σ₀)) :=
      Finset.sum_le_sum fun i _ => hK _ hn _ (hx i)
    calc (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |segHess H ξ₀ σ₀ (θs n) (x i) - H ξ₀ σ₀ (x i)|
        ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          K * gpdDist ξ₀ σ₀ (θs n) * (1 + log (1 + ξ₀ * x i / σ₀)) := by gcongr
      _ = K * gpdDist ξ₀ σ₀ (θs n) *
          (1 + (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, log (1 + ξ₀ * x i / σ₀)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
        field_simp
  have := hdiff.add hm
  simpa using this

end Expansion

/-! ### The inverse information as the adjugate over the determinant -/

section Adjugate

variable {ξ σ : ℝ}

/-- `det I(ξ, σ) = 1/(σ² (1 + ξ)² (1 + 2ξ))`, and `I⁻¹ = adj(I)/det(I)` entrywise. -/
lemma gpdFisherInfo_det_adj (hξ : -1 / 2 < ξ) (hσ : 0 < σ) :
    let I11 := 2 / ((1 + ξ) * (1 + 2 * ξ))
    let I12 := 1 / (σ * (1 + ξ) * (1 + 2 * ξ))
    let I22 := 1 / (σ ^ 2 * (1 + 2 * ξ))
    0 < I11 * I22 - I12 ^ 2 ∧
    I22 / (I11 * I22 - I12 ^ 2) = (1 + ξ) * (1 + ξ) ∧
    -I12 / (I11 * I22 - I12 ^ 2) = (1 + ξ) * -σ ∧
    I11 / (I11 * I22 - I12 ^ 2) = (1 + ξ) * (2 * σ ^ 2) := by
  intro I11 I12 I22
  have h1ξ : 0 < 1 + ξ := by linarith
  have h2ξ : 0 < 1 + 2 * ξ := by linarith
  have h2ξ' : 1 + ξ * 2 ≠ 0 := by intro h; linarith
  have hdet : I11 * I22 - I12 ^ 2 = 1 / (σ ^ 2 * (1 + ξ) ^ 2 * (1 + 2 * ξ)) := by
    simp only [I11, I12, I22]
    field_simp
    ring
  rw [hdet]
  refine ⟨by positivity, ?_, ?_, ?_⟩ <;> simp only [I11, I12, I22] <;> field_simp

end Adjugate

/-! ### Central limit theorems for linear images of the score -/

section ScoreLin

open RealInnerProductSpace Matrix

variable {ξ σ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
  [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ}

/-- The quadratic form of the Fisher information. -/
noncomputable def gpdInfoQuad (ξ σ c₁ c₂ : ℝ) : ℝ :=
  c₁ ^ 2 * (2 / ((1 + ξ) * (1 + 2 * ξ))) + 2 * c₁ * c₂ * (1 / (σ * (1 + ξ) * (1 + 2 * ξ))) +
    c₂ ^ 2 * (1 / (σ ^ 2 * (1 + 2 * ξ)))

/-- The image `M ∇ℓ(ξ, σ; x)` of the score under the matrix `[[m₁₁, m₁₂], [m₂₁, m₂₂]]`. -/
noncomputable def gpdScoreLin (m₁₁ m₁₂ m₂₁ m₂₂ ξ σ x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[m₁₁ * gpdScoreXi ξ σ x + m₁₂ * gpdScoreSigma ξ σ x,
    m₂₁ * gpdScoreXi ξ σ x + m₂₂ * gpdScoreSigma ξ σ x]

/-- The scalar CLT for a combination of the scores: `n^{-1/2} ∑ (c₁ ∂_ξ ℓ + c₂ ∂_σ ℓ)(Xᵢ)`
converges to `N(0, Q_I(c₁, c₂))`. -/
theorem tendstoInDistribution_lin_score (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ) P) (hind : iIndepFun X P) (c₁ c₂ : ℝ)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (gpdInfoQuad ξ σ c₁ c₂).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
      (c₁ * gpdScoreXi ξ σ (X i ω) + c₂ * gpdScoreSigma ξ σ (X i ω))) atTop Z (fun _ => P) P' := by
  set f : ℝ → ℝ := fun x => c₁ * gpdScoreXi ξ σ x + c₂ * gpdScoreSigma ξ σ x
  have hf : Measurable f := by
    have := measurable_gpdScoreXi ξ σ; have := measurable_gpdScoreSigma ξ σ
    simp only [f]; fun_prop
  set Y : ℕ → Ω → ℝ := fun i => f ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => f) (fun _ => hf)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hf
  have hmemLp : MemLp (Y 0) 2 P := by
    rw [← memLp_map_measure_iff hf.aestronglyMeasurable (hX 0).aemeasurable, (hX 0).map_eq]
    exact memLp_lin_score hσ hξ0 hξ _ _
  have hint : ∀ g : ℝ → ℝ, Measurable g → P[g ∘ X 0] = ∫ x, g x ∂gpdMeasure ξ σ :=
    fun g hg => (hX 0).integral_comp hg.aestronglyMeasurable
  have hmean : P[Y 0] = 0 := by
    rw [hint f hf]
    simp only [f]
    rw [integral_add, integral_const_mul, integral_const_mul, integral_gpdScoreXi hσ hξ0 hξ,
      integral_gpdScoreSigma hσ hξ0 hξ, mul_zero, mul_zero, add_zero]
    · exact ((memLp_lin_score hσ hξ0 hξ c₁ 0).integrable one_le_two).congr
        (ae_of_all _ fun x => by simp)
    · exact ((memLp_lin_score hσ hξ0 hξ 0 c₂).integrable one_le_two).congr
        (ae_of_all _ fun x => by simp)
  have hvar : Var[Y 0; P] = gpdInfoQuad ξ σ c₁ c₂ := by
    rw [variance_of_integral_eq_zero (hf.comp_aemeasurable (hX 0).aemeasurable) hmean]
    have := hint (fun x => f x ^ 2) (hf.pow_const 2)
    simp only [Function.comp_def] at this
    simp only [Function.comp_def]
    rw [this, integral_lin_score_sq hσ hξ0 hξ]
    rfl
  have hZt : HasLaw Z (gaussianReal 0 Var[Y 0; P].toNNReal) P' := by rw [hvar]; exact hZ
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZt hmemLp hind' hident
  rw [hmean] at hclt
  convert hclt using 3 with n ω
  simp [Y, f]

/-- The normalized sums of a combination of the scores are bounded in probability. -/
theorem isBoundedInProbability_lin_score (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ) P) (hind : iIndepFun X P) (c₁ c₂ : ℝ) :
    IsBoundedInProbability P (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
      (c₁ * gpdScoreXi ξ σ (X i ω) + c₂ * gpdScoreSigma ξ σ (X i ω))) :=
  isBoundedInProbability_of_tendstoInDistribution
    (tendstoInDistribution_lin_score (P' := gaussianReal 0 (gpdInfoQuad ξ σ c₁ c₂).toNNReal)
      hξ hξ0 hσ hX hind c₁ c₂ HasLaw.id)

/-- **The bivariate CLT for a linear image of the score**: `n^{-1/2} ∑ M ∇ℓ(Xᵢ) ⇒ N(0, Σ)`
whenever `Q_I(Mᵀ t) = tᵀ Σ t` for all `t`. -/
theorem tendstoInDistribution_gpdScoreLin (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ) P) (hind : iIndepFun X P)
    (m₁₁ m₁₂ m₂₁ m₂₂ : ℝ) {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosSemidef)
    (hQ : ∀ t : Fin 2 → ℝ, gpdInfoQuad ξ σ (t 0 * m₁₁ + t 1 * m₂₁) (t 0 * m₁₂ + t 1 * m₂₂) =
      t ⬝ᵥ S *ᵥ t)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)} (hW : HasLaw W (multivariateGaussian 0 S) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
        gpdScoreLin m₁₁ m₁₂ m₂₁ m₂₂ ξ σ (X i ω))
      atTop W (fun _ => P) P' := by
  refine TendstoInDistribution.of_inner hW.aemeasurable (fun n => ?_) fun t => ?_
  · have : Measurable (gpdScoreLin m₁₁ m₁₂ m₂₁ m₂₂ ξ σ) := by
      unfold gpdScoreLin
      refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
      have := measurable_gpdScoreXi ξ σ; have := measurable_gpdScoreSigma ξ σ
      fin_cases i <;> simp <;> fun_prop
    have := fun i => (hX i).aemeasurable
    fun_prop
  have hZt := hasLaw_inner_multivariateGaussian hS hW t
  rw [← hQ] at hZt
  have hclt := tendstoInDistribution_lin_score hξ hξ0 hσ hX hind _ _ hZt
  convert hclt using 3 with n ω
  rw [inner_smul_left, sum_inner]
  simp only [gpdScoreLin, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_inv₀]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end ScoreLin

/-! ### Joint asymptotic normality -/

section Normality

open RealInnerProductSpace Matrix

/-- Solving the `2 × 2` linearized likelihood equations `S = -B T`. -/
lemma solve_two_by_two {B₁₁ B₁₂ B₂₂ S₁ S₂ T₁ T₂ j₁₁ j₁₂ j₂₂ : ℝ}
    (hS₁ : S₁ = -(B₁₁ * T₁ + B₁₂ * T₂)) (hS₂ : S₂ = -(B₁₂ * T₁ + B₂₂ * T₂))
    (hD : B₁₁ * B₂₂ - B₁₂ ^ 2 ≠ 0) :
    T₁ - (j₁₁ * S₁ + j₁₂ * S₂) = (-B₂₂ / (B₁₁ * B₂₂ - B₁₂ ^ 2) - j₁₁) * S₁ +
        (B₁₂ / (B₁₁ * B₂₂ - B₁₂ ^ 2) - j₁₂) * S₂ ∧
      T₂ - (j₁₂ * S₁ + j₂₂ * S₂) = (B₁₂ / (B₁₁ * B₂₂ - B₁₂ ^ 2) - j₁₂) * S₁ +
        (-B₁₁ / (B₁₁ * B₂₂ - B₁₂ ^ 2) - j₂₂) * S₂ := by
  have e₁ : -B₂₂ * S₁ + B₁₂ * S₂ = (B₁₁ * B₂₂ - B₁₂ ^ 2) * T₁ := by rw [hS₁, hS₂]; ring
  have e₂ : B₁₂ * S₁ + -B₁₁ * S₂ = (B₁₁ * B₂₂ - B₁₂ ^ 2) * T₂ := by rw [hS₁, hS₂]; ring
  constructor
  · rw [show (-B₂₂ / (B₁₁ * B₂₂ - B₁₂ ^ 2) - j₁₁) * S₁ + (B₁₂ / (B₁₁ * B₂₂ - B₁₂ ^ 2) - j₁₂) * S₂
      = (-B₂₂ * S₁ + B₁₂ * S₂) / (B₁₁ * B₂₂ - B₁₂ ^ 2) - (j₁₁ * S₁ + j₁₂ * S₂) by ring,
      e₁, mul_div_cancel_left₀ _ hD]
  · rw [show (B₁₂ / (B₁₁ * B₂₂ - B₁₂ ^ 2) - j₁₂) * S₁ + (-B₁₁ / (B₁₁ * B₂₂ - B₁₂ ^ 2) - j₂₂) * S₂
      = (B₁₂ * S₁ + -B₁₁ * S₂) / (B₁₁ * B₂₂ - B₁₂ ^ 2) - (j₁₂ * S₁ + j₂₂ * S₂) by ring,
      e₂, mul_div_cancel_left₀ _ hD]

lemma norm_euclidean_two_le (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ≤ |v 0| + |v 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_left]
  · simp only [Real.norm_eq_abs]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)]
  · positivity

variable {ξ₀ σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
  [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma tendstoInMeasure_add_zero {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure P f atTop (fun _ => 0)) (hg : TendstoInMeasure P g atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => f n ω + g n ω) atTop (fun _ => 0) := by
  have := tendstoInMeasure_comp₂ hf hg (φ := fun p => p.1 + p.2) continuous_add.continuousAt
  simpa using this

omit [IsProbabilityMeasure P] in
lemma tendstoInMeasure_abs_zero {f : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure P f atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => |f n ω|) atTop (fun _ => 0) := by
  have := tendstoInMeasure_comp hf (φ := fun r => |r|) continuous_abs.continuousAt
  simpa using this

/-- **Joint asymptotic normality of the GPD maximum likelihood estimator** for a positive shape
([Smith 1985]; [Coles, §4.3.3]). Let `X₀, X₁, …` be iid `GPD(ξ₀, σ₀)` with `ξ₀ > 0`, and let
`θ̂ₙ = (ξ̂ₙ, σ̂ₙ)` be measurable, strongly consistent estimators which almost surely, for all large
`n`, solve the likelihood equations `∑_{i<n} ∂_ξ ℓ(θ̂ₙ; Xᵢ) = 0`, `∑_{i<n} ∂_σ ℓ(θ̂ₙ; Xᵢ) = 0`.
Then

  `√n (θ̂ₙ - θ₀) ⇒ N(0, I(θ₀)⁻¹)`, `I(ξ, σ)⁻¹ = (1 + ξ) [[1 + ξ, -σ], [-σ, 2σ²]]`. -/
theorem tendstoInDistribution_gpdJointMLE (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)))
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0)
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gpdFisherInfoInv ξ₀ σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - ξ₀, (θh n ω).2 - σ₀])
      atTop W (fun _ => P) P' := by
  have hξ : -1 / 2 < ξ₀ := by linarith
  have hξ0 : ξ₀ ≠ 0 := hξ₀.ne'
  set j₁₁ := (1 + ξ₀) * (1 + ξ₀)
  set j₁₂ := (1 + ξ₀) * -σ₀
  set j₂₂ := (1 + ξ₀) * (2 * σ₀ ^ 2)
  set I₁₁ := 2 / ((1 + ξ₀) * (1 + 2 * ξ₀))
  set I₁₂ := 1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀))
  set I₂₂ := 1 / (σ₀ ^ 2 * (1 + 2 * ξ₀))
  obtain ⟨hd, hJ₁₁, hJ₁₂, hJ₂₂⟩ := gpdFisherInfo_det_adj hξ hσ₀
  set d := I₁₁ * I₂₂ - I₁₂ ^ 2
  have hJ₁₁' : I₂₂ / d = j₁₁ := hJ₁₁
  have hJ₁₂' : -I₁₂ / d = j₁₂ := hJ₁₂
  have hJ₂₂' : I₁₁ / d = j₂₂ := hJ₂₂
  -- the CLT for `I⁻¹ × score`
  have hQ : ∀ t : Fin 2 → ℝ, gpdInfoQuad ξ₀ σ₀ (t 0 * j₁₁ + t 1 * j₁₂) (t 0 * j₁₂ + t 1 * j₂₂) =
      t ⬝ᵥ gpdFisherInfoInv ξ₀ σ₀ *ᵥ t := fun t => by
    have h1ξ : 1 + ξ₀ ≠ 0 := by intro h; linarith
    have h2ξ : 1 + 2 * ξ₀ ≠ 0 := by intro h; linarith
    have h2ξ' : 1 + ξ₀ * 2 ≠ 0 := by intro h; linarith
    have := hσ₀.ne'
    simp only [gpdInfoQuad, gpdFisherInfoInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, j₁₁, j₁₂, j₂₂]
    field_simp
    ring
  have hV := tendstoInDistribution_gpdScoreLin hξ hξ0 hσ₀ hX hind j₁₁ j₁₂ j₁₂ j₂₂
    (posDef_gpdFisherInfoInv hξ hσ₀).posSemidef hQ hW
  -- the random quantities
  set S₁ : ℕ → Ω → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
    (1 * gpdScoreXi ξ₀ σ₀ (X i ω) + 0 * gpdScoreSigma ξ₀ σ₀ (X i ω))
  set S₂ : ℕ → Ω → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
    (0 * gpdScoreXi ξ₀ σ₀ (X i ω) + 1 * gpdScoreSigma ξ₀ σ₀ (X i ω))
  set B₁₁ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    segHess gpdHessXiXi ξ₀ σ₀ (θh n ω) (X i ω)
  set B₁₂ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    segHess gpdHessXiSigma ξ₀ σ₀ (θh n ω) (X i ω)
  set B₂₂ : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
    segHess gpdHessSigmaSigma ξ₀ σ₀ (θh n ω) (X i ω)
  set Dn : ℕ → Ω → ℝ := fun n ω => B₁₁ n ω * B₂₂ n ω - B₁₂ n ω ^ 2
  set M₁₁ : ℕ → Ω → ℝ := fun n ω => -B₂₂ n ω / Dn n ω - j₁₁
  set M₁₂ : ℕ → Ω → ℝ := fun n ω => B₁₂ n ω / Dn n ω - j₁₂
  set M₂₂ : ℕ → Ω → ℝ := fun n ω => -B₁₁ n ω / Dn n ω - j₂₂
  set T : ℕ → Ω → EuclideanSpace ℝ (Fin 2) :=
    fun n ω => √(n : ℝ) • !₂[(θh n ω).1 - ξ₀, (θh n ω).2 - σ₀]
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin 2) := fun n ω => (√(n : ℝ))⁻¹ •
    ∑ i ∈ Finset.range n, gpdScoreLin j₁₁ j₁₂ j₁₂ j₂₂ ξ₀ σ₀ (X i ω)
  -- measurability
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hBm : ∀ (H : ℝ → ℝ → ℝ → ℝ), (Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) →
      ∀ n : ℕ, AEMeasurable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        segHess H ξ₀ σ₀ (θh n ω) (X i ω)) P := fun H hH n => by
    have h := measurable_segHess (ξ₀ := ξ₀) (σ₀ := σ₀) hH
    have : ∀ i, AEMeasurable (fun ω => segHess H ξ₀ σ₀ (θh n ω) (X i ω)) P := fun i =>
      h.comp_aemeasurable ((hθm n).prodMk (hXm i))
    exact (Finset.aemeasurable_fun_sum _ fun i _ => this i).const_mul _
  have hB₁₁m := hBm _ measurable_gpdHessXiXi₃
  have hB₁₂m := hBm _ measurable_gpdHessXiSigma₃
  have hB₂₂m := hBm _ measurable_gpdHessSigmaSigma₃
  have hSm : ∀ (c₁ c₂ : ℝ) (n : ℕ), AEMeasurable (fun ω => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n,
      (c₁ * gpdScoreXi ξ₀ σ₀ (X i ω) + c₂ * gpdScoreSigma ξ₀ σ₀ (X i ω))) P := fun c₁ c₂ n => by
    have := measurable_gpdScoreXi ξ₀ σ₀; have := measurable_gpdScoreSigma ξ₀ σ₀
    have : ∀ i, AEMeasurable (fun ω => c₁ * gpdScoreXi ξ₀ σ₀ (X i ω) +
        c₂ * gpdScoreSigma ξ₀ σ₀ (X i ω)) P := fun i => by
      have := hXm i; fun_prop
    exact (Finset.aemeasurable_fun_sum _ fun i _ => this i).const_mul _
  have hMm : ∀ (F : ℝ → ℝ → ℝ → ℝ), Measurable (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2) →
      ∀ n, AEMeasurable (fun ω => F (B₁₁ n ω) (B₁₂ n ω) (B₂₂ n ω)) P := fun F hF n =>
    hF.comp_aemeasurable ((hB₁₁m n).prodMk ((hB₁₂m n).prodMk (hB₂₂m n)))
  have hM₁₁m : ∀ n, AEMeasurable (M₁₁ n) P :=
    hMm (fun a b c => -c / (a * c - b ^ 2) - j₁₁) (by fun_prop)
  have hM₁₂m : ∀ n, AEMeasurable (M₁₂ n) P :=
    hMm (fun a b c => b / (a * c - b ^ 2) - j₁₂) (by fun_prop)
  have hM₂₂m : ∀ n, AEMeasurable (M₂₂ n) P :=
    hMm (fun a b c => -a / (a * c - b ^ 2) - j₂₂) (by fun_prop)
  have hTm : ∀ n, AEMeasurable (T n) P := fun n => by
    have hm : Measurable fun θ : ℝ × ℝ => (!₂[θ.1 - ξ₀, θ.2 - σ₀] : EuclideanSpace ℝ (Fin 2)) :=
      (WithLp.measurable_toLp 2 _).comp (f := fun θ : ℝ × ℝ => ![θ.1 - ξ₀, θ.2 - σ₀])
        (measurable_pi_iff.2 fun i => by fin_cases i <;> simp <;> fun_prop)
    exact (hm.comp_aemeasurable (hθm n)).const_smul (√(n : ℝ))
  have hVm : ∀ n, AEMeasurable (V n) P := hV.forall_aemeasurable
  -- the strong laws
  have hpos := ae_forall_pos_of_gpd hσ₀ hX
  have hL₀m : Measurable fun x : ℝ => log (1 + ξ₀ * x / σ₀) := by fun_prop
  have hL₀i : Integrable (fun x : ℝ => log (1 + ξ₀ * x / σ₀)) (gpdMeasure ξ₀ σ₀) :=
    integrable_gpdMeasure_of_poly hξ hL₀m 0 ξ₀ 0 0 0 0 fun t => by
      rw [log_one_add_mul_gpdTransform hσ₀ hξ0]; ring
  have hsL := ae_tendsto_avg_comp hX hind hL₀m hL₀i
  have hs₁₁ := ae_tendsto_avg_comp hX hind (measurable_gpdHessXiXi ξ₀ σ₀)
    (integrable_gpdHessXiXi hσ₀ hξ0 hξ)
  have hs₁₂ := ae_tendsto_avg_comp hX hind (measurable_gpdHessXiSigma ξ₀ σ₀)
    (integrable_gpdHessXiSigma hσ₀ hξ0 hξ)
  have hs₂₂ := ae_tendsto_avg_comp hX hind (measurable_gpdHessSigmaSigma ξ₀ σ₀)
    (integrable_gpdHessSigmaSigma hσ₀ hξ0 hξ)
  rw [integral_gpdHessXiXi hσ₀ hξ0 hξ] at hs₁₁
  rw [integral_gpdHessXiSigma hσ₀ hξ0 hξ] at hs₁₂
  rw [integral_gpdHessSigmaSigma hσ₀ hξ0 hξ] at hs₂₂
  -- the Lipschitz control
  obtain ⟨K, hK0, hK⟩ := exists_gpdHess_lipschitz hξ₀ hσ₀
  have hexp := fun {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) =>
    gpdScore_sub_eq_segHess hξ₀ hσ₀ hK0 hK hθ hx
  -- almost sure convergence of the averaged Hessians
  have hB : ∀ᵐ ω ∂P, Tendsto (fun n => B₁₁ n ω) atTop (𝓝 (-I₁₁)) ∧
      Tendsto (fun n => B₁₂ n ω) atTop (𝓝 (-I₁₂)) ∧
      Tendsto (fun n => B₂₂ n ω) atTop (𝓝 (-I₂₂)) := by
    filter_upwards [hpos, hcons, hsL, hs₁₁, hs₁₂, hs₂₂] with ω hω hc hl h₁₁ h₁₂ h₂₂
    have hx : ∀ i, 0 ≤ X i ω := fun i => (hω i).le
    exact ⟨tendsto_avg_segHess hξ₀ hσ₀ (fun θ hθ x hx => (hexp hθ hx).2.2.1) hx hc h₁₁ hl,
      tendsto_avg_segHess hξ₀ hσ₀ (fun θ hθ x hx => (hexp hθ hx).2.2.2.1) hx hc h₁₂ hl,
      tendsto_avg_segHess hξ₀ hσ₀ (fun θ hθ x hx => (hexp hθ hx).2.2.2.2) hx hc h₂₂ hl⟩
  have hDlim : ∀ᵐ ω ∂P, Tendsto (fun n => Dn n ω) atTop (𝓝 d) := by
    filter_upwards [hB] with ω ⟨h₁, h₂, h₃⟩
    have := (h₁.mul h₃).sub (h₂.pow 2)
    simpa [d, neg_mul_neg] using this
  have hMlim : ∀ᵐ ω ∂P, Tendsto (fun n => M₁₁ n ω) atTop (𝓝 0) ∧
      Tendsto (fun n => M₁₂ n ω) atTop (𝓝 0) ∧ Tendsto (fun n => M₂₂ n ω) atTop (𝓝 0) := by
    filter_upwards [hB, hDlim] with ω ⟨h₁, h₂, h₃⟩ hD
    refine ⟨?_, ?_, ?_⟩
    · have := (h₃.neg.div hD hd.ne').sub_const j₁₁
      rwa [neg_neg, hJ₁₁', sub_self] at this
    · have := (h₂.div hD hd.ne').sub_const j₁₂
      rwa [hJ₁₂', sub_self] at this
    · have := (h₁.neg.div hD hd.ne').sub_const j₂₂
      rwa [neg_neg, hJ₂₂', sub_self] at this
  have hM₁₁ : TendstoInMeasure P M₁₁ atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hM₁₁m n).aestronglyMeasurable)
      (hMlim.mono fun ω h => h.1)
  have hM₁₂ : TendstoInMeasure P M₁₂ atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hM₁₂m n).aestronglyMeasurable)
      (hMlim.mono fun ω h => h.2.1)
  have hM₂₂ : TendstoInMeasure P M₂₂ atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hM₂₂m n).aestronglyMeasurable)
      (hMlim.mono fun ω h => h.2.2)
  have hS₁b := isBoundedInProbability_lin_score hξ hξ0 hσ₀ hX hind 1 0
  have hS₂b := isBoundedInProbability_lin_score hξ hξ0 hσ₀ hX hind 0 1
  -- the dominating sequence
  set G : ℕ → Ω → ℝ := fun n ω => |M₁₁ n ω * S₁ n ω| + |M₁₂ n ω * S₂ n ω| +
    (|M₁₂ n ω * S₁ n ω| + |M₂₂ n ω * S₂ n ω|)
  have hG : TendstoInMeasure P G atTop (fun _ => 0) := by
    have a₁ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability'
      hS₁b hM₁₁)
    have a₂ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability'
      hS₂b hM₁₂)
    have a₃ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability'
      hS₁b hM₁₂)
    have a₄ := tendstoInMeasure_abs_zero (tendstoInMeasure_mul_zero_of_isBoundedInProbability'
      hS₂b hM₂₂)
    exact tendstoInMeasure_add_zero (tendstoInMeasure_add_zero a₁ a₂)
      (tendstoInMeasure_add_zero a₃ a₄)
  -- the eventual domination
  have hdom : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, |‖T n ω - V n ω‖| ≤ G n ω := by
    filter_upwards [hpos, hcons, hroot, hDlim] with ω hω hc hr hD
    filter_upwards [hc.eventually (gpdNbhd_mem_nhds hξ₀ hσ₀), hr,
      hD.eventually (isOpen_ne.mem_nhds hd.ne'), eventually_gt_atTop 0] with n hn hrn hDn hn0
    have hx : ∀ i, 0 ≤ X i ω := fun i => (hω i).le
    set a := (θh n ω).1 - ξ₀
    set b := (θh n ω).2 - σ₀
    have hsq : (√(n : ℝ))⁻¹ * n = √(n : ℝ) := by
      have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
      field_simp
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
    -- the linearized likelihood equations
    have eξ : ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (X i ω) =
        -(a * (n * B₁₁ n ω) + b * (n * B₁₂ n ω)) := by
      have h := Finset.sum_congr rfl fun i (_ : i ∈ Finset.range n) => (hexp hn (hx i)).1
      rw [Finset.sum_sub_distrib, hrn.1] at h
      simp only [B₁₁, B₁₂, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← h]
      ring
    have eσ : ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (X i ω) =
        -(a * (n * B₁₂ n ω) + b * (n * B₂₂ n ω)) := by
      have h := Finset.sum_congr rfl fun i (_ : i ∈ Finset.range n) => (hexp hn (hx i)).2.1
      rw [Finset.sum_sub_distrib, hrn.2] at h
      simp only [B₁₂, B₂₂, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← h]
      ring
    have hS₁e : S₁ n ω = -(B₁₁ n ω * (√(n : ℝ) * a) + B₁₂ n ω * (√(n : ℝ) * b)) := by
      simp only [S₁, one_mul, zero_mul, add_zero]
      rw [eξ, show (√(n : ℝ))⁻¹ * -(a * (n * B₁₁ n ω) + b * (n * B₁₂ n ω)) =
        -(((√(n : ℝ))⁻¹ * n) * a * B₁₁ n ω + ((√(n : ℝ))⁻¹ * n) * b * B₁₂ n ω) by ring, hsq]
      ring
    have hS₂e : S₂ n ω = -(B₁₂ n ω * (√(n : ℝ) * a) + B₂₂ n ω * (√(n : ℝ) * b)) := by
      simp only [S₂, one_mul, zero_mul, zero_add]
      rw [eσ, show (√(n : ℝ))⁻¹ * -(a * (n * B₁₂ n ω) + b * (n * B₂₂ n ω)) =
        -(((√(n : ℝ))⁻¹ * n) * a * B₁₂ n ω + ((√(n : ℝ))⁻¹ * n) * b * B₂₂ n ω) by ring, hsq]
      ring
    obtain ⟨h₁, h₂⟩ := solve_two_by_two (j₁₁ := j₁₁) (j₁₂ := j₁₂) (j₂₂ := j₂₂) hS₁e hS₂e hDn
    -- the coordinates of `T - V`
    have hV0 : V n ω 0 = j₁₁ * S₁ n ω + j₁₂ * S₂ n ω := by
      simp only [V, S₁, S₂, gpdScoreLin, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        smul_eq_mul, Matrix.cons_val_zero, one_mul, zero_mul, add_zero, zero_add,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have hV1 : V n ω 1 = j₁₂ * S₁ n ω + j₂₂ * S₂ n ω := by
      simp only [V, S₁, S₂, gpdScoreLin, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
        smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero, one_mul, zero_mul, add_zero,
        zero_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    have hT0 : T n ω 0 = √(n : ℝ) * a := by simp [T, a]
    have hT1 : T n ω 1 = √(n : ℝ) * b := by simp [T, b]
    rw [abs_norm]
    refine (norm_euclidean_two_le _).trans ?_
    simp only [PiLp.sub_apply, hT0, hT1, hV0, hV1]
    rw [h₁, h₂]
    simp only [G, M₁₁, M₁₂, M₂₂, Dn]
    exact add_le_add (abs_add_le _ _) (abs_add_le _ _)
  have hdiff : TendstoInMeasure P (T - V) atTop 0 := by
    have hr := tendstoInMeasure_zero_of_ae_eventually_abs_le
      (f := fun n ω => ‖T n ω - V n ω‖)
      (fun n => ((hTm n).sub (hVm n)).norm.aestronglyMeasurable)
      (fun n => by
        have := hM₁₁m n; have := hM₁₂m n; have := hM₂₂m n
        have := hSm 1 0 n; have := hSm 0 1 n
        exact (by fun_prop : AEMeasurable (G n) P).aestronglyMeasurable) hdom hG
    rw [tendstoInMeasure_iff_norm] at hr ⊢
    intro ε hε
    simpa using hr ε hε
  exact tendstoInDistribution_of_tendstoInMeasure_sub T W hV hdiff hTm

end Normality

/-! ### The maximum likelihood estimator on a compact parameter set -/

section MLE

lemma ereal_coe_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

/-- For a positive shape and nonnegative data the extended-real log-likelihood is finite. -/
lemma gpdLogLikE_eq_coe {ξ σ : ℝ} (hξ : 0 < ξ) (hσ : 0 < σ) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i) :
    gpdLogLikE ξ σ x = ((∑ i, log (gpdDensity ξ σ (x i)) : ℝ) : EReal) := by
  rw [gpdLogLikE, ereal_coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : 0 < 1 + ξ * x i / σ := by have := hx i; positivity
  unfold gpdLogDensityE
  rw [ite_eq_left (show _ ∧ _ from ⟨hx i, this⟩)]

/-- **The likelihood equations at an interior maximizer.** If `θ` maximizes the log-likelihood
over `K`, lies in the interior of `K` and has positive coordinates, and the data are
nonnegative, then both components of the score vanish at `θ`. -/
theorem score_eq_zero_of_isMaxOn {K : Set (ℝ × ℝ)} {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i) {θ : ℝ × ℝ} (hθK : θ ∈ interior K) (hθ₁ : 0 < θ.1) (hθ₂ : 0 < θ.2)
    (hmax : IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K θ) :
    ∑ i, gpdScoreXi θ.1 θ.2 (x i) = 0 ∧ ∑ i, gpdScoreSigma θ.1 θ.2 (x i) = 0 := by
  have hint := isOpen_interior.mem_nhds hθK
  have hle : ∀ p ∈ interior K, 0 < p.1 → 0 < p.2 →
      ∑ i, log (gpdDensity p.1 p.2 (x i)) ≤ ∑ i, log (gpdDensity θ.1 θ.2 (x i)) := by
    intro p hp h1 h2
    have := hmax (interior_subset hp)
    simp only [mem_ofPred_eq] at this
    rw [gpdLogLikE_eq_coe h1 h2 hx, gpdLogLikE_eq_coe hθ₁ hθ₂ hx] at this
    exact EReal.coe_le_coe_iff.1 this
  constructor
  · have hd : HasDerivAt (fun ξ => ∑ i, log (gpdDensity ξ θ.2 (x i)))
        (∑ i, gpdScoreXi θ.1 θ.2 (x i)) θ.1 := by
      have := HasDerivAt.sum (u := Finset.univ) fun i _ =>
        hasDerivAt_log_gpdDensity_xi hθ₂ hθ₁.ne' (hx i) (by have := hx i; positivity)
      convert this using 1
      funext ξ; simp
    have hloc : IsLocalMax (fun ξ => ∑ i, log (gpdDensity ξ θ.2 (x i))) θ.1 := by
      have h1 : ∀ᶠ ξ in 𝓝 θ.1, (ξ, θ.2) ∈ interior K :=
        (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
          (by simpa using hint)
      filter_upwards [h1, lt_mem_nhds hθ₁] with ξ h1 h2
      exact hle (ξ, θ.2) h1 h2 hθ₂
    exact hloc.hasDerivAt_eq_zero hd
  · have hd : HasDerivAt (fun σ => ∑ i, log (gpdDensity θ.1 σ (x i)))
        (∑ i, gpdScoreSigma θ.1 θ.2 (x i)) θ.2 := by
      have := HasDerivAt.sum (u := Finset.univ) fun i _ =>
        hasDerivAt_log_gpdDensity_sigma hθ₂ hθ₁.ne' (hx i) (by have := hx i; positivity)
      convert this using 1
      funext σ; simp
    have hloc : IsLocalMax (fun σ => ∑ i, log (gpdDensity θ.1 σ (x i))) θ.2 := by
      have h1 : ∀ᶠ σ in 𝓝 θ.2, (θ.1, σ) ∈ interior K :=
        (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
          (by simpa using hint)
      filter_upwards [h1, lt_mem_nhds hθ₂] with σ h1 h2
      exact hle (θ.1, σ) h1 hθ₁ h2
    exact hloc.hasDerivAt_eq_zero hd

variable {ξ₀ σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'}
  [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ}

/-- **Asymptotic normality of the joint GPD maximum likelihood estimator, `ξ₀ > 0`**
([Smith 1985]; [Coles, §4.3.3]). Let `K ⊂ {ξ > -1, σ > 0}` be compact with the true parameter
`θ₀ = (ξ₀, σ₀)`, `ξ₀ > 0`, in its interior, let `X₀, X₁, …` be iid `GPD(θ₀)`, and let `θ̂ₙ` be
measurable maximizers over `K` of the log-likelihood of `X₀, …, X_{n-1}` (which exist by
`exists_isMaxOn_gpdLogLikE`). Then `√n (θ̂ₙ - θ₀) ⇒ N(0, I(θ₀)⁻¹)` with
`I(ξ, σ)⁻¹ = (1 + ξ) [[1 + ξ, -σ], [-σ, 2σ²]]`. -/
theorem tendstoInDistribution_gpdMLE {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2) (hθ₀ : (ξ₀, σ₀) ∈ interior K)
    (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 (fun i : Fin n => X i ω)) K
      (θh n ω))
    {W : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hW : HasLaw W (multivariateGaussian 0 (gpdFisherInfoInv ξ₀ σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - ξ₀, (θh n ω).2 - σ₀])
      atTop W (fun _ => P) P' := by
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)) := by
    filter_upwards [ae_tendsto_gpdMLE' hK hKS (interior_subset hθ₀) hX hind] with ω hω
    refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
      (Eventually.of_forall fun n => ?_)
    have := hmax n ω (interior_subset hθ₀)
    simp only [mem_ofPred_eq] at this
    simpa using this
  refine tendstoInDistribution_gpdJointMLE hξ₀ hσ₀ hX hind hθm hcons ?_ hW
  filter_upwards [ae_forall_pos_of_gpd hσ₀ hX, hcons] with ω hω hc
  filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀),
    hc.eventually (gpdNbhd_mem_nhds hξ₀ hσ₀)] with n h1 h2
  obtain ⟨h3, -, h4, -⟩ := pos_of_mem_gpdNbhd h2
  have := score_eq_zero_of_isMaxOn (x := fun i : Fin n => X i ω) (fun i => (hω i).le) h1
    (by linarith) (by linarith) (hmax n ω)
  rw [Fin.sum_univ_eq_sum_range (fun i => gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω)) n,
    Fin.sum_univ_eq_sum_range (fun i => gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω)) n] at this
  exact this

end MLE

end ExtremeValueTheory
