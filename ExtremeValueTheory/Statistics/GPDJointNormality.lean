/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDFisherInformation

/-!
# Joint asymptotic normality of the GPD maximum likelihood estimator, `ξ₀ > 0`

WIP.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### Lipschitz control of the Hessian near the true parameter -/

section Lipschitz

variable {ξ₀ σ₀ : ℝ}

/-- The closed neighbourhood `|ξ - ξ₀| ≤ ξ₀/8`, `|σ - σ₀| ≤ σ₀/8` of the true parameter, on
which the Hessian of the log-density is Lipschitz in the parameter, uniformly in the data. -/
def gpdNbhd (ξ₀ σ₀ : ℝ) : Set (ℝ × ℝ) :=
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
def gpdBox (ξ₀ σ₀ : ℝ) : Set (ℝ × ℝ × ℝ) :=
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

end Expansion

end ExtremeValueTheory
