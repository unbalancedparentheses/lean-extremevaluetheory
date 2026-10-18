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

end ExtremeValueTheory
