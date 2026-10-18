/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDJointNormality

/-!
# Joint asymptotic normality of the GPD maximum likelihood estimator, `-1/2 < ξ₀ < 0`

TODO
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### A neighbourhood of a negative shape -/

section Nbhd

variable {ξ₀ σ₀ : ℝ}

/-- The closed neighbourhood `|ξ - ξ₀| ≤ |ξ₀|/8`, `|σ - σ₀| ≤ σ₀/8` of `(ξ₀, σ₀)`, `ξ₀ < 0`. -/
def gpdNbhdNeg (ξ₀ σ₀ : ℝ) : Set (ℝ × ℝ) :=
  Icc (ξ₀ + ξ₀ / 8) (ξ₀ - ξ₀ / 8) ×ˢ Icc (σ₀ - σ₀ / 8) (σ₀ + σ₀ / 8)

lemma convex_gpdNbhdNeg : Convex ℝ (gpdNbhdNeg ξ₀ σ₀) := (convex_Icc _ _).prod (convex_Icc _ _)

lemma isCompact_gpdNbhdNeg : IsCompact (gpdNbhdNeg ξ₀ σ₀) := isCompact_Icc.prod isCompact_Icc

lemma bounds_of_mem_gpdNbhdNeg {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) :
    9 * ξ₀ / 8 ≤ θ.1 ∧ θ.1 ≤ 7 * ξ₀ / 8 ∧ 7 * σ₀ / 8 ≤ θ.2 ∧ θ.2 ≤ 9 * σ₀ / 8 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hθ
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma mem_gpdNbhdNeg_of_gpdDist_le {θ : ℝ × ℝ}
    (hθ : gpdDist ξ₀ σ₀ θ ≤ min (-ξ₀ / 8) (σ₀ / 8)) : θ ∈ gpdNbhdNeg ξ₀ σ₀ := by
  unfold gpdDist at hθ
  have h1 := abs_nonneg (θ.1 - ξ₀)
  have h2 := abs_nonneg (θ.2 - σ₀)
  have ha : |θ.1 - ξ₀| ≤ -ξ₀ / 8 := by linarith [min_le_left (-ξ₀ / 8) (σ₀ / 8)]
  have hb : |θ.2 - σ₀| ≤ σ₀ / 8 := by linarith [min_le_right (-ξ₀ / 8) (σ₀ / 8)]
  rw [abs_le] at ha hb
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

variable (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
include hξ₀' hσ₀

lemma mem_gpdNbhdNeg_self : (ξ₀, σ₀) ∈ gpdNbhdNeg ξ₀ σ₀ :=
  ⟨⟨by simp; linarith, by simp; linarith⟩, by simp; linarith, by simp; linarith⟩

lemma gpdNbhdNeg_mem_nhds : gpdNbhdNeg ξ₀ σ₀ ∈ 𝓝 (ξ₀, σ₀) :=
  prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
    (Icc_mem_nhds (by linarith) (by linarith))

/-- On the neighbourhood: `-9/16 < ξ < 0`, `σ > 0`. -/
lemma param_bounds_of_mem_gpdNbhdNeg (hξ₀ : -1 / 2 < ξ₀) {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) :
    -9 / 16 < θ.1 ∧ θ.1 < 0 ∧ 0 < θ.2 := by
  obtain ⟨h1, h2, h3, -⟩ := bounds_of_mem_gpdNbhdNeg hθ
  exact ⟨by linarith, by linarith, by linarith⟩

lemma segment_mem_gpdNbhdNeg {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀)) ∈ gpdNbhdNeg ξ₀ σ₀ := by
  have h := convex_gpdNbhdNeg (mem_gpdNbhdNeg_self hξ₀' hσ₀) hθ (sub_nonneg.2 hs.2) hs.1
    (by ring)
  convert h using 1
  ext <;> simp <;> ring

end Nbhd

/-! ### Pointwise bounds on the Hessian for a negative shape -/

section Pointwise

variable {ξ σ x : ℝ}

/-- **One-sided bound on the Hessian.** For `-1 < ξ < 0` and `x` in the support, the Hessian
quadratic form is bounded above:
`t₁² ∂²_ξ ℓ + 2 t₁ t₂ ∂_ξ∂_σ ℓ + t₂² ∂²_σ ℓ ≤ β²/(4a) + s²` with `s = t₂/σ`,
`p = t₁ - ξ s`, `a = -(1 + ξ)/ξ > 0`, `β = 2p/ξ² + (4/ξ + 2) s`. The terms which blow up at
the endpoint of the support, `-a w² p²` and `(2/ξ³) log(1 + ξ x/σ) t₁²`, have the good sign. -/
lemma gpdHess_quad_le (hξ1 : -1 < ξ) (hξ0 : ξ < 0) (hσ : 0 < σ) (hx : 0 ≤ x)
    (hu : 0 < σ + ξ * x) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * gpdHessXiXi ξ σ x + 2 * t₁ * t₂ * gpdHessXiSigma ξ σ x +
        t₂ ^ 2 * gpdHessSigmaSigma ξ σ x ≤
      (2 / ξ ^ 2 * (t₁ - ξ * (t₂ / σ)) + (4 / ξ + 2) * (t₂ / σ)) ^ 2 /
          (4 * (-(1 + ξ) / ξ)) + (t₂ / σ) ^ 2 := by
  set w := x / (σ + ξ * x) with hw
  set L := log (1 + ξ * x / σ) with hL
  set s := t₂ / σ with hs
  set p := t₁ - ξ * s with hp
  set a := -(1 + ξ) / ξ with ha
  set β := 2 / ξ ^ 2 * p + (4 / ξ + 2) * s with hβ
  have ha0 : 0 < a := div_pos_of_neg_of_neg (by linarith) hξ0
  have hL0 : L ≤ 0 := by
    refine log_nonpos (one_add_mul_div_pos hσ hu).le ?_
    have : ξ * x / σ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      hξ0.le hx) hσ.le
    linarith
  have hξ3 : ξ ^ 3 < 0 := by have := pow_pos (neg_pos.2 hξ0) 3; nlinarith [this]
  have ht₁ : t₁ = p + ξ * s := by simp only [hp]; ring
  have ht₂ : t₂ = σ * s := by simp only [hs]; field_simp
  -- the exact identity
  have key : t₁ ^ 2 * gpdHessXiXi ξ σ x + 2 * t₁ * t₂ * gpdHessXiSigma ξ σ x +
      t₂ ^ 2 * gpdHessSigmaSigma ξ σ x =
      -2 * L / ξ ^ 3 * t₁ ^ 2 + (-a * (w * p) ^ 2 + β * (w * p)) + s ^ 2 := by
    unfold gpdHessXiXi gpdHessXiSigma gpdHessSigmaSigma
    rw [← hw, ← hL]
    simp only [hβ, ha]
    rw [ht₁, ht₂]
    have := hσ.ne'
    have := hξ0.ne
    field_simp
    ring
  rw [key]
  have h1 : -2 * L / ξ ^ 3 * t₁ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonneg_of_nonpos (by linarith) hξ3.le)
      (sq_nonneg _)
  have h2 : -a * (w * p) ^ 2 + β * (w * p) ≤ β ^ 2 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * (w * p) - β)]
  linarith

lemma abs_lin_le {c₀ c₁ c₂ c₃ L w G : ℝ} (hw : 0 ≤ w)
    (hG : |c₀| + |c₁| + |c₂| + |c₃| ≤ G) :
    |c₀ * L + c₁ * w + c₂ * w ^ 2 + c₃| ≤ G * (|L| + w + w ^ 2 + 1) := by
  have h1 : |c₀ * L + c₁ * w + c₂ * w ^ 2 + c₃| ≤ |c₀| * |L| + |c₁| * w + |c₂| * w ^ 2 + |c₃| := by
    have := abs_add_le (c₀ * L + c₁ * w + c₂ * w ^ 2) c₃
    have := abs_add_le (c₀ * L + c₁ * w) (c₂ * w ^ 2)
    have := abs_add_le (c₀ * L) (c₁ * w)
    simp only [abs_mul, abs_of_nonneg hw, abs_of_nonneg (sq_nonneg w)] at *
    linarith
  have hL := abs_nonneg L
  have hw2 := sq_nonneg w
  have : |c₀| * |L| + |c₁| * w + |c₂| * w ^ 2 + |c₃| ≤
      (|c₀| + |c₁| + |c₂| + |c₃|) * (|L| + w + w ^ 2 + 1) := by
    nlinarith [abs_nonneg c₀, abs_nonneg c₁, abs_nonneg c₂, abs_nonneg c₃]
  have h0 : 0 ≤ |L| + w + w ^ 2 + 1 := by positivity
  nlinarith

/-- The coefficient sum controlling the Hessian entries as polynomials in `log(1 + ξx/σ)` and
`w = x/(σ + ξx)`. -/
noncomputable def gpdHessCoef (θ : ℝ × ℝ) : ℝ :=
  |-2 / θ.1 ^ 3| + |2 / θ.1 ^ 2| + |1 / θ.1 + 1| + |1 / θ.2| + |(1 + θ.1) / θ.2| +
    |1 / θ.2 ^ 2| + |2 * (1 + θ.1) / θ.2 ^ 2| + |θ.1 * (1 + θ.1) / θ.2 ^ 2|

/-- The coefficient of the one-sided bound of the Hessian quadratic form. -/
noncomputable def gpdQuadCoef (θ : ℝ × ℝ) : ℝ :=
  16 * (1 / (4 * (-(1 + θ.1) / θ.1))) / θ.1 ^ 4 +
    ((1 / (4 * (-(1 + θ.1) / θ.1))) * (16 / θ.1 ^ 2 + 2 * (4 / θ.1 + 2) ^ 2) + 1) / θ.2 ^ 2

lemma gpdHess_quad_le_coef (hξ1 : -1 < ξ) (hξ0 : ξ < 0) (hσ : 0 < σ) (hx : 0 ≤ x)
    (hu : 0 < σ + ξ * x) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * gpdHessXiXi ξ σ x + 2 * t₁ * t₂ * gpdHessXiSigma ξ σ x +
        t₂ ^ 2 * gpdHessSigmaSigma ξ σ x ≤ gpdQuadCoef (ξ, σ) * (t₁ ^ 2 + t₂ ^ 2) := by
  refine (gpdHess_quad_le hξ1 hξ0 hσ hx hu t₁ t₂).trans ?_
  set s := t₂ / σ with hs
  set p := t₁ - ξ * s with hp
  set u := 1 / (4 * (-(1 + ξ) / ξ)) with hu'
  have hu0 : 0 < u := by
    have : 0 < -(1 + ξ) / ξ := div_pos_of_neg_of_neg (by linarith) hξ0
    exact one_div_pos.2 (by linarith)
  set E := 16 / ξ ^ 2 + 2 * (4 / ξ + 2) ^ 2 with hE
  have hξ2 : 0 < ξ ^ 2 := by have := hξ0.ne; positivity
  have hp2 : p ^ 2 ≤ 2 * t₁ ^ 2 + 2 * ξ ^ 2 * s ^ 2 := by
    simp only [hp]; nlinarith [sq_nonneg (t₁ + ξ * s)]
  have hβ : (2 / ξ ^ 2 * p + (4 / ξ + 2) * s) ^ 2 ≤ 16 / ξ ^ 4 * t₁ ^ 2 + E * s ^ 2 := by
    have h1 : (2 / ξ ^ 2 * p + (4 / ξ + 2) * s) ^ 2 ≤
        2 * (2 / ξ ^ 2 * p) ^ 2 + 2 * ((4 / ξ + 2) * s) ^ 2 := by
      nlinarith [sq_nonneg (2 / ξ ^ 2 * p - (4 / ξ + 2) * s)]
    have h2 : 2 * (2 / ξ ^ 2 * p) ^ 2 = 8 / ξ ^ 4 * p ^ 2 := by field_simp; ring
    have h3 : 8 / ξ ^ 4 * p ^ 2 ≤ 8 / ξ ^ 4 * (2 * t₁ ^ 2 + 2 * ξ ^ 2 * s ^ 2) := by gcongr
    have h4 : 8 / ξ ^ 4 * (2 * t₁ ^ 2 + 2 * ξ ^ 2 * s ^ 2) =
        16 / ξ ^ 4 * t₁ ^ 2 + 16 / ξ ^ 2 * s ^ 2 := by field_simp; ring
    simp only [hE]
    nlinarith
  have hdiv : (2 / ξ ^ 2 * p + (4 / ξ + 2) * s) ^ 2 / (4 * (-(1 + ξ) / ξ)) =
      u * (2 / ξ ^ 2 * p + (4 / ξ + 2) * s) ^ 2 := by simp only [hu']; ring
  rw [hdiv]
  have hs2 : s ^ 2 = t₂ ^ 2 / σ ^ 2 := by simp only [hs]; ring
  have hE0 : 0 ≤ E := by positivity
  have hmain : u * (2 / ξ ^ 2 * p + (4 / ξ + 2) * s) ^ 2 + s ^ 2 ≤
      16 * u / ξ ^ 4 * t₁ ^ 2 + (u * E + 1) / σ ^ 2 * t₂ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hβ hu0.le
    have e : u * (16 / ξ ^ 4 * t₁ ^ 2 + E * s ^ 2) + s ^ 2 =
        16 * u / ξ ^ 4 * t₁ ^ 2 + (u * E + 1) / σ ^ 2 * t₂ ^ 2 := by
      rw [hs2]; field_simp; ring
    linarith
  refine hmain.trans ?_
  unfold gpdQuadCoef
  simp only
  rw [← hu', ← hE]
  have a1 : 0 ≤ 16 * u / ξ ^ 4 := by positivity
  have a2 : 0 ≤ (u * E + 1) / σ ^ 2 := by positivity
  have e : 16 * u / ξ ^ 4 = 16 * u / ξ ^ 4 := rfl
  nlinarith [sq_nonneg t₁, sq_nonneg t₂]

/-- The three Hessian entries as polynomials in `L = log(1 + ξx/σ)` and `w`. -/
lemma abs_gpdHess_le (hx : 0 ≤ x) (hu : 0 < σ + ξ * x) :
    |gpdHessXiXi ξ σ x| ≤ gpdHessCoef (ξ, σ) * (|log (1 + ξ * x / σ)| + x / (σ + ξ * x) +
        (x / (σ + ξ * x)) ^ 2 + 1) ∧
    |gpdHessXiSigma ξ σ x| ≤ gpdHessCoef (ξ, σ) * (|log (1 + ξ * x / σ)| + x / (σ + ξ * x) +
        (x / (σ + ξ * x)) ^ 2 + 1) ∧
    |gpdHessSigmaSigma ξ σ x| ≤ gpdHessCoef (ξ, σ) * (|log (1 + ξ * x / σ)| + x / (σ + ξ * x) +
        (x / (σ + ξ * x)) ^ 2 + 1) := by
  have hw : 0 ≤ x / (σ + ξ * x) := div_nonneg hx hu.le
  have hc := fun a : ℝ => abs_nonneg a
  unfold gpdHessCoef
  simp only
  refine ⟨?_, ?_, ?_⟩
  · have e : gpdHessXiXi ξ σ x = (-2 / ξ ^ 3) * log (1 + ξ * x / σ) +
        (2 / ξ ^ 2) * (x / (σ + ξ * x)) + (1 / ξ + 1) * (x / (σ + ξ * x)) ^ 2 + 0 := by
      unfold gpdHessXiXi; ring
    rw [e]
    refine abs_lin_le hw ?_
    simp only [abs_zero]
    nlinarith [hc ((1 + ξ) / σ), hc (1 / σ), hc (1 / σ ^ 2), hc (2 * (1 + ξ) / σ ^ 2),
      hc (ξ * (1 + ξ) / σ ^ 2)]
  · have e : gpdHessXiSigma ξ σ x = 0 * log (1 + ξ * x / σ) +
        (1 / σ) * (x / (σ + ξ * x)) + (-((1 + ξ) / σ)) * (x / (σ + ξ * x)) ^ 2 + 0 := by
      unfold gpdHessXiSigma; ring
    rw [e]
    refine abs_lin_le hw ?_
    simp only [abs_zero, abs_neg]
    nlinarith [hc (-2 / ξ ^ 3), hc (2 / ξ ^ 2), hc (1 / ξ + 1), hc (1 / σ ^ 2),
      hc (2 * (1 + ξ) / σ ^ 2), hc (ξ * (1 + ξ) / σ ^ 2)]
  · have e : gpdHessSigmaSigma ξ σ x = 0 * log (1 + ξ * x / σ) +
        (-(2 * (1 + ξ) / σ ^ 2)) * (x / (σ + ξ * x)) +
        (ξ * (1 + ξ) / σ ^ 2) * (x / (σ + ξ * x)) ^ 2 + 1 / σ ^ 2 := by
      unfold gpdHessSigmaSigma; ring
    rw [e]
    refine abs_lin_le hw ?_
    simp only [abs_zero, abs_neg]
    nlinarith [hc (-2 / ξ ^ 3), hc (2 / ξ ^ 2), hc (1 / ξ + 1), hc (1 / σ),
      hc ((1 + ξ) / σ)]

lemma continuousAt_gpdHessXiXi₃ {q : ℝ × ℝ × ℝ} (h1 : q.1 ≠ 0) (h2 : 0 < q.2.1)
    (h3 : 0 < q.2.1 + q.1 * q.2.2) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ => gpdHessXiXi q.1 q.2.1 q.2.2) q := by
  have h4 := (one_add_mul_div_pos h2 h3).ne'
  have h2' := h2.ne'
  have h3' := h3.ne'
  have h5 : q.1 ^ 3 ≠ 0 := pow_ne_zero 3 h1
  have h6 : q.1 ^ 2 ≠ 0 := pow_ne_zero 2 h1
  unfold gpdHessXiXi
  fun_prop (disch := assumption)

lemma continuousAt_gpdHessXiSigma₃ {q : ℝ × ℝ × ℝ} (h2 : 0 < q.2.1)
    (h3 : 0 < q.2.1 + q.1 * q.2.2) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ => gpdHessXiSigma q.1 q.2.1 q.2.2) q := by
  have h2' := h2.ne'
  have h3' := h3.ne'
  unfold gpdHessXiSigma
  fun_prop (disch := assumption)

lemma continuousAt_gpdHessSigmaSigma₃ {q : ℝ × ℝ × ℝ} (h2 : 0 < q.2.1)
    (h3 : 0 < q.2.1 + q.1 * q.2.2) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ => gpdHessSigmaSigma q.1 q.2.1 q.2.2) q := by
  have h2' := h2.ne'
  have h3' := h3.ne'
  have h6 : q.2.1 ^ 2 ≠ 0 := pow_ne_zero 2 h2'
  unfold gpdHessSigmaSigma
  fun_prop (disch := assumption)

end Pointwise

/-! ### Uniform constants on the neighbourhood -/

section Constants

variable {ξ₀ σ₀ : ℝ} (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
include hξ₀ hξ₀' hσ₀

/-- The coefficients of the Hessian bounds are bounded on the neighbourhood. -/
theorem exists_gpdCoef_bound :
    ∃ Kc C₁ : ℝ, 0 ≤ Kc ∧ 0 ≤ C₁ ∧ ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀,
      gpdHessCoef θ ≤ Kc ∧ gpdQuadCoef θ ≤ C₁ := by
  have hp : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, θ.1 ≠ 0 ∧ θ.2 ≠ 0 ∧ -(1 + θ.1) / θ.1 ≠ 0 := fun θ hθ => by
    obtain ⟨h1, h2, h3⟩ := param_bounds_of_mem_gpdNbhdNeg hξ₀' hσ₀ hξ₀ hθ
    exact ⟨h2.ne, h3.ne', (div_pos_of_neg_of_neg (by linarith) h2).ne'⟩
  have c1 : ContinuousOn gpdHessCoef (gpdNbhdNeg ξ₀ σ₀) := fun θ hθ => by
    obtain ⟨h1, h2, h3⟩ := hp θ hθ
    have h4 : θ.1 ^ 3 ≠ 0 := pow_ne_zero 3 h1
    have h5 : θ.1 ^ 2 ≠ 0 := pow_ne_zero 2 h1
    have h6 : θ.2 ^ 2 ≠ 0 := pow_ne_zero 2 h2
    refine ContinuousAt.continuousWithinAt ?_
    unfold gpdHessCoef
    fun_prop (disch := assumption)
  have c2 : ContinuousOn gpdQuadCoef (gpdNbhdNeg ξ₀ σ₀) := fun θ hθ => by
    obtain ⟨h1, h2, h3⟩ := hp θ hθ
    have h4 : θ.1 ^ 4 ≠ 0 := pow_ne_zero 4 h1
    have h5 : θ.1 ^ 2 ≠ 0 := pow_ne_zero 2 h1
    have h6 : θ.2 ^ 2 ≠ 0 := pow_ne_zero 2 h2
    have h7 : 4 * (-(1 + θ.1) / θ.1) ≠ 0 := mul_ne_zero four_ne_zero h3
    refine ContinuousAt.continuousWithinAt ?_
    unfold gpdQuadCoef
    fun_prop (disch := assumption)
  obtain ⟨K, hK⟩ := isCompact_gpdNbhdNeg.exists_bound_of_continuousOn c1
  obtain ⟨C, hC⟩ := isCompact_gpdNbhdNeg.exists_bound_of_continuousOn c2
  refine ⟨max K 0, max C 0, le_max_right _ _, le_max_right _ _, fun θ hθ => ⟨?_, ?_⟩⟩
  · exact (le_abs_self _).trans ((hK θ hθ).trans (le_max_left _ _))
  · exact (le_abs_self _).trans ((hC θ hθ).trans (le_max_left _ _))

end Constants

end ExtremeValueTheory
