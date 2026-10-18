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

/-! ### The dominating function -/

section Dom

variable {ξ₀ σ₀ ξ σ x : ℝ}

/-- The integrable function `1 + w₀ + w₀² - log(1 + ξ₀ x/σ₀)`, `w₀ = x/(σ₀ + ξ₀ x)`, which
dominates the Hessian near `θ₀` away from the moving endpoint. -/
noncomputable def gpdDom (ξ₀ σ₀ x : ℝ) : ℝ :=
  1 + x / (σ₀ + ξ₀ * x) + (x / (σ₀ + ξ₀ * x)) ^ 2 - log (1 + ξ₀ * x / σ₀)

lemma measurable_gpdDom (ξ₀ σ₀ : ℝ) : Measurable (gpdDom ξ₀ σ₀) := by
  unfold gpdDom; fun_prop

lemma one_le_gpdDom (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀) (hx : 0 ≤ x) (h0 : 0 < σ₀ + ξ₀ * x) :
    1 ≤ gpdDom ξ₀ σ₀ x := by
  have hw : 0 ≤ x / (σ₀ + ξ₀ * x) := div_nonneg hx h0.le
  have hL : log (1 + ξ₀ * x / σ₀) ≤ 0 := by
    refine log_nonpos (one_add_mul_div_pos hσ₀ h0).le ?_
    have : ξ₀ * x / σ₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hξ₀'.le hx) hσ₀.le
    linarith
  unfold gpdDom
  nlinarith [sq_nonneg (x / (σ₀ + ξ₀ * x))]

lemma integrable_gpdDom (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀) :
    Integrable (gpdDom ξ₀ σ₀) (gpdMeasure ξ₀ σ₀) :=
  integrable_gpdMeasure_of_poly hξ₀ (measurable_gpdDom ξ₀ σ₀) (1 + 1 / ξ₀ + 1 / ξ₀ ^ 2) (-ξ₀) 0
    (-(1 / ξ₀) - 2 / ξ₀ ^ 2) (1 / ξ₀ ^ 2) 0 fun t => by
    unfold gpdDom
    rw [gpdTransform_div hσ₀ hξ₀'.ne, log_one_add_mul_gpdTransform hσ₀ hξ₀'.ne]
    have := hξ₀'.ne
    field_simp
    ring

/-- Where `σ + ξ x ≥ (σ₀ + ξ₀ x)/2`, the polynomial controlling the Hessian at `(ξ, σ)` is at
most `4 gpdDom`. -/
lemma le_gpdDom_of_half (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀) (hθ : (ξ, σ) ∈ gpdNbhdNeg ξ₀ σ₀)
    (hx : 0 ≤ x) (h0 : 0 < σ₀ + ξ₀ * x) (hh : (σ₀ + ξ₀ * x) / 2 ≤ σ + ξ * x) :
    |log (1 + ξ * x / σ)| + x / (σ + ξ * x) + (x / (σ + ξ * x)) ^ 2 + 1 ≤
      4 * gpdDom ξ₀ σ₀ x := by
  obtain ⟨-, h2, h3, h4⟩ := bounds_of_mem_gpdNbhdNeg hθ
  simp only at h2 h3 h4
  have hξ : ξ < 0 := by linarith
  have hσ : 0 < σ := by linarith
  have hu : 0 < σ + ξ * x := by linarith
  have hw₀ : 0 ≤ x / (σ₀ + ξ₀ * x) := div_nonneg hx h0.le
  -- `w ≤ 2 w₀`
  have hw : x / (σ + ξ * x) ≤ 2 * (x / (σ₀ + ξ₀ * x)) := by
    rw [div_le_iff₀ hu]
    rw [show 2 * (x / (σ₀ + ξ₀ * x)) * (σ + ξ * x) =
      x * (2 * (σ + ξ * x) / (σ₀ + ξ₀ * x)) by ring]
    have : 1 ≤ 2 * (σ + ξ * x) / (σ₀ + ξ₀ * x) := by rw [le_div_iff₀ h0]; linarith
    nlinarith
  have hw0 : 0 ≤ x / (σ + ξ * x) := div_nonneg hx hu.le
  -- the logarithms
  have hA := one_add_mul_div_pos hσ₀ h0
  have hB := one_add_mul_div_pos hσ hu
  have hL : log (1 + ξ * x / σ) ≤ 0 := by
    refine log_nonpos hB.le ?_
    have : ξ * x / σ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hξ.le hx) hσ.le
    linarith
  have hL₀ : log (1 + ξ₀ * x / σ₀) ≤ 0 := by
    refine log_nonpos hA.le ?_
    have : ξ₀ * x / σ₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hξ₀'.le hx) hσ₀.le
    linarith
  have hratio : (1 + ξ₀ * x / σ₀) / (1 + ξ * x / σ) ≤ 9 / 4 := by
    rw [div_le_iff₀ hB]
    have e1 : 1 + ξ₀ * x / σ₀ = (σ₀ + ξ₀ * x) / σ₀ := by field_simp
    have e2 : 1 + ξ * x / σ = (σ + ξ * x) / σ := by field_simp
    rw [e1, e2, div_le_iff₀ hσ₀]
    rw [show 9 / 4 * ((σ + ξ * x) / σ) * σ₀ = (σ + ξ * x) * (9 * σ₀ / (4 * σ)) by
      field_simp]
    have : 2 ≤ 9 * σ₀ / (4 * σ) := by rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith
  have hdiff : log (1 + ξ₀ * x / σ₀) - log (1 + ξ * x / σ) ≤ 2 := by
    rw [← log_div hA.ne' hB.ne']
    have := log_le_sub_one_of_pos (div_pos hA hB)
    linarith
  rw [abs_of_nonpos hL]
  unfold gpdDom
  nlinarith [mul_le_mul hw hw hw0 (by positivity)]

end Dom

/-! ### The score along a segment from `θ₀`, for a negative shape -/

section SegmentNeg

variable {ξ₀ σ₀ : ℝ}

lemma seg_support_eq (θ : ℝ × ℝ) (x s : ℝ) :
    (σ₀ + s * (θ.2 - σ₀)) + (ξ₀ + s * (θ.1 - ξ₀)) * x =
      (1 - s) * (σ₀ + ξ₀ * x) + s * (θ.2 + θ.1 * x) := by ring

lemma seg_support_pos {θ : ℝ × ℝ} {x : ℝ} (h0 : 0 < σ₀ + ξ₀ * x) (h1 : 0 < θ.2 + θ.1 * x)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < (σ₀ + s * (θ.2 - σ₀)) + (ξ₀ + s * (θ.1 - ξ₀)) * x := by
  rw [seg_support_eq]
  have hm := lt_min h0 h1
  nlinarith [mul_le_mul_of_nonneg_left (min_le_left (σ₀ + ξ₀ * x) (θ.2 + θ.1 * x))
    (sub_nonneg.2 hs.2), mul_le_mul_of_nonneg_left (min_le_right (σ₀ + ξ₀ * x) (θ.2 + θ.1 * x))
    hs.1]

lemma seg_support_half {θ : ℝ × ℝ} {x : ℝ} (h0 : 0 < σ₀ + ξ₀ * x)
    (h1 : (σ₀ + ξ₀ * x) / 2 ≤ θ.2 + θ.1 * x) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (σ₀ + ξ₀ * x) / 2 ≤ (σ₀ + s * (θ.2 - σ₀)) + (ξ₀ + s * (θ.1 - ξ₀)) * x := by
  rw [seg_support_eq]
  nlinarith [mul_le_mul_of_nonneg_left h1 hs.1, mul_nonneg (sub_nonneg.2 hs.2) h0.le]

variable (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
include hξ₀ hξ₀' hσ₀

lemma seg_params {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    -9 / 16 < ξ₀ + s * (θ.1 - ξ₀) ∧ ξ₀ + s * (θ.1 - ξ₀) < 0 ∧ 0 < σ₀ + s * (θ.2 - σ₀) :=
  param_bounds_of_mem_gpdNbhdNeg hξ₀' hσ₀ hξ₀ (segment_mem_gpdNbhdNeg hξ₀' hσ₀ hθ hs)

lemma continuousOn_seg {H : ℝ → ℝ → ℝ → ℝ}
    (hH : ∀ q : ℝ × ℝ × ℝ, q.1 ≠ 0 → 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {x : ℝ} (h0 : 0 < σ₀ + ξ₀ * x)
    (h1 : 0 < θ.2 + θ.1 * x) :
    ContinuousOn (fun s => H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x) (Icc 0 1) := by
  intro s hs
  obtain ⟨-, hp1, hp2⟩ := seg_params hξ₀ hξ₀' hσ₀ hθ hs
  have hpos := seg_support_pos h0 h1 hs
  exact ((hH (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀), x) hp1.ne hp2 hpos).comp
    (f := fun s => (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀), x))
    (by fun_prop)).continuousWithinAt

lemma intervalIntegrable_seg {H : ℝ → ℝ → ℝ → ℝ}
    (hH : ∀ q : ℝ × ℝ × ℝ, q.1 ≠ 0 → 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {x : ℝ} (h0 : 0 < σ₀ + ξ₀ * x)
    (h1 : 0 < θ.2 + θ.1 * x) :
    IntervalIntegrable (fun s => H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x) volume 0 1 :=
  ContinuousOn.intervalIntegrable (by
    rw [uIcc_of_le zero_le_one]; exact continuousOn_seg hξ₀ hξ₀' hσ₀ hH hθ h0 h1)

lemma intervalIntegrable_seg_XX {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {x : ℝ}
    (h0 : 0 < σ₀ + ξ₀ * x) (h1 : 0 < θ.2 + θ.1 * x) :
    IntervalIntegrable (fun s => gpdHessXiXi (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x)
      volume 0 1 :=
  intervalIntegrable_seg hξ₀ hξ₀' hσ₀ (fun _ h1 h2 h3 => continuousAt_gpdHessXiXi₃ h1 h2 h3)
    hθ h0 h1

lemma intervalIntegrable_seg_XS {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {x : ℝ}
    (h0 : 0 < σ₀ + ξ₀ * x) (h1 : 0 < θ.2 + θ.1 * x) :
    IntervalIntegrable (fun s => gpdHessXiSigma (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x)
      volume 0 1 :=
  intervalIntegrable_seg hξ₀ hξ₀' hσ₀ (fun _ _ h2 h3 => continuousAt_gpdHessXiSigma₃ h2 h3)
    hθ h0 h1

lemma intervalIntegrable_seg_SS {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {x : ℝ}
    (h0 : 0 < σ₀ + ξ₀ * x) (h1 : 0 < θ.2 + θ.1 * x) :
    IntervalIntegrable
      (fun s => gpdHessSigmaSigma (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x) volume 0 1 :=
  intervalIntegrable_seg hξ₀ hξ₀' hσ₀ (fun _ _ h2 h3 => continuousAt_gpdHessSigmaSigma₃ h2 h3)
    hθ h0 h1

/-- **The exact expansion of the score, negative shape.** For `θ` in the neighbourhood and an
observation `x` in the support of both `θ₀` and `θ`,
`∇ℓ(θ, x) - ∇ℓ(θ₀, x) = H̄(θ, x) (θ - θ₀)`. -/
theorem gpdScore_sub_eq_segHess_neg {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {x : ℝ}
    (h0 : 0 < σ₀ + ξ₀ * x) (h1 : 0 < θ.2 + θ.1 * x) :
    gpdScoreXi θ.1 θ.2 x - gpdScoreXi ξ₀ σ₀ x =
        (θ.1 - ξ₀) * segHess gpdHessXiXi ξ₀ σ₀ θ x +
          (θ.2 - σ₀) * segHess gpdHessXiSigma ξ₀ σ₀ θ x ∧
    gpdScoreSigma θ.1 θ.2 x - gpdScoreSigma ξ₀ σ₀ x =
        (θ.1 - ξ₀) * segHess gpdHessXiSigma ξ₀ σ₀ θ x +
          (θ.2 - σ₀) * segHess gpdHessSigmaSigma ξ₀ σ₀ θ x := by
  set a := θ.1 - ξ₀
  set b := θ.2 - σ₀
  have iXX := intervalIntegrable_seg_XX hξ₀ hξ₀' hσ₀ hθ h0 h1
  have iXS := intervalIntegrable_seg_XS hξ₀ hξ₀' hσ₀ hθ h0 h1
  have iSS := intervalIntegrable_seg_SS hξ₀ hξ₀' hσ₀ hθ h0 h1
  have hpos : ∀ s ∈ uIcc (0 : ℝ) 1, ξ₀ + s * a ≠ 0 ∧ 0 < σ₀ + s * b ∧
      0 < (σ₀ + s * b) + (ξ₀ + s * a) * x := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    obtain ⟨-, hp1, hp2⟩ := seg_params hξ₀ hξ₀' hσ₀ hθ hs
    exact ⟨hp1.ne, hp2, seg_support_pos h0 h1 hs⟩
  have e1 : ξ₀ + 1 * a = θ.1 := by simp [a]
  have e2 : σ₀ + 1 * b = θ.2 := by simp [b]
  refine ⟨?_, ?_⟩
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

/-- **The one-sided bound along the segment**: the segment-averaged Hessian quadratic form is at
most `C₁ |t|²`, whatever the position of the observation relative to the endpoints. -/
theorem segHess_quad_le_neg {C₁ : ℝ} (hC : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdQuadCoef θ ≤ C₁)
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) (h0 : 0 < σ₀ + ξ₀ * x)
    (h1 : 0 < θ.2 + θ.1 * x) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * segHess gpdHessXiXi ξ₀ σ₀ θ x + 2 * t₁ * t₂ * segHess gpdHessXiSigma ξ₀ σ₀ θ x +
        t₂ ^ 2 * segHess gpdHessSigmaSigma ξ₀ σ₀ θ x ≤ C₁ * (t₁ ^ 2 + t₂ ^ 2) := by
  have iXX := (intervalIntegrable_seg_XX hξ₀ hξ₀' hσ₀ hθ h0 h1).const_mul (t₁ ^ 2)
  have iXS := (intervalIntegrable_seg_XS hξ₀ hξ₀' hσ₀ hθ h0 h1).const_mul (2 * t₁ * t₂)
  have iSS := (intervalIntegrable_seg_SS hξ₀ hξ₀' hσ₀ hθ h0 h1).const_mul (t₂ ^ 2)
  unfold segHess
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add iXX iXS,
    ← intervalIntegral.integral_add (iXX.add iXS) iSS]
  have hle := intervalIntegral.integral_mono_on zero_le_one ((iXX.add iXS).add iSS)
    (intervalIntegrable_const (c := C₁ * (t₁ ^ 2 + t₂ ^ 2))) (fun s hs => by
      obtain ⟨hp0, hp1, hp2⟩ := seg_params hξ₀ hξ₀' hσ₀ hθ hs
      have hb := gpdHess_quad_le_coef (by linarith) hp1 hp2 hx (seg_support_pos h0 h1 hs) t₁ t₂
      have hc := hC _ (segment_mem_gpdNbhdNeg hξ₀' hσ₀ hθ hs)
      exact hb.trans (mul_le_mul_of_nonneg_right hc (by positivity)))
  simpa using hle

omit hξ₀ in
/-- **Domination along the segment**: if `σ + ξ x ≥ (σ₀ + ξ₀ x)/2`, the segment average of a
Hessian entry is at most `4 Kc gpdDom(x)`. -/
theorem abs_segHess_le_gpdDom {H : ℝ → ℝ → ℝ → ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hHb : ∀ ξ σ x, 0 ≤ x → 0 < σ + ξ * x → |H ξ σ x| ≤ gpdHessCoef (ξ, σ) *
      (|log (1 + ξ * x / σ)| + x / (σ + ξ * x) + (x / (σ + ξ * x)) ^ 2 + 1))
    {Kc : ℝ} (hK : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdHessCoef θ ≤ Kc)
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) (h0 : 0 < σ₀ + ξ₀ * x)
    (hh : (σ₀ + ξ₀ * x) / 2 ≤ θ.2 + θ.1 * x) :
    |segHess H ξ₀ σ₀ θ x| ≤ 4 * Kc * gpdDom ξ₀ σ₀ x := by
  have hb : ∀ s ∈ Icc (0 : ℝ) 1,
      |H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x - 0| ≤ 4 * Kc * gpdDom ξ₀ σ₀ x :=
    fun s hs => by
      rw [sub_zero]
      have hmem := segment_mem_gpdNbhdNeg hξ₀' hσ₀ hθ hs
      have hhalf := seg_support_half h0 hh hs
      have hpos : 0 < (σ₀ + s * (θ.2 - σ₀)) + (ξ₀ + s * (θ.1 - ξ₀)) * x := by linarith
      have h1 := hHb _ _ x hx hpos
      have h2 := le_gpdDom_of_half hξ₀' hσ₀ hmem hx h0 hhalf
      have h3 := hK _ hmem
      have hc0 : 0 ≤ gpdHessCoef (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀)) := by
        unfold gpdHessCoef; positivity
      have hP : 0 ≤ |log (1 + (ξ₀ + s * (θ.1 - ξ₀)) * x / (σ₀ + s * (θ.2 - σ₀)))| +
          x / ((σ₀ + s * (θ.2 - σ₀)) + (ξ₀ + s * (θ.1 - ξ₀)) * x) +
          (x / ((σ₀ + s * (θ.2 - σ₀)) + (ξ₀ + s * (θ.1 - ξ₀)) * x)) ^ 2 + 1 := by
        have := div_nonneg hx hpos.le; positivity
      calc _ ≤ _ := h1
        _ ≤ Kc * (4 * gpdDom ξ₀ σ₀ x) := mul_le_mul h3 h2 hP (hc0.trans h3)
        _ = 4 * Kc * gpdDom ξ₀ σ₀ x := by ring
  have := (intervalIntegrable_and_abs_integral_sub_le (c := 0)
    (hHm.comp (f := fun s => (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀), x)) (by fun_prop))
    hb).2
  rw [sub_zero] at this
  exact this

/-- **Uniform convergence on a good set** `{σ₀ + ξ₀ x ≥ c}`, away from the endpoint: for every
`ε > 0` there is `δ > 0` with `|H̄(θ, x) - H(θ₀, x)| ≤ ε` whenever `|θ - θ₀|₁ ≤ δ` and
`σ₀ + ξ₀ x ≥ c`. -/
theorem exists_delta_segHess_good {H : ℝ → ℝ → ℝ → ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hH : ∀ q : ℝ × ℝ × ℝ, q.1 ≠ 0 → 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ : ℝ × ℝ, gpdDist ξ₀ σ₀ θ ≤ δ → ∀ x, 0 ≤ x → c ≤ σ₀ + ξ₀ * x →
      |segHess H ξ₀ σ₀ θ x - H ξ₀ σ₀ x| ≤ ε := by
  set xc := (c - σ₀) / ξ₀ with hxc
  have hgood : ∀ x, c ≤ σ₀ + ξ₀ * x → x ≤ xc := fun x hx => by
    rw [hxc, le_div_iff_of_neg hξ₀']; linarith
  have hxcξ : ξ₀ * xc = c - σ₀ := mul_div_cancel₀ _ hξ₀'.ne
  set η := min (min (-ξ₀ / 8) (σ₀ / 8)) (c / (2 * (1 + |xc|))) with hη
  have hη0 : 0 < η := lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have hη1 : η ≤ -ξ₀ / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ σ₀ / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η * (1 + |xc|) ≤ c / 2 := by
    have := min_le_right (min (-ξ₀ / 8) (σ₀ / 8)) (c / (2 * (1 + |xc|)))
    rw [← hη] at this
    have h1 : 0 < 1 + |xc| := by positivity
    calc η * (1 + |xc|) ≤ c / (2 * (1 + |xc|)) * (1 + |xc|) := by gcongr
      _ = c / 2 := by field_simp
  set S : Set (ℝ × ℝ × ℝ) :=
    Icc (ξ₀ - η) (ξ₀ + η) ×ˢ (Icc (σ₀ - η) (σ₀ + η) ×ˢ Icc 0 xc) with hS
  have hSc : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hSpos : ∀ q ∈ S, q.1 ≠ 0 ∧ 0 < q.2.1 ∧ 0 < q.2.1 + q.1 * q.2.2 := fun q hq => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := hq
    refine ⟨by intro h; linarith, by linarith, ?_⟩
    have hx0 : xc = |xc| := (abs_of_nonneg (h5.trans h6)).symm
    have e : q.2.1 + q.1 * q.2.2 = (σ₀ + ξ₀ * xc) + ξ₀ * (q.2.2 - xc) + (q.2.1 - σ₀) +
        (q.1 - ξ₀) * q.2.2 := by ring
    have hA : 0 ≤ ξ₀ * (q.2.2 - xc) := mul_nonneg_of_nonpos_of_nonpos hξ₀'.le (by linarith)
    have hB : -η * xc ≤ (q.1 - ξ₀) * q.2.2 := by nlinarith
    rw [e, hxcξ]
    nlinarith
  have hcont : ContinuousOn (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) S := fun q hq =>
    (hH q (hSpos q hq).1 (hSpos q hq).2.1 (hSpos q hq).2.2).continuousWithinAt
  obtain ⟨δ₁, hδ₁, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (hSc.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min η (δ₁ / 2), lt_min hη0 (by linarith), fun θ hθ x hx hcx => ?_⟩
  have hρ1 : gpdDist ξ₀ σ₀ θ ≤ η := hθ.trans (min_le_left _ _)
  have hρ2 : gpdDist ξ₀ σ₀ θ ≤ δ₁ / 2 := hθ.trans (min_le_right _ _)
  have hxx := hgood x hcx
  have hb : ∀ s ∈ Icc (0 : ℝ) 1,
      |H (ξ₀ + s * (θ.1 - ξ₀)) (σ₀ + s * (θ.2 - σ₀)) x - H ξ₀ σ₀ x| ≤ ε := fun s hs => by
    have hd := gpdDist_segment (ξ₀ := ξ₀) (σ₀ := σ₀) θ hs
    have hd1 : |ξ₀ + s * (θ.1 - ξ₀) - ξ₀| + |σ₀ + s * (θ.2 - σ₀) - σ₀| ≤ gpdDist ξ₀ σ₀ θ :=
      hd
    have ha1 := abs_le.1 (show |ξ₀ + s * (θ.1 - ξ₀) - ξ₀| ≤ η by
      linarith [abs_nonneg (σ₀ + s * (θ.2 - σ₀) - σ₀)])
    have ha2 := abs_le.1 (show |σ₀ + s * (θ.2 - σ₀) - σ₀| ≤ η by
      linarith [abs_nonneg (ξ₀ + s * (θ.1 - ξ₀) - ξ₀)])
    have hmemA : (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀), x) ∈ S :=
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hx, hxx⟩
    have hmemB : (ξ₀, σ₀, x) ∈ S :=
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hx, hxx⟩
    have hdist : dist (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀), x) (ξ₀, σ₀, x) < δ₁ := by
      have := dist_triple_le (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀), x) (ξ₀, σ₀, x)
      simp only [sub_self, abs_zero, add_zero] at this
      linarith
    have := hδ _ hmemA _ hmemB hdist
    rw [Real.dist_eq] at this
    exact this.le
  exact (intervalIntegrable_and_abs_integral_sub_le
    (hHm.comp (f := fun s => (ξ₀ + s * (θ.1 - ξ₀), σ₀ + s * (θ.2 - σ₀), x)) (by fun_prop))
    hb).2

end SegmentNeg

/-! ### Averages along the sample -/

section AvgLemmas

lemma abs_avg_sub_le {n : ℕ} (hn : 0 < n) {f g b : ℕ → ℝ} {e : ℝ}
    (h : ∀ i < n, |f i - g i| ≤ e + b i) :
    |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f i - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g i| ≤
      e + (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, b i := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hn')]
  calc (n : ℝ)⁻¹ * |∑ i ∈ Finset.range n, (f i - g i)|
      ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (e + b i) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i hi => h i (Finset.mem_range.1 hi))
    _ = e + (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, b i := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_add]
        field_simp

lemma avg_le_avg {n : ℕ} {f g : ℕ → ℝ} (h : ∀ i < n, f i ≤ g i) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f i ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g i :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => h i (Finset.mem_range.1 hi))
    (inv_nonneg.2 (Nat.cast_nonneg _))

lemma avg_nonneg {n : ℕ} {f : ℕ → ℝ} (h : ∀ i < n, 0 ≤ f i) :
    0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f i :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i hi => h i (Finset.mem_range.1 hi))

lemma quad_avg (n : ℕ) (a b c : ℕ → ℝ) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) +
        2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, b i) +
        t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, c i) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (t₁ ^ 2 * a i + 2 * t₁ * t₂ * b i + t₂ ^ 2 * c i) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

lemma avg_add_const_mul {n : ℕ} (hn : 0 < n) (a b : ℕ → ℝ) (e K T : ℝ) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (a i + (e + K * b i) * T) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i +
        (e + K * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, b i)) * T := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have : ∑ i ∈ Finset.range n, (a i + (e + K * b i) * T) =
      ∑ i ∈ Finset.range n, a i + (n * e + K * ∑ i ∈ Finset.range n, b i) * T := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  rw [this]
  field_simp

lemma quad_le_of_abs_le {d₁ d₂ d₃ M : ℝ} (h₁ : |d₁| ≤ M) (h₂ : |d₂| ≤ M) (h₃ : |d₃| ≤ M)
    (t₁ t₂ : ℝ) : t₁ ^ 2 * d₁ + 2 * t₁ * t₂ * d₂ + t₂ ^ 2 * d₃ ≤ 2 * M * (t₁ ^ 2 + t₂ ^ 2) := by
  obtain ⟨a₁, b₁⟩ := abs_le.1 h₁
  obtain ⟨a₂, b₂⟩ := abs_le.1 h₂
  obtain ⟨a₃, b₃⟩ := abs_le.1 h₃
  have e1 : t₁ ^ 2 * d₁ ≤ t₁ ^ 2 * M := mul_le_mul_of_nonneg_left b₁ (sq_nonneg _)
  have e3 : t₂ ^ 2 * d₃ ≤ t₂ ^ 2 * M := mul_le_mul_of_nonneg_left b₃ (sq_nonneg _)
  have e2 : 0 ≤ (M - d₂) * (t₁ + t₂) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have e2' : 0 ≤ (M + d₂) * (t₁ - t₂) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith

end AvgLemmas

/-! ### The averaged Hessian along a consistent sequence -/

section Averages

variable {ξ₀ σ₀ : ℝ}

/-- The part `gpdDom · 1{σ₀ + ξ₀ x < c}` of the dominating function near the endpoint. -/
noncomputable def gpdDomTail (ξ₀ σ₀ c x : ℝ) : ℝ :=
  Set.indicator {y | σ₀ + ξ₀ * y < c} (gpdDom ξ₀ σ₀) x

lemma measurable_gpdDomTail (ξ₀ σ₀ c : ℝ) : Measurable (gpdDomTail ξ₀ σ₀ c) :=
  (measurable_gpdDom ξ₀ σ₀).indicator (measurableSet_lt (by fun_prop) measurable_const)

lemma gpdDomTail_of_le {c x : ℝ} (h : c ≤ σ₀ + ξ₀ * x) : gpdDomTail ξ₀ σ₀ c x = 0 :=
  Set.indicator_of_notMem (by simp only [mem_ofPred_eq, not_lt]; exact h) _

lemma gpdDomTail_of_lt {c x : ℝ} (h : σ₀ + ξ₀ * x < c) :
    gpdDomTail ξ₀ σ₀ c x = gpdDom ξ₀ σ₀ x :=
  Set.indicator_of_mem (show x ∈ {y | σ₀ + ξ₀ * y < c} from h) _

lemma gpdDomTail_nonneg (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀) {c x : ℝ} (hx : 0 ≤ x)
    (h0 : 0 < σ₀ + ξ₀ * x) : 0 ≤ gpdDomTail ξ₀ σ₀ c x := by
  by_cases h : σ₀ + ξ₀ * x < c
  · rw [gpdDomTail_of_lt h]; linarith [one_le_gpdDom hξ₀' hσ₀ hx h0]
  · rw [gpdDomTail_of_le (not_lt.1 h)]

lemma integrable_gpdDomTail (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀) (c : ℝ) :
    Integrable (gpdDomTail ξ₀ σ₀ c) (gpdMeasure ξ₀ σ₀) :=
  (integrable_gpdDom hξ₀ hξ₀' hσ₀).indicator (measurableSet_lt (by fun_prop) measurable_const)

/-- The tail of the dominating function has vanishing mean. -/
lemma tendsto_integral_gpdDomTail (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀) :
    Tendsto (fun k : ℕ => ∫ x, gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) x ∂gpdMeasure ξ₀ σ₀)
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun x => |gpdDom ξ₀ σ₀ x|)
    (F := fun (k : ℕ) x => gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) x) (f := fun _ => 0)
    (fun k => (measurable_gpdDomTail _ _ _).aestronglyMeasurable)
    (integrable_gpdDom hξ₀ hξ₀' hσ₀).abs
    (fun k => ae_of_all _ fun x =>
      (norm_indicator_le_norm_self (s := {y | σ₀ + ξ₀ * y < 1 / ((k : ℝ) + 1)})
          (gpdDom ξ₀ σ₀) x).trans_eq (Real.norm_eq_abs _)) ?_
  · simpa using h
  filter_upwards [ae_gpdMeasure (ξ := ξ₀) hσ₀] with x hx
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hx.2)] with k hk
  exact (gpdDomTail_of_le hk.le).symm

variable (hξ₀ : -1 / 2 < ξ₀) (hξ₀' : ξ₀ < 0) (hσ₀ : 0 < σ₀)
include hξ₀ hξ₀' hσ₀

omit hξ₀ in
/-- The Hessian at the true parameter is dominated by `4 Kc gpdDom`. -/
theorem abs_gpdHess_self_le {H : ℝ → ℝ → ℝ → ℝ}
    (hHb : ∀ ξ σ x, 0 ≤ x → 0 < σ + ξ * x → |H ξ σ x| ≤ gpdHessCoef (ξ, σ) *
      (|log (1 + ξ * x / σ)| + x / (σ + ξ * x) + (x / (σ + ξ * x)) ^ 2 + 1))
    {Kc : ℝ} (hK : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdHessCoef θ ≤ Kc) {x : ℝ} (hx : 0 ≤ x)
    (h0 : 0 < σ₀ + ξ₀ * x) : |H ξ₀ σ₀ x| ≤ 4 * Kc * gpdDom ξ₀ σ₀ x := by
  have hmem := mem_gpdNbhdNeg_self hξ₀' hσ₀
  have h1 := hHb ξ₀ σ₀ x hx h0
  have h2 := le_gpdDom_of_half hξ₀' hσ₀ hmem hx h0 (by linarith)
  have h3 := hK _ hmem
  have hc0 : 0 ≤ gpdHessCoef (ξ₀, σ₀) := by unfold gpdHessCoef; positivity
  have hP : 0 ≤ |log (1 + ξ₀ * x / σ₀)| + x / (σ₀ + ξ₀ * x) + (x / (σ₀ + ξ₀ * x)) ^ 2 + 1 := by
    have := div_nonneg hx h0.le; positivity
  calc _ ≤ _ := h1
    _ ≤ Kc * (4 * gpdDom ξ₀ σ₀ x) := mul_le_mul h3 h2 hP (hc0.trans h3)
    _ = 4 * Kc * gpdDom ξ₀ σ₀ x := by ring

omit hξ₀ in
/-- **The deviation of one segment-averaged Hessian entry**: at most `ε` on the good set and
`8 Kc gpdDom` near the endpoint, provided `σ + ξ x ≥ (σ₀ + ξ₀ x)/2`. -/
theorem segHess_dev_le {H : ℝ → ℝ → ℝ → ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hHb : ∀ ξ σ x, 0 ≤ x → 0 < σ + ξ * x → |H ξ σ x| ≤ gpdHessCoef (ξ, σ) *
      (|log (1 + ξ * x / σ)| + x / (σ + ξ * x) + (x / (σ + ξ * x)) ^ 2 + 1))
    {Kc : ℝ} (hK : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdHessCoef θ ≤ Kc) {c ε δ : ℝ}
    (hgood : ∀ θ : ℝ × ℝ, gpdDist ξ₀ σ₀ θ ≤ δ → ∀ x, 0 ≤ x → c ≤ σ₀ + ξ₀ * x →
      |segHess H ξ₀ σ₀ θ x - H ξ₀ σ₀ x| ≤ ε) (hε : 0 ≤ ε)
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) (hρ : gpdDist ξ₀ σ₀ θ ≤ δ) {x : ℝ} (hx : 0 ≤ x)
    (h0 : 0 < σ₀ + ξ₀ * x) (hh : (σ₀ + ξ₀ * x) / 2 ≤ θ.2 + θ.1 * x) :
    |segHess H ξ₀ σ₀ θ x - H ξ₀ σ₀ x| ≤ ε + 8 * Kc * gpdDomTail ξ₀ σ₀ c x := by
  by_cases hcx : c ≤ σ₀ + ξ₀ * x
  · rw [gpdDomTail_of_le hcx, mul_zero, add_zero]
    exact hgood θ hρ x hx hcx
  · rw [gpdDomTail_of_lt (not_le.1 hcx)]
    have h1 := abs_segHess_le_gpdDom hξ₀' hσ₀ hHm hHb hK hθ hx h0 hh
    have h2 := abs_gpdHess_self_le hξ₀' hσ₀ hHb hK hx h0
    have := abs_sub (segHess H ξ₀ σ₀ θ x) (H ξ₀ σ₀ x)
    linarith

/-- **The deviation of the segment-averaged Hessian quadratic form** (one-sided): at most
`2ε |t|²` on the good set and `(C₁ + 8 Kc) gpdDom |t|²` near the endpoint, whatever the
position of the observation relative to the endpoint of `θ`. -/
theorem segHess_quad_dev_le {Kc C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hK : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdHessCoef θ ≤ Kc)
    (hC : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdQuadCoef θ ≤ C₁) {c ε δ : ℝ} (hε : 0 ≤ ε)
    (g₁ : ∀ θ : ℝ × ℝ, gpdDist ξ₀ σ₀ θ ≤ δ → ∀ x, 0 ≤ x → c ≤ σ₀ + ξ₀ * x →
      |segHess gpdHessXiXi ξ₀ σ₀ θ x - gpdHessXiXi ξ₀ σ₀ x| ≤ ε)
    (g₂ : ∀ θ : ℝ × ℝ, gpdDist ξ₀ σ₀ θ ≤ δ → ∀ x, 0 ≤ x → c ≤ σ₀ + ξ₀ * x →
      |segHess gpdHessXiSigma ξ₀ σ₀ θ x - gpdHessXiSigma ξ₀ σ₀ x| ≤ ε)
    (g₃ : ∀ θ : ℝ × ℝ, gpdDist ξ₀ σ₀ θ ≤ δ → ∀ x, 0 ≤ x → c ≤ σ₀ + ξ₀ * x →
      |segHess gpdHessSigmaSigma ξ₀ σ₀ θ x - gpdHessSigmaSigma ξ₀ σ₀ x| ≤ ε)
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhdNeg ξ₀ σ₀) (hρ : gpdDist ξ₀ σ₀ θ ≤ δ) {x : ℝ} (hx : 0 ≤ x)
    (h0 : 0 < σ₀ + ξ₀ * x) (h1 : 0 < θ.2 + θ.1 * x) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * segHess gpdHessXiXi ξ₀ σ₀ θ x + 2 * t₁ * t₂ * segHess gpdHessXiSigma ξ₀ σ₀ θ x +
        t₂ ^ 2 * segHess gpdHessSigmaSigma ξ₀ σ₀ θ x ≤
      (t₁ ^ 2 * gpdHessXiXi ξ₀ σ₀ x + 2 * t₁ * t₂ * gpdHessXiSigma ξ₀ σ₀ x +
        t₂ ^ 2 * gpdHessSigmaSigma ξ₀ σ₀ x) +
      (2 * ε + (C₁ + 8 * Kc) * gpdDomTail ξ₀ σ₀ c x) * (t₁ ^ 2 + t₂ ^ 2) := by
  have ht : 0 ≤ t₁ ^ 2 + t₂ ^ 2 := by positivity
  by_cases hcx : c ≤ σ₀ + ξ₀ * x
  · rw [gpdDomTail_of_le hcx, mul_zero, add_zero]
    have := quad_le_of_abs_le (g₁ θ hρ x hx hcx) (g₂ θ hρ x hx hcx) (g₃ θ hρ x hx hcx) t₁ t₂
    nlinarith
  · rw [gpdDomTail_of_lt (not_le.1 hcx)]
    have hD := one_le_gpdDom hξ₀' hσ₀ hx h0
    have hq := segHess_quad_le_neg hξ₀ hξ₀' hσ₀ hC hθ hx h0 h1 t₁ t₂
    have b₁ := abs_gpdHess_self_le hξ₀' hσ₀ (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).1)
      hK hx h0
    have b₂ := abs_gpdHess_self_le hξ₀' hσ₀ (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).2.1)
      hK hx h0
    have b₃ := abs_gpdHess_self_le hξ₀' hσ₀ (fun ξ σ x hx hu => (abs_gpdHess_le hx hu).2.2)
      hK hx h0
    rw [← abs_neg] at b₁ b₂ b₃
    have hneg := quad_le_of_abs_le b₁ b₂ b₃ t₁ t₂
    have e1 : C₁ * (t₁ ^ 2 + t₂ ^ 2) ≤ C₁ * gpdDom ξ₀ σ₀ x * (t₁ ^ 2 + t₂ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hD hC₁
      nlinarith
    have e2 : 0 ≤ 2 * ε * (t₁ ^ 2 + t₂ ^ 2) := by positivity
    nlinarith

omit hξ₀ hξ₀' hσ₀ in
lemma tendsto_gpdDist {θs : ℕ → ℝ × ℝ} (hθ : Tendsto θs atTop (𝓝 (ξ₀, σ₀))) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ n in atTop, gpdDist ξ₀ σ₀ (θs n) ≤ δ := by
  have hc : Continuous (gpdDist ξ₀ σ₀) := by unfold gpdDist; fun_prop
  have := (hc.tendsto (ξ₀, σ₀)).comp hθ
  rw [show gpdDist ξ₀ σ₀ (ξ₀, σ₀) = 0 by simp [gpdDist]] at this
  exact this.eventually (ge_mem_nhds hδ)

/-- **Convergence of an averaged segment Hessian entry, negative shape** (deterministic). Along
`θₙ → θ₀`, given the strong laws for `H(θ₀, ·)` and for the tails of the dominating function,
for every `ε > 0` the empirical mean of `H̄(θₙ, xᵢ)` is eventually within `ε` of the limit `m`
of the empirical means of `H(θ₀, xᵢ)`, whenever all observations satisfy
`σₙ + ξₙ xᵢ ≥ (σ₀ + ξ₀ xᵢ)/2`. -/
theorem eventually_abs_avg_segHess_sub_le {H : ℝ → ℝ → ℝ → ℝ}
    (hHm : Measurable fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
    (hH : ∀ q : ℝ × ℝ × ℝ, q.1 ≠ 0 → 0 < q.2.1 → 0 < q.2.1 + q.1 * q.2.2 →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) q)
    (hHb : ∀ ξ σ x, 0 ≤ x → 0 < σ + ξ * x → |H ξ σ x| ≤ gpdHessCoef (ξ, σ) *
      (|log (1 + ξ * x / σ)| + x / (σ + ξ * x) + (x / (σ + ξ * x)) ^ 2 + 1))
    {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i ∧ 0 < σ₀ + ξ₀ * x i)
    {θs : ℕ → ℝ × ℝ} (hθ : Tendsto θs atTop (𝓝 (ξ₀, σ₀)))
    {m : ℝ} (hm : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (x i))
      atTop (𝓝 m))
    {d : ℕ → ℝ} (hD : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) (x i)) atTop (𝓝 (d k)))
    (hd : Tendsto d atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (∀ i < n, (σ₀ + ξ₀ * x i) / 2 ≤ (θs n).2 + (θs n).1 * x i) →
      |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess H ξ₀ σ₀ (θs n) (x i) - m| ≤ ε := by
  obtain ⟨Kc, C₁, hKc, hC₁, hb⟩ := exists_gpdCoef_bound hξ₀ hξ₀' hσ₀
  set A := 8 * Kc + 1 with hA
  have hA0 : 0 < A := by positivity
  obtain ⟨k, hk⟩ : ∃ k, A * d k < ε / 4 := by
    have h := hd.const_mul A
    rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  obtain ⟨δ, hδ, hgood⟩ := exists_delta_segHess_good hξ₀ hξ₀' hσ₀ hHm hH
    (c := 1 / ((k : ℝ) + 1)) (by positivity) (ε := ε / 4) (by positivity)
  filter_upwards [tendsto_gpdDist hθ hδ, hθ.eventually (gpdNbhdNeg_mem_nhds hξ₀' hσ₀),
    ((hD k).const_mul A).eventually (gt_mem_nhds hk),
    hm.eventually (Metric.ball_mem_nhds m (show 0 < ε / 4 by positivity)),
    eventually_gt_atTop 0] with n hn1 hn2 hn3 hn4 hn5 hhalf
  set tail : ℕ → ℝ := fun i => gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) (x i) with htail
  have h1 := abs_avg_sub_le hn5 (f := fun i => segHess H ξ₀ σ₀ (θs n) (x i))
    (g := fun i => H ξ₀ σ₀ (x i)) (e := ε / 4) (b := fun i => 8 * Kc * tail i)
    (fun i hi => segHess_dev_le hξ₀' hσ₀ hHm hHb (fun θ hθ => (hb θ hθ).1) hgood
      (by positivity) hn2 hn1 (hx i).1 (hx i).2 (hhalf i hi))
  have htail0 : 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i :=
    avg_nonneg fun i _ => gpdDomTail_nonneg hξ₀' hσ₀ (hx i).1 (hx i).2
  have h2 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, 8 * Kc * tail i ≤
      A * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) := by
    rw [← Finset.mul_sum, show (n : ℝ)⁻¹ * (8 * Kc * ∑ i ∈ Finset.range n, tail i) =
      8 * Kc * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) by ring]
    exact mul_le_mul_of_nonneg_right (by linarith) htail0
  have h3 : |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (x i) - m| < ε / 4 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hn4
  have h4 := abs_sub_le ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess H ξ₀ σ₀ (θs n) (x i))
    ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, H ξ₀ σ₀ (x i)) m
  simp only [htail] at h2 hn3
  linarith

/-- **The averaged observed information is eventually uniformly positive** (deterministic,
negative shape). Along `θₙ → θ₀` with all observations in the support of `θₙ`, if the limit
`m` of the empirical mean Hessians at `θ₀` satisfies `tᵀ m t ≤ -λ |t|²`, then eventually the
empirical mean of the segment-averaged Hessians `Bₙ` satisfies `tᵀ Bₙ t ≤ -(λ/2) |t|²`: the
observations near the endpoint contribute only through the one-sided bound. -/
theorem eventually_quad_avg_segHess_le {lam : ℝ} (hlam : 0 < lam) {m₁₁ m₁₂ m₂₂ : ℝ}
    (hm : ∀ t₁ t₂ : ℝ, t₁ ^ 2 * m₁₁ + 2 * t₁ * t₂ * m₁₂ + t₂ ^ 2 * m₂₂ ≤
      -lam * (t₁ ^ 2 + t₂ ^ 2))
    {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i ∧ 0 < σ₀ + ξ₀ * x i)
    {θs : ℕ → ℝ × ℝ} (hθ : Tendsto θs atTop (𝓝 (ξ₀, σ₀)))
    (hadm : ∀ᶠ n in atTop, ∀ i < n, 0 < (θs n).2 + (θs n).1 * x i)
    (h₁₁ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiXi ξ₀ σ₀ (x i))
      atTop (𝓝 m₁₁))
    (h₁₂ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiSigma ξ₀ σ₀ (x i))
      atTop (𝓝 m₁₂))
    (h₂₂ : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdHessSigmaSigma ξ₀ σ₀ (x i)) atTop (𝓝 m₂₂))
    {d : ℕ → ℝ} (hD : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) (x i)) atTop (𝓝 (d k)))
    (hd : Tendsto d atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiXi ξ₀ σ₀ (θs n) (x i)) +
        2 * t₁ * t₂ *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma ξ₀ σ₀ (θs n) (x i)) +
        t₂ ^ 2 *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, segHess gpdHessSigmaSigma ξ₀ σ₀ (θs n) (x i)) ≤
      -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2) := by
  obtain ⟨Kc, C₁, hKc, hC₁, hb⟩ := exists_gpdCoef_bound hξ₀ hξ₀' hσ₀
  have hK : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdHessCoef θ ≤ Kc := fun θ hθ => (hb θ hθ).1
  have hC : ∀ θ ∈ gpdNbhdNeg ξ₀ σ₀, gpdQuadCoef θ ≤ C₁ := fun θ hθ => (hb θ hθ).2
  set A := C₁ + 8 * Kc + 1 with hA
  have hA0 : 0 < A := by positivity
  set ε := lam / 16 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨k, hk⟩ : ∃ k, A * d k < lam / 16 := by
    have h := hd.const_mul A
    rw [mul_zero] at h
    exact (h.eventually (gt_mem_nhds (by positivity))).exists
  have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨δ₁, hδ₁, g₁⟩ := exists_delta_segHess_good hξ₀ hξ₀' hσ₀ measurable_gpdHessXiXi₃
    (fun _ h1 h2 h3 => continuousAt_gpdHessXiXi₃ h1 h2 h3) hc hε0
  obtain ⟨δ₂, hδ₂, g₂⟩ := exists_delta_segHess_good hξ₀ hξ₀' hσ₀ measurable_gpdHessXiSigma₃
    (fun _ _ h2 h3 => continuousAt_gpdHessXiSigma₃ h2 h3) hc hε0
  obtain ⟨δ₃, hδ₃, g₃⟩ := exists_delta_segHess_good hξ₀ hξ₀' hσ₀ measurable_gpdHessSigmaSigma₃
    (fun _ _ h2 h3 => continuousAt_gpdHessSigmaSigma₃ h2 h3) hc hε0
  set δ := min δ₁ (min δ₂ δ₃)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hball : ∀ {f : ℕ → ℝ} {m : ℝ}, Tendsto f atTop (𝓝 m) → ∀ᶠ n in atTop, |f n - m| ≤ ε :=
    fun {f m} h => (h.eventually (Metric.closedBall_mem_nhds m hε0)).mono fun n hn => by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hn
  filter_upwards [tendsto_gpdDist hθ hδ, hθ.eventually (gpdNbhdNeg_mem_nhds hξ₀' hσ₀),
    ((hD k).const_mul A).eventually (gt_mem_nhds hk), hball h₁₁, hball h₁₂, hball h₂₂,
    eventually_gt_atTop 0, hadm] with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 t₁ t₂
  set T := t₁ ^ 2 + t₂ ^ 2 with hT
  have hT0 : 0 ≤ T := by positivity
  set tail : ℕ → ℝ := fun i => gpdDomTail ξ₀ σ₀ (1 / ((k : ℝ) + 1)) (x i) with htail
  set q₀ : ℕ → ℝ := fun i => t₁ ^ 2 * gpdHessXiXi ξ₀ σ₀ (x i) +
    2 * t₁ * t₂ * gpdHessXiSigma ξ₀ σ₀ (x i) + t₂ ^ 2 * gpdHessSigmaSigma ξ₀ σ₀ (x i)
    with hq₀
  have hi : ∀ i < n, t₁ ^ 2 * segHess gpdHessXiXi ξ₀ σ₀ (θs n) (x i) +
      2 * t₁ * t₂ * segHess gpdHessXiSigma ξ₀ σ₀ (θs n) (x i) +
      t₂ ^ 2 * segHess gpdHessSigmaSigma ξ₀ σ₀ (θs n) (x i) ≤
      q₀ i + (2 * ε + (C₁ + 8 * Kc) * tail i) * T := fun i hi =>
    segHess_quad_dev_le hξ₀ hξ₀' hσ₀ hC₁ hK hC hε0.le
      (fun θ hθ => g₁ θ (hθ.trans (min_le_left _ _)))
      (fun θ hθ => g₂ θ (hθ.trans ((min_le_right _ _).trans (min_le_left _ _))))
      (fun θ hθ => g₃ θ (hθ.trans ((min_le_right _ _).trans (min_le_right _ _))))
      hn2 hn1 (hx i).1 (hx i).2 (hn8 i hi) t₁ t₂
  rw [quad_avg]
  refine (avg_le_avg hi).trans ?_
  rw [avg_add_const_mul hn7, hq₀, ← quad_avg]
  have htail0 : 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i :=
    avg_nonneg fun i _ => gpdDomTail_nonneg hξ₀' hσ₀ (hx i).1 (hx i).2
  have hdev := quad_le_of_abs_le hn4 hn5 hn6 t₁ t₂
  have hmt := hm t₁ t₂
  have htl : (C₁ + 8 * Kc) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) ≤ lam / 16 := by
    have : (C₁ + 8 * Kc) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) ≤
        A * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i) :=
      mul_le_mul_of_nonneg_right (by linarith) htail0
    simp only [htail] at hn3
    linarith
  have e : t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiXi ξ₀ σ₀ (x i)) +
      2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiSigma ξ₀ σ₀ (x i)) +
      t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessSigmaSigma ξ₀ σ₀ (x i)) =
      (t₁ ^ 2 * m₁₁ + 2 * t₁ * t₂ * m₁₂ + t₂ ^ 2 * m₂₂) +
      (t₁ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiXi ξ₀ σ₀ (x i) - m₁₁) +
        2 * t₁ * t₂ * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessXiSigma ξ₀ σ₀ (x i) - m₁₂) +
        t₂ ^ 2 * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gpdHessSigmaSigma ξ₀ σ₀ (x i) - m₂₂)) := by
    ring
  rw [e]
  have : (2 * ε + (C₁ + 8 * Kc) * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, tail i)) * T ≤
      (2 * ε + lam / 16) * T := mul_le_mul_of_nonneg_right (by linarith) hT0
  rw [hε] at this hdev
  nlinarith

end Averages

/-! ### Linear algebra of the linearized likelihood equations -/

section LinAlg

/-- The Fisher information is uniformly positive definite for `-1/2 < ξ < 0`:
`tᵀ (-I) t ≤ -|t|²/(4 (1 + ξ)(1 + σ²))`. -/
lemma gpdInfo_quad_le {ξ σ : ℝ} (hξ : -1 / 2 < ξ) (hξ' : ξ < 0) (hσ : 0 < σ) (t₁ t₂ : ℝ) :
    t₁ ^ 2 * -(2 / ((1 + ξ) * (1 + 2 * ξ))) +
        2 * t₁ * t₂ * -(1 / (σ * (1 + ξ) * (1 + 2 * ξ))) +
        t₂ ^ 2 * -(1 / (σ ^ 2 * (1 + 2 * ξ))) ≤
      -(1 / (4 * (1 + ξ) * (1 + σ ^ 2))) * (t₁ ^ 2 + t₂ ^ 2) := by
  have ha : 0 < 1 + ξ := by linarith
  have hb : 0 < 1 + 2 * ξ := by linarith
  set s := t₂ / σ with hs
  have ht₂ : t₂ = σ * s := by simp only [hs]; field_simp
  have e : t₁ ^ 2 * -(2 / ((1 + ξ) * (1 + 2 * ξ))) +
      2 * t₁ * t₂ * -(1 / (σ * (1 + ξ) * (1 + 2 * ξ))) +
      t₂ ^ 2 * -(1 / (σ ^ 2 * (1 + 2 * ξ))) =
      -((2 * t₁ ^ 2 + 2 * t₁ * s + (1 + ξ) * s ^ 2) / ((1 + ξ) * (1 + 2 * ξ))) := by
    rw [ht₂]; field_simp; ring
  rw [e]
  have hQ : (1 + 2 * ξ) / 4 * (t₁ ^ 2 + s ^ 2) ≤ 2 * t₁ ^ 2 + 2 * t₁ * s + (1 + ξ) * s ^ 2 := by
    have h_a : t₁ ^ 2 ≤ 2 * (t₁ + s / 2) ^ 2 + s ^ 2 / 2 := by nlinarith [sq_nonneg (t₁ + s)]
    nlinarith [mul_le_mul_of_nonneg_left h_a (by linarith : (0 : ℝ) ≤ (1 + 2 * ξ) / 4),
      mul_nonneg (by linarith : (0 : ℝ) ≤ -ξ) (sq_nonneg (t₁ + s / 2)),
      mul_nonneg hb.le (sq_nonneg s), sq_nonneg (t₁ + s / 2)]
  have hs2 : t₂ ^ 2 / (1 + σ ^ 2) ≤ s ^ 2 := by
    rw [hs, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg t₂, sq_nonneg σ]
  have ht1 : t₁ ^ 2 / (1 + σ ^ 2) ≤ t₁ ^ 2 := div_le_self (sq_nonneg _) (by nlinarith)
  have h1 : (t₁ ^ 2 + t₂ ^ 2) / (1 + σ ^ 2) ≤ t₁ ^ 2 + s ^ 2 := by rw [add_div]; linarith
  have h2 : 1 / (4 * (1 + ξ) * (1 + σ ^ 2)) * (t₁ ^ 2 + t₂ ^ 2) =
      (1 + 2 * ξ) / 4 * ((t₁ ^ 2 + t₂ ^ 2) / (1 + σ ^ 2)) / ((1 + ξ) * (1 + 2 * ξ)) := by
    have : 1 + ξ * 2 ≠ 0 := by intro h; linarith
    field_simp
  have h3 : (1 + 2 * ξ) / 4 * ((t₁ ^ 2 + t₂ ^ 2) / (1 + σ ^ 2)) ≤
      2 * t₁ ^ 2 + 2 * t₁ * s + (1 + ξ) * s ^ 2 :=
    (mul_le_mul_of_nonneg_left h1 (by positivity)).trans hQ
  have h4 := div_le_div_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ (1 + ξ) * (1 + 2 * ξ))
  rw [neg_mul, h2]
  linarith

/-- If `S = -B T` with `tᵀ B t ≤ -(λ/2)|t|²`, then `|T₁| + |T₂| ≤ (4/λ)(|S₁| + |S₂|)`. -/
lemma abs_add_abs_le_of_quad {B₁₁ B₁₂ B₂₂ S₁ S₂ T₁ T₂ lam : ℝ} (hlam : 0 < lam)
    (hq : ∀ t₁ t₂ : ℝ, t₁ ^ 2 * B₁₁ + 2 * t₁ * t₂ * B₁₂ + t₂ ^ 2 * B₂₂ ≤
      -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2))
    (hS₁ : S₁ = -(B₁₁ * T₁ + B₁₂ * T₂)) (hS₂ : S₂ = -(B₁₂ * T₁ + B₂₂ * T₂)) :
    |T₁| + |T₂| ≤ 4 / lam * (|S₁| + |S₂|) := by
  have h := hq T₁ T₂
  have hTS : (lam / 2) * (T₁ ^ 2 + T₂ ^ 2) ≤ T₁ * S₁ + T₂ * S₂ := by
    rw [hS₁, hS₂]; nlinarith
  have hCS : T₁ * S₁ + T₂ * S₂ ≤ (|T₁| + |T₂|) * (|S₁| + |S₂|) := by
    have a1 : T₁ * S₁ ≤ |T₁| * |S₁| := by rw [← abs_mul]; exact le_abs_self _
    have a2 : T₂ * S₂ ≤ |T₂| * |S₂| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith [abs_nonneg T₁, abs_nonneg T₂, abs_nonneg S₁, abs_nonneg S₂]
  have hsq : (|T₁| + |T₂|) ^ 2 ≤ 2 * (T₁ ^ 2 + T₂ ^ 2) := by
    nlinarith [sq_abs T₁, sq_abs T₂, sq_nonneg (|T₁| - |T₂|)]
  set u := |T₁| + |T₂|
  set v := |S₁| + |S₂|
  have hu : 0 ≤ u := by positivity
  have hv : 0 ≤ v := by positivity
  have key : lam / 4 * u ^ 2 ≤ u * v := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
  rcases hu.eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]; positivity
  · nlinarith

/-- If `tᵀ B t ≤ -(λ/2)|t|²`, then `det B > 0`. -/
lemma det_pos_of_quad {B₁₁ B₁₂ B₂₂ lam : ℝ} (hlam : 0 < lam)
    (hq : ∀ t₁ t₂ : ℝ, t₁ ^ 2 * B₁₁ + 2 * t₁ * t₂ * B₁₂ + t₂ ^ 2 * B₂₂ ≤
      -(lam / 2) * (t₁ ^ 2 + t₂ ^ 2)) :
    0 < B₁₁ * B₂₂ - B₁₂ ^ 2 := by
  have h1 := hq 1 0
  have h2 := hq B₁₂ (-B₁₁)
  simp only [one_pow, one_mul, mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_one] at h1
  have hB : B₁₁ < 0 := by linarith
  have e : B₁₂ ^ 2 * B₁₁ + 2 * B₁₂ * -B₁₁ * B₁₂ + (-B₁₁) ^ 2 * B₂₂ =
      B₁₁ * (B₁₁ * B₂₂ - B₁₂ ^ 2) := by ring
  rw [e] at h2
  have hpos : 0 < lam / 2 * (B₁₂ ^ 2 + (-B₁₁) ^ 2) := by
    have : 0 < (-B₁₁) ^ 2 := pow_pos (by linarith) 2
    have := sq_nonneg B₁₂
    positivity
  have : B₁₁ * (B₁₁ * B₂₂ - B₁₂ ^ 2) < 0 := by linarith
  by_contra hcon
  have := mul_nonneg_of_nonpos_of_nonpos hB.le (not_lt.1 hcon)
  linarith

end LinAlg

end ExtremeValueTheory
