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

end ExtremeValueTheory
