/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLEInformation
import ExtremeValueTheory.Statistics.GPDLikelihoodNormality

/-!
# The GEV likelihood equations along a sample path

This file contains the deterministic part of the proof of the asymptotic normality of the GEV
maximum likelihood estimator. Fix a sample `x₀, x₁, …` in the support of the truth `θ₀`, on which
the averages of the second derivatives at the truth and of the error terms `gevEtaTail` converge to
their expectations (`gevPath_estimates`, hypotheses `hM`, `hT`), and estimators `θ̂ₙ → θ₀` which, for
all large `n`, are local maximizers of the likelihood at which every observation is in the support.
With `Δₙ = η(θ̂ₙ) - η₀`, the increment in the coordinates `η` of
`ExtremeValueTheory.Statistics.GEVMLECoordinates`:

* `sum_gevEtaD_eq_zero_of_isLocalMax`: the likelihood equations hold in the coordinates `η`.
* `exists_sum_gevEtaM_eq`: the mean value theorem along the segment from `η₀` to `η₀ + Δₙ`; since
  `u` is affine on this segment, it lies in the support of every observation.
* `gevPath_dev`: the average of the second derivatives is close to minus the information, with the
  one-sided bound for all parameters near the truth at which the observations are in the support,
  and the two-sided bound for the parameters at which every observation is good.
* `gevPath_estimates`: **the rate and the linearization**. From the one-sided bound,
  `√n |Δₙ| ≤ C Σⱼ |Zₙⱼ|`, `Zₙ = n^{-1/2} ∑_{i<n} ∇ℓ(θ₀, xᵢ)`: this is the **preliminary `√n` rate**
  (no observation can spoil it, the one-sided bound holds for all of them). If moreover
  `|Δₙ| (1 + max_{i<n} 1/v(xᵢ)) < 1/2`, every observation is good all along the segment, and
  `√n (θ̂ₙ - θ₀)` is `I(θ₀)⁻¹ Zₙ`, up to an arbitrarily small multiple of `1 + Σⱼ |Zₙⱼ|`.

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix

namespace ExtremeValueTheory

/-! ### The likelihood equations in the coordinates `η` -/

section Stationary

variable {ξ₀ μ₀ σ₀ : ℝ}

/-- Inside the support, the GEV density is positive. -/
lemma gevLocScaleDensity_pos {ξ μ σ x : ℝ} (hσ : 0 < σ) (hξ : ξ ≠ 0) (hu : 0 < gevU ξ μ σ x) :
    0 < gevLocScaleDensity ξ μ σ x := by
  have hu' : 0 < 1 + ξ * ((x - μ) / σ) := hu
  simp only [gevLocScaleDensity, gevDensity, hξ, hu', ↓reduceIte]
  positivity

/-- Where the GEV density is positive, the observation is in the support. -/
lemma gevU_pos_of_gevLocScaleDensity_pos {ξ μ σ x : ℝ} (hξ : ξ ≠ 0)
    (h : 0 < gevLocScaleDensity ξ μ σ x) : 0 < gevU ξ μ σ x := by
  by_contra hu
  have hu' : ¬ 0 < 1 + ξ * ((x - μ) / σ) := hu
  simp [gevLocScaleDensity, gevDensity, hξ, hu'] at h

private lemma hasDerivAt_line (a τ s : ℝ) : HasDerivAt (fun r => a + r * τ) τ s := by
  simpa using ((hasDerivAt_id s).mul_const τ).const_add a

/-- **The likelihood equations in the coordinates `η`.** At a local maximizer `θ` of the extended
real log-likelihood at which every observation is in the support, the derivative of the
log-likelihood in the coordinates `η` vanishes in every direction `e`. -/
theorem sum_gevEtaD_eq_zero_of_isLocalMax (hξ₀ : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) {n : ℕ} {x : Fin n → ℝ}
    {θ : ℝ × ℝ × ℝ} (hθ1 : 0 < θ.1 / ξ₀) (hθ2 : 0 < θ.2.2)
    (hadm : ∀ i, 0 < gevU θ.1 θ.2.1 θ.2.2 (x i))
    (hmax : IsLocalMax (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) θ) (e : ℝ × ℝ × ℝ) :
    ∑ i, gevEtaD (gevEtaOf ξ₀ μ₀ σ₀ θ) (gevU ξ₀ μ₀ σ₀ (x i)) e = 0 := by
  have hξθ : θ.1 ≠ 0 := fun h => by simp [h] at hθ1
  set η := gevEtaOf ξ₀ μ₀ σ₀ θ with hη
  have hη1 : η.1 = θ.1 := rfl
  have hκ : 0 < η.2.2 := by
    have e1 : η.2.2 = θ.1 / ξ₀ * (σ₀ / θ.2.2) := by
      simp only [hη, gevEtaOf]
      field_simp
    rw [e1]
    positivity
  have hθη : gevThetaOf ξ₀ μ₀ σ₀ η = θ := gevThetaOf_gevEtaOf hξ₀ hσ₀.ne' hξθ hθ2.ne'
  have huη : ∀ i, 0 < gevEtaU η (gevU ξ₀ μ₀ σ₀ (x i)) := fun i => by
    have := gevU_gevThetaOf (μ₀ := μ₀) hξ₀ hσ₀.ne' (η := η) hξθ hκ.ne' (x i)
    rw [hθη] at this
    rw [← this]
    exact hadm i
  -- the curve through `η` in the direction `e`
  set X : ℝ → ℝ := fun r => η.1 + r * e.1 with hX
  set K₀ : ℝ → ℝ := fun r => η.2.1 + r * e.2.1 with hK₀
  set K₁ : ℝ → ℝ := fun r => η.2.2 + r * e.2.2 with hK₁
  have hc0 : (X 0, K₀ 0, K₁ 0) = η := by simp [hX, hK₀, hK₁]
  have hdX := fun s => hasDerivAt_line η.1 e.1 s
  have hdK₀ := fun s => hasDerivAt_line η.2.1 e.2.1 s
  have hdK₁ := fun s => hasDerivAt_line η.2.2 e.2.2 s
  set g : ℝ → ℝ := fun r => ∑ i, gevEtaLog ξ₀ σ₀ (X r, K₀ r, K₁ r) (gevU ξ₀ μ₀ σ₀ (x i)) with hg
  have hd : HasDerivAt g (∑ i, gevEtaD η (gevU ξ₀ μ₀ σ₀ (x i)) e) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h := hasDerivAt_gevEtaLog (v := gevU ξ₀ μ₀ σ₀ (x i)) (σ₀ := σ₀) hξ₀ (hdX 0) (hdK₀ 0)
      (hdK₁ 0) (by simpa [hX, hη1] using hξθ) (by simpa [hK₁] using hκ.ne')
      (by rw [hc0]; exact (huη i).ne')
    rw [hc0] at h
    exact h
  -- near `0`, the curve is admissible
  have hcX : ContinuousAt X 0 := (hdX 0).continuousAt
  have hcK : ContinuousAt K₁ 0 := (hdK₁ 0).continuousAt
  have hcK₀ : ContinuousAt K₀ 0 := (hdK₀ 0).continuousAt
  have hne1 : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < X r / ξ₀ := by
    have : ContinuousAt (fun r => X r / ξ₀) 0 := hcX.div_const ξ₀
    refine this.eventually (lt_mem_nhds ?_)
    simpa [hX, hη1] using hθ1
  have hne2 : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < K₁ r :=
    hcK.eventually (lt_mem_nhds (by simpa [hK₁] using hκ))
  have hne3 : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i, 0 < gevEtaU (X r, K₀ r, K₁ r) (gevU ξ₀ μ₀ σ₀ (x i)) := by
    refine eventually_all.2 fun i => ?_
    have hc : ContinuousAt (fun r => gevEtaU (X r, K₀ r, K₁ r) (gevU ξ₀ μ₀ σ₀ (x i))) 0 := by
      unfold gevEtaU
      exact hcK₀.add (hcK.mul continuousAt_const)
    refine hc.eventually (lt_mem_nhds ?_)
    simp only [hc0]
    exact huη i
  have hcθ : ContinuousAt (fun r => gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)) 0 := by
    have hden : ξ₀ * K₁ 0 ≠ 0 := mul_ne_zero hξ₀ (by simpa [hK₁] using hκ.ne')
    unfold gevThetaOf
    exact hcX.prodMk ((continuousAt_const.add
      (((continuousAt_const.sub hcK).sub hcK₀).mul continuousAt_const |>.div
        (continuousAt_const.mul hcK) hden)).prodMk
      ((hcX.mul continuousAt_const).div (continuousAt_const.mul hcK) hden))
  have hval : gevThetaOf ξ₀ μ₀ σ₀ (X 0, K₀ 0, K₁ 0) = θ := by rw [hc0, hθη]
  have hmax' : ∀ᶠ r in 𝓝 (0 : ℝ),
      gevLogLikE (gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)).1
        (gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)).2.1
        (gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)).2.2 x ≤ gevLogLikE θ.1 θ.2.1 θ.2.2 x := by
    have : Tendsto (fun r => gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)) (𝓝 0) (𝓝 θ) := by
      have := hcθ.tendsto
      rwa [hval] at this
    exact this.eventually hmax
  -- the log-likelihood along the curve
  have hL : ∀ {r : ℝ}, 0 < X r / ξ₀ → 0 < K₁ r →
      (∀ i, 0 < gevEtaU (X r, K₀ r, K₁ r) (gevU ξ₀ μ₀ σ₀ (x i))) →
      gevLogLikE (gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)).1
        (gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)).2.1
        (gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)).2.2 x = ((g r : ℝ) : EReal) := by
    intro r h1 h2 h3
    have hξr : (X r, K₀ r, K₁ r).1 ≠ 0 := fun h => by
      simp only at h
      simp [h] at h1
    have hσr := gevThetaOf_scale_pos (μ₀ := μ₀) (η := (X r, K₀ r, K₁ r)) hσ₀ h1 h2
    have hdens : ∀ i, 0 < gevLocScaleDensity (gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)).1
        (gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)).2.1
        (gevThetaOf ξ₀ μ₀ σ₀ (X r, K₀ r, K₁ r)).2.2 (x i) := fun i => by
      refine gevLocScaleDensity_pos hσr hξr ?_
      rw [gevU_gevThetaOf hξ₀ hσ₀.ne' hξr h2.ne']
      exact h3 i
    rw [gevLogLikE_eq_coe hdens]
    congr 1
    simp only [gevLogLik, hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact log_gevLocScaleDensity_gevThetaOf hξ₀ hσ₀ h1 h2 (h3 i)
  have hL0 : gevLogLikE θ.1 θ.2.1 θ.2.2 x = ((g 0 : ℝ) : EReal) := by
    have h1 : 0 < X 0 / ξ₀ := by simpa [hX, hη1] using hθ1
    have h2 : 0 < K₁ 0 := by simpa [hK₁] using hκ
    have h3 : ∀ i, 0 < gevEtaU (X 0, K₀ 0, K₁ 0) (gevU ξ₀ μ₀ σ₀ (x i)) := fun i => by
      rw [hc0]
      exact huη i
    have := hL h1 h2 h3
    rwa [hval] at this
  have hloc : IsLocalMax g 0 := by
    filter_upwards [hne1, hne2, hne3, hmax'] with r h1 h2 h3 h4
    rw [hL h1 h2 h3, hL0] at h4
    exact EReal.coe_le_coe_iff.1 h4
  exact hloc.hasDerivAt_eq_zero hd

end Stationary

/-! ### The mean value theorem along the segment from the truth -/

section MeanValue

variable {ξ₀ : ℝ}

/-- The segment from the truth `(ξ₀, 0, 1)` in the direction `Δ`. -/
def gevEtaLine (ξ₀ : ℝ) (Δ : ℝ × ℝ × ℝ) (s : ℝ) : ℝ × ℝ × ℝ :=
  (ξ₀ + s * Δ.1, 0 + s * Δ.2.1, 1 + s * Δ.2.2)

lemma gevEtaLine_zero (Δ : ℝ × ℝ × ℝ) : gevEtaLine ξ₀ Δ 0 = (ξ₀, 0, 1) := by simp [gevEtaLine]

lemma gevEtaLine_one (Δ : ℝ × ℝ × ℝ) : gevEtaLine ξ₀ Δ 1 = (ξ₀, 0, 1) + Δ := by
  simp [gevEtaLine, Prod.ext_iff]

lemma gevEtaLine_sub (Δ : ℝ × ℝ × ℝ) (s : ℝ) :
    gevEtaLine ξ₀ Δ s - (ξ₀, 0, 1) = s • Δ := by
  simp [gevEtaLine, Prod.ext_iff]

lemma gevEtaNorm_gevEtaLine_sub_le (Δ : ℝ × ℝ × ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    gevEtaNorm (gevEtaLine ξ₀ Δ s - (ξ₀, 0, 1)) ≤ gevEtaNorm Δ := by
  rw [gevEtaLine_sub, gevEtaNorm_smul, abs_of_nonneg hs.1]
  exact mul_le_of_le_one_left (gevEtaNorm_nonneg Δ) hs.2

lemma gevEtaLine_mem_gevEtaBox {Δ : ℝ × ℝ × ℝ} (hΔ : (ξ₀, (0 : ℝ), (1 : ℝ)) + Δ ∈ gevEtaBox ξ₀)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : gevEtaLine ξ₀ Δ s ∈ gevEtaBox ξ₀ := by
  have := convex_gevEtaBox (ξ₀ := ξ₀) mem_gevEtaBox_self hΔ (a := 1 - s) (b := s)
    (by linarith [hs.2]) hs.1 (by ring)
  convert this using 1
  simp only [gevEtaLine, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨by ring, by ring, by ring⟩

/-- On the segment, `u` is the convex combination of `v` and its value at the end point. -/
lemma gevEtaU_gevEtaLine (Δ : ℝ × ℝ × ℝ) (s v : ℝ) :
    gevEtaU (gevEtaLine ξ₀ Δ s) v = (1 - s) * v + s * gevEtaU ((ξ₀, 0, 1) + Δ) v := by
  simp only [gevEtaLine, gevEtaU, Prod.fst_add, Prod.snd_add]
  ring

/-- If `|Δ| (1 + 1/v) ≤ 1/2`, the observation is good all along the segment. -/
lemma gevEtaU_gevEtaLine_good (Δ : ℝ × ℝ × ℝ) {s v : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hv : 0 < v)
    (h : gevEtaNorm Δ * (1 + 1 / v) ≤ 1 / 2) :
    v / 2 ≤ gevEtaU (gevEtaLine ξ₀ Δ s) v ∧ gevEtaU (gevEtaLine ξ₀ Δ s) v ≤ 2 * v := by
  have hb := abs_snd_fst_le_gevEtaNorm Δ
  have hc := abs_snd_snd_le_gevEtaNorm Δ
  have hN := gevEtaNorm_nonneg Δ
  have h1 : gevEtaNorm Δ * (1 + v) ≤ v / 2 := by
    have e : gevEtaNorm Δ * (1 + v) = gevEtaNorm Δ * (1 + 1 / v) * v := by
      field_simp
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_right h hv.le
    linarith
  have h2 : |s * Δ.2.1 + s * Δ.2.2 * v| ≤ gevEtaNorm Δ * (1 + v) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs.1, abs_of_pos hv]
    have hs1 := hs.2
    have hs0 := hs.1
    have a1 : s * |Δ.2.1| ≤ gevEtaNorm Δ := by nlinarith [abs_nonneg Δ.2.1]
    have a2 : s * |Δ.2.2| ≤ gevEtaNorm Δ := by nlinarith [abs_nonneg Δ.2.2]
    nlinarith
  have e : gevEtaU (gevEtaLine ξ₀ Δ s) v = v + (s * Δ.2.1 + s * Δ.2.2 * v) := by
    simp only [gevEtaLine, gevEtaU]
    ring
  rw [e]
  have := abs_le.1 (h2.trans h1)
  constructor <;> linarith [this.1, this.2]

/-- **The mean value theorem along the segment.** If the segment from the truth stays in the
domain of the log-density, then there is a point of the segment at which the increment of the
derivative in the direction `e` is the second derivative in the directions `Δ, e`. -/
theorem exists_sum_gevEtaM_eq {Δ e : ℝ × ℝ × ℝ} {n : ℕ} {v : ℕ → ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) 1, (gevEtaLine ξ₀ Δ s).1 ≠ 0 ∧ (gevEtaLine ξ₀ Δ s).2.2 ≠ 0 ∧
      ∀ i < n, gevEtaU (gevEtaLine ξ₀ Δ s) (v i) ≠ 0) :
    ∃ s ∈ Ioo (0 : ℝ) 1, ∑ i ∈ Finset.range n, gevEtaD ((ξ₀, 0, 1) + Δ) (v i) e -
        ∑ i ∈ Finset.range n, gevEtaD (ξ₀, 0, 1) (v i) e =
      ∑ i ∈ Finset.range n, gevEtaM (gevEtaLine ξ₀ Δ s) (v i) Δ e := by
  set f : ℝ → ℝ := fun s => ∑ i ∈ Finset.range n, gevEtaD (gevEtaLine ξ₀ Δ s) (v i) e with hf
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f
      (∑ i ∈ Finset.range n, gevEtaM (gevEtaLine ξ₀ Δ s) (v i) Δ e) s := fun s hs => by
    obtain ⟨h1, h2, h3⟩ := h s hs
    exact HasDerivAt.fun_sum fun i hi =>
      hasDerivAt_gevEtaD (X := fun r => ξ₀ + r * Δ.1) (K₀ := fun r => 0 + r * Δ.2.1)
        (K₁ := fun r => 1 + r * Δ.2.2) e (hasDerivAt_line _ _ s) (hasDerivAt_line _ _ s)
        (hasDerivAt_line _ _ s) h1 h2 (h3 i (Finset.mem_range.1 hi))
  obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope f _ (zero_lt_one' ℝ)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  refine ⟨s, hs, ?_⟩
  rw [hslope]
  simp only [hf, gevEtaLine_zero, gevEtaLine_one, sub_zero, div_one]

end MeanValue

/-! ### The averages along a sample path -/

section Dev

variable {ξ₀ σ₀ ε K : ℝ}

/-- The conclusion of `exists_gevEtaM_dev_le`, as a named property of the constant `K`. -/
def GevEtaDev (ξ₀ ε K : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ e' : ℝ, 0 < e' → ∃ δ : ℝ, 0 < δ ∧
    ∀ η ∈ gevEtaBox ξ₀, gevEtaNorm (η - (ξ₀, 0, 1)) ≤ δ → ∀ v : ℝ, 0 < v →
      (0 < gevEtaU η v → ∀ d : ℝ × ℝ × ℝ, gevEtaM η v d d ≤ gevEtaM (ξ₀, 0, 1) v d d +
        (e' + gevEtaTail ξ₀ ε K c v) * gevEtaNorm d ^ 2) ∧
      (v / 2 ≤ gevEtaU η v → gevEtaU η v ≤ 2 * v → ∀ d e : ℝ × ℝ × ℝ,
        |gevEtaM η v d e - gevEtaM (ξ₀, 0, 1) v d e| ≤
          (e' + gevEtaTail ξ₀ ε K c v) * gevEtaNorm d * gevEtaNorm e)

/-- The information form is bilinear. -/
lemma gevEtaInfo_eq_sum (ξ₀ σ₀ : ℝ) (d e : ℝ × ℝ × ℝ) :
    gevEtaInfo ξ₀ σ₀ d e = ∑ j, ∑ k, gevEtaCoord d j * gevEtaCoord e k *
      gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k) := by
  simp only [gevEtaInfo, gevEtaJ, gevEtaBasis, gevEtaCoord, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three]
  simp
  ring

private lemma avg_gevEtaM_eq (v : ℕ → ℝ) (n : ℕ) (d e : ℝ × ℝ × ℝ) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM (ξ₀, 0, 1) (v i) d e =
      ∑ j, ∑ k, gevEtaCoord d j * gevEtaCoord e k * ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        gevEtaM (ξ₀, 0, 1) (v i) (gevEtaBasis j) (gevEtaBasis k)) := by
  simp_rw [gevEtaM_eq_sum (ξ₀, 0, 1) _ d e, Fin.sum_univ_three, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- **The averaged second derivatives along a sample path.** If the averages of the second
derivatives at the truth converge to minus the information, and the averages of the error terms to
numbers tending to `0`, then for every `e' > 0` there is `δ > 0` such that for all large `n`, and
for `η` in the box within `δ` of the truth:

* if every observation is in the support of `η`: the average of `M(η, vᵢ)[d, d]` is at most
  `-I(d, d) + e' |d|²`;
* if every observation is good for `η`: the average of `M(η, vᵢ)[d, e]` is within `e' |d| |e|` of
  `-I(d, e)`. -/
theorem gevPath_dev (hdev : GevEtaDev ξ₀ ε K) {v : ℕ → ℝ} (hv : ∀ i, 0 < v i)
    (hM : ∀ j k, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        gevEtaM (ξ₀, 0, 1) (v i) (gevEtaBasis j) (gevEtaBasis k)) atTop
      (𝓝 (-gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k))))
    {t : ℕ → ℝ} (hT : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (v i)) atTop (𝓝 (t k)))
    (ht : Tendsto t atTop (𝓝 0)) {e' : ℝ} (he' : 0 < e') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ η ∈ gevEtaBox ξ₀, gevEtaNorm (η - (ξ₀, 0, 1)) ≤ δ →
      ((∀ i < n, 0 < gevEtaU η (v i)) → ∀ d : ℝ × ℝ × ℝ,
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM η (v i) d d ≤
          -gevEtaInfo ξ₀ σ₀ d d + e' * gevEtaNorm d ^ 2) ∧
      ((∀ i < n, v i / 2 ≤ gevEtaU η (v i) ∧ gevEtaU η (v i) ≤ 2 * v i) →
        ∀ d e : ℝ × ℝ × ℝ, |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM η (v i) d e +
          gevEtaInfo ξ₀ σ₀ d e| ≤ e' * gevEtaNorm d * gevEtaNorm e) := by
  have he3 : 0 < e' / 3 := by positivity
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds he3)).exists
  obtain ⟨δ, hδ, hδu⟩ := hdev (1 / ((k : ℝ) + 1)) (by positivity) (e' / 3) he3
  refine ⟨δ, hδ, ?_⟩
  have hTe := (hT k).eventually (gt_mem_nhds hk)
  have hMe : ∀ᶠ n : ℕ in atTop, ∀ j k, |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gevEtaM (ξ₀, 0, 1) (v i) (gevEtaBasis j) (gevEtaBasis k) +
      gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k)| < e' / 3 := by
    refine eventually_all.2 fun j => eventually_all.2 fun k => ?_
    have := (hM j k).add_const (gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k))
    rw [neg_add_cancel] at this
    have h2 := this.abs
    rw [abs_zero] at h2
    exact h2.eventually (gt_mem_nhds he3)
  filter_upwards [hTe, hMe, eventually_gt_atTop 0] with n hn1 hn2 hn0
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hn'' : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  -- the average at the truth, for all directions
  have hM0 : ∀ d e : ℝ × ℝ × ℝ, |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM (ξ₀, 0, 1) (v i) d e +
      gevEtaInfo ξ₀ σ₀ d e| ≤ e' / 3 * gevEtaNorm d * gevEtaNorm e := fun d e => by
    rw [avg_gevEtaM_eq, gevEtaInfo_eq_sum ξ₀ σ₀ d e, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, ← mul_add]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ j, |∑ k, gevEtaCoord d j * gevEtaCoord e k *
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          gevEtaM (ξ₀, 0, 1) (v i) (gevEtaBasis j) (gevEtaBasis k) +
          gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k))| ≤
        |gevEtaCoord d j| * gevEtaNorm e * (e' / 3) := fun j => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |gevEtaCoord d j * gevEtaCoord e k *
            ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
              gevEtaM (ξ₀, 0, 1) (v i) (gevEtaBasis j) (gevEtaBasis k) +
              gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k))|
          ≤ ∑ k, |gevEtaCoord d j| * |gevEtaCoord e k| * (e' / 3) :=
            Finset.sum_le_sum fun k _ => by
              rw [abs_mul, abs_mul]
              exact mul_le_mul_of_nonneg_left (hn2 j k).le (by positivity)
        _ = _ := by
            rw [gevEtaNorm_eq_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    refine (Finset.sum_le_sum fun j _ => hb j).trans (le_of_eq ?_)
    rw [gevEtaNorm_eq_sum d, ← Finset.sum_mul, ← Finset.sum_mul, ← gevEtaNorm_eq_sum]
    ring
  set T := (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (v i) with hT'
  have hconst : (n : ℝ)⁻¹ * ∑ _i ∈ Finset.range n, e' / 3 = e' / 3 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  intro η hη hdist
  refine ⟨fun hu d => ?_, fun hg d e => ?_⟩
  · have hle : ∑ i ∈ Finset.range n, gevEtaM η (v i) d d ≤
        ∑ i ∈ Finset.range n, (gevEtaM (ξ₀, 0, 1) (v i) d d + (e' / 3 +
          gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (v i)) * gevEtaNorm d ^ 2) :=
      Finset.sum_le_sum fun i hi =>
        ((hδu η hη hdist (v i) (hv i)).1 (hu i (Finset.mem_range.1 hi))) d
    have h1 := mul_le_mul_of_nonneg_left hle hn''
    have e1 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (gevEtaM (ξ₀, 0, 1) (v i) d d + (e' / 3 +
        gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (v i)) * gevEtaNorm d ^ 2) =
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM (ξ₀, 0, 1) (v i) d d +
          (e' / 3 + T) * gevEtaNorm d ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib, mul_add, ← mul_assoc,
        mul_add ((n : ℝ)⁻¹), hconst]
    rw [e1] at h1
    have h2 := (abs_le.1 (hM0 d d)).2
    have hN2 := sq_nonneg (gevEtaNorm d)
    have h3 : (e' / 3 + T) * gevEtaNorm d ^ 2 ≤ (e' / 3 + e' / 3) * gevEtaNorm d ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hN2
    have e2 : e' / 3 * gevEtaNorm d * gevEtaNorm d = e' / 3 * gevEtaNorm d ^ 2 := by ring
    rw [e2] at h2
    linarith
  · have hle : ∑ i ∈ Finset.range n, |gevEtaM η (v i) d e - gevEtaM (ξ₀, 0, 1) (v i) d e| ≤
        ∑ i ∈ Finset.range n, (e' / 3 + gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (v i)) *
          (gevEtaNorm d * gevEtaNorm e) :=
      Finset.sum_le_sum fun i hi => by
        have := (hδu η hη hdist (v i) (hv i)).2 (hg i (Finset.mem_range.1 hi)).1
          (hg i (Finset.mem_range.1 hi)).2 d e
        rwa [mul_assoc] at this
    have h1 := mul_le_mul_of_nonneg_left hle hn''
    have e1 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (e' / 3 +
        gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (v i)) * (gevEtaNorm d * gevEtaNorm e) =
        (e' / 3 + T) * (gevEtaNorm d * gevEtaNorm e) := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, ← mul_assoc, mul_add, hconst]
    rw [e1] at h1
    have hNN := mul_nonneg (gevEtaNorm_nonneg d) (gevEtaNorm_nonneg e)
    have h3 : (e' / 3 + T) * (gevEtaNorm d * gevEtaNorm e) ≤
        (e' / 3 + e' / 3) * (gevEtaNorm d * gevEtaNorm e) :=
      mul_le_mul_of_nonneg_right (by linarith) hNN
    have h2 := hM0 d e
    have h4 : |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM η (v i) d e -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM (ξ₀, 0, 1) (v i) d e| ≤
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |gevEtaM η (v i) d e - gevEtaM (ξ₀, 0, 1) (v i) d e| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hn'']
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hn''
    have e5 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM η (v i) d e + gevEtaInfo ξ₀ σ₀ d e =
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM η (v i) d e -
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM (ξ₀, 0, 1) (v i) d e) +
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM (ξ₀, 0, 1) (v i) d e +
          gevEtaInfo ξ₀ σ₀ d e) := by ring
    rw [e5]
    refine (abs_add_le _ _).trans ?_
    have e6 : e' * gevEtaNorm d * gevEtaNorm e = e' * (gevEtaNorm d * gevEtaNorm e) := by ring
    have e7 : e' / 3 * gevEtaNorm d * gevEtaNorm e = e' / 3 * (gevEtaNorm d * gevEtaNorm e) := by
      ring
    rw [e6]
    rw [e7] at h2
    nlinarith

end Dev

/-! ### The rate and the linearization along a sample path -/

section Estimates

variable {ξ₀ μ₀ σ₀ ε K lam : ℝ}

/-- `Zₙ = n^{-1/2} ∑_{i<n} ∇ℓ(θ₀, xᵢ)`, in the order `(μ, σ, ξ)`. -/
noncomputable def gevPathZ (ξ₀ μ₀ σ₀ : ℝ) (x : ℕ → ℝ) (n : ℕ) : Fin 3 → ℝ :=
  fun k => (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gevScore ξ₀ μ₀ σ₀ (x i) k

/-- `Σⱼ |Zₙⱼ|`. -/
noncomputable def gevPathZNorm (ξ₀ μ₀ σ₀ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k, |gevPathZ ξ₀ μ₀ σ₀ x n k|

/-- The coordinates of the increment `θ - θ₀`, in the order `(μ, σ, ξ)`. -/
def gevThetaDiff (ξ₀ μ₀ σ₀ : ℝ) (θ : ℝ × ℝ × ℝ) : Fin 3 → ℝ :=
  ![θ.2.1 - μ₀, θ.2.2 - σ₀, θ.1 - ξ₀]

/-- The increment of the coordinates `η`. -/
noncomputable def gevEtaIncr (ξ₀ μ₀ σ₀ : ℝ) (θ : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  gevEtaOf ξ₀ μ₀ σ₀ θ - (ξ₀, 0, 1)

/-- `f ⬝ Zₙ = (√n)⁻¹ ∑ᵢ f ⬝ ∇ℓ(θ₀, xᵢ)`. -/
lemma dotProduct_gevPathZ (f : Fin 3 → ℝ) (x : ℕ → ℝ) (n : ℕ) :
    f ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n =
      (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, f ⬝ᵥ gevScore ξ₀ μ₀ σ₀ (x i) := by
  simp only [dotProduct, gevPathZ, Fin.sum_univ_three, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [← Finset.mul_sum]
  ring

/-- `|f ⬝ g| ≤ (Σ|fⱼ|) (Σ|gⱼ|)`. -/
private lemma abs_dotProduct_le (f g : Fin 3 → ℝ) :
    |f ⬝ᵥ g| ≤ (∑ j, |f j|) * ∑ j, |g j| := by
  rw [dotProduct, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact Finset.single_le_sum (f := fun j => |g j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

/-- The constant `C_J` with `Σⱼ |(J d)ⱼ| ≤ C_J |d|`. -/
noncomputable def gevJBound (ξ₀ σ₀ : ℝ) : ℝ := 1 + |σ₀ / ξ₀| * (3 + |ξ₀|)

lemma sum_abs_gevEtaJ_le (d : ℝ × ℝ × ℝ) :
    ∑ j, |gevEtaJ ξ₀ σ₀ d j| ≤ gevJBound ξ₀ σ₀ * gevEtaNorm d := by
  simp only [Fin.sum_univ_three, gevEtaJ, gevJBound, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  rw [abs_mul, abs_mul]
  set A := |σ₀ / ξ₀|
  have hA : 0 ≤ A := abs_nonneg _
  have h1 := abs_fst_le_gevEtaNorm d
  have h2 := abs_snd_fst_le_gevEtaNorm d
  have h3 := abs_snd_snd_le_gevEtaNorm d
  have hN := gevEtaNorm_nonneg d
  have a1 : |-d.2.2 - d.2.1| ≤ 2 * gevEtaNorm d := by
    refine (abs_sub _ _).trans ?_
    rw [abs_neg]
    linarith
  have a2 : |d.1 - ξ₀ * d.2.2| ≤ (1 + |ξ₀|) * gevEtaNorm d := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    nlinarith [abs_nonneg ξ₀]
  have b1 := mul_le_mul_of_nonneg_left a1 hA
  have b2 := mul_le_mul_of_nonneg_left a2 hA
  have e : (1 + A * (3 + |ξ₀|)) * gevEtaNorm d =
      A * (2 * gevEtaNorm d) + A * ((1 + |ξ₀|) * gevEtaNorm d) + gevEtaNorm d := by ring
  rw [e]
  linarith

/-- The derivative at the truth is the score. -/
private lemma sum_gevEtaD_self (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) {x : ℕ → ℝ}
    (hx : ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (x i)) {n : ℕ} (hn : 0 < n) (e : ℝ × ℝ × ℝ) :
    ∑ i ∈ Finset.range n, gevEtaD (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ (x i)) e =
      √(n : ℝ) * (gevEtaJ ξ₀ σ₀ e ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n) := by
  have hsq : (√(n : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
  rw [dotProduct_gevPathZ, mul_inv_cancel_left₀ hsq]
  exact Finset.sum_congr rfl fun i _ => gevEtaD_self_eq hξ₀0 hσ₀.ne' (hx i) e

/-- **The preliminary rate at a fixed sample size**, from the one-sided bound. -/
private lemma gevPath_rate_step (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hlam0 : 0 < lam)
    (hlam : ∀ d : ℝ × ℝ × ℝ, lam * gevEtaNorm d ^ 2 ≤ gevEtaInfo ξ₀ σ₀ d d)
    {x : ℕ → ℝ} (hx : ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (x i)) {n : ℕ} (hn : 0 < n) {Δ : ℝ × ℝ × ℝ}
    (hst : ∑ i ∈ Finset.range n, gevEtaD ((ξ₀, 0, 1) + Δ) (gevU ξ₀ μ₀ σ₀ (x i)) Δ = 0)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, gevEtaLine ξ₀ Δ s ∈ gevEtaBox ξ₀ ∧
      (gevEtaLine ξ₀ Δ s).1 ≠ 0 ∧ (gevEtaLine ξ₀ Δ s).2.2 ≠ 0)
    (hsupp : ∀ i < n, ∀ s ∈ Icc (0 : ℝ) 1, 0 < gevEtaU (gevEtaLine ξ₀ Δ s) (gevU ξ₀ μ₀ σ₀ (x i)))
    {δ : ℝ} (hNδ : gevEtaNorm Δ ≤ δ)
    (hd : ∀ η ∈ gevEtaBox ξ₀, gevEtaNorm (η - (ξ₀, 0, 1)) ≤ δ →
      (∀ i < n, 0 < gevEtaU η (gevU ξ₀ μ₀ σ₀ (x i))) → ∀ d : ℝ × ℝ × ℝ,
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM η (gevU ξ₀ μ₀ σ₀ (x i)) d d ≤
          -gevEtaInfo ξ₀ σ₀ d d + lam / 2 * gevEtaNorm d ^ 2) :
    √(n : ℝ) * gevEtaNorm Δ ≤ 2 * gevJBound ξ₀ σ₀ / lam * gevPathZNorm ξ₀ μ₀ σ₀ x n := by
  have hCJ0 : 0 ≤ gevJBound ξ₀ σ₀ := by unfold gevJBound; positivity
  obtain ⟨s, hs, hmvt⟩ := exists_sum_gevEtaM_eq (ξ₀ := ξ₀) (Δ := Δ) (e := Δ) (n := n)
    (v := fun i => gevU ξ₀ μ₀ σ₀ (x i))
    (fun s hs => ⟨(hdom s hs).2.1, (hdom s hs).2.2, fun i hi => (hsupp i hi s hs).ne'⟩)
  have hsI := Ioo_subset_Icc_self hs
  have hb := hd _ (hdom s hsI).1 ((gevEtaNorm_gevEtaLine_sub_le Δ hsI).trans hNδ)
    (fun i hi => hsupp i hi s hsI) Δ
  rw [hst, zero_sub, sum_gevEtaD_self hξ₀0 hσ₀ hx hn] at hmvt
  rw [← hmvt] at hb
  have hl := hlam Δ
  set N := gevEtaNorm Δ with hN
  have hN' : 0 ≤ N := gevEtaNorm_nonneg _
  set a := √(n : ℝ) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hn' : (n : ℝ) = a * a := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
  set Z := gevEtaJ ξ₀ σ₀ Δ ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n with hZ
  have hZ0 : 0 ≤ gevPathZNorm ξ₀ μ₀ σ₀ x n := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hZle : |Z| ≤ gevJBound ξ₀ σ₀ * N * gevPathZNorm ξ₀ μ₀ σ₀ x n :=
    (abs_dotProduct_le (gevEtaJ ξ₀ σ₀ Δ) (gevPathZ ξ₀ μ₀ σ₀ x n)).trans
      (mul_le_mul_of_nonneg_right (sum_abs_gevEtaJ_le _) hZ0)
  -- `(a N)² λ/2 ≤ a Z`
  have hmain : lam / 2 * (a * N) ^ 2 ≤ a * Z := by
    have e1 : (n : ℝ)⁻¹ * -(a * Z) ≤ -(lam / 2) * N ^ 2 := by linarith
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have e2 := mul_le_mul_of_nonneg_left e1 hnpos.le
    rw [mul_inv_cancel_left₀ hnpos.ne', hn'] at e2
    have e3 : a * a * (-(lam / 2) * N ^ 2) = -(lam / 2 * (a * N) ^ 2) := by ring
    rw [e3] at e2
    linarith
  have hZa : a * Z ≤ a * (gevJBound ξ₀ σ₀ * N * gevPathZNorm ξ₀ μ₀ σ₀ x n) :=
    mul_le_mul_of_nonneg_left ((le_abs_self Z).trans hZle) ha0.le
  rcases hN'.eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    positivity
  · have hpos : 0 < a * N := mul_pos ha0 h0
    have h7 : lam / 2 * (a * N) ≤ gevJBound ξ₀ σ₀ * gevPathZNorm ξ₀ μ₀ σ₀ x n := by
      have h8 : (lam / 2 * (a * N)) * (a * N) ≤
          (gevJBound ξ₀ σ₀ * gevPathZNorm ξ₀ μ₀ σ₀ x n) * (a * N) := by
        calc (lam / 2 * (a * N)) * (a * N) = lam / 2 * (a * N) ^ 2 := by ring
          _ ≤ a * (gevJBound ξ₀ σ₀ * N * gevPathZNorm ξ₀ μ₀ σ₀ x n) := hmain.trans hZa
          _ = _ := by ring
      exact le_of_mul_le_mul_right h8 hpos
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam0]
    linarith

/-- **The linearization of one coordinate at a fixed sample size**, from the two-sided bound:
`|√n I(Δ, e) - (J e) ⬝ Zₙ| ≤ e₂ √n |Δ| |e|`. -/
private lemma gevPath_lin_step (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    {x : ℕ → ℝ} (hx : ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (x i)) {n : ℕ} (hn : 0 < n) {Δ e : ℝ × ℝ × ℝ}
    (hst : ∑ i ∈ Finset.range n, gevEtaD ((ξ₀, 0, 1) + Δ) (gevU ξ₀ μ₀ σ₀ (x i)) e = 0)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, gevEtaLine ξ₀ Δ s ∈ gevEtaBox ξ₀ ∧
      (gevEtaLine ξ₀ Δ s).1 ≠ 0 ∧ (gevEtaLine ξ₀ Δ s).2.2 ≠ 0)
    (hgood : ∀ i < n, ∀ s ∈ Icc (0 : ℝ) 1,
      gevU ξ₀ μ₀ σ₀ (x i) / 2 ≤ gevEtaU (gevEtaLine ξ₀ Δ s) (gevU ξ₀ μ₀ σ₀ (x i)) ∧
      gevEtaU (gevEtaLine ξ₀ Δ s) (gevU ξ₀ μ₀ σ₀ (x i)) ≤ 2 * gevU ξ₀ μ₀ σ₀ (x i))
    {δ e2 : ℝ} (hNδ : gevEtaNorm Δ ≤ δ)
    (hd : ∀ η ∈ gevEtaBox ξ₀, gevEtaNorm (η - (ξ₀, 0, 1)) ≤ δ →
      (∀ i < n, gevU ξ₀ μ₀ σ₀ (x i) / 2 ≤ gevEtaU η (gevU ξ₀ μ₀ σ₀ (x i)) ∧
        gevEtaU η (gevU ξ₀ μ₀ σ₀ (x i)) ≤ 2 * gevU ξ₀ μ₀ σ₀ (x i)) → ∀ d e : ℝ × ℝ × ℝ,
        |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, gevEtaM η (gevU ξ₀ μ₀ σ₀ (x i)) d e +
          gevEtaInfo ξ₀ σ₀ d e| ≤ e2 * gevEtaNorm d * gevEtaNorm e) :
    |√(n : ℝ) * gevEtaInfo ξ₀ σ₀ Δ e - gevEtaJ ξ₀ σ₀ e ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n| ≤
      e2 * (√(n : ℝ) * gevEtaNorm Δ) * gevEtaNorm e := by
  obtain ⟨s, hs, hmvt⟩ := exists_sum_gevEtaM_eq (ξ₀ := ξ₀) (Δ := Δ) (e := e) (n := n)
    (v := fun i => gevU ξ₀ μ₀ σ₀ (x i))
    (fun s hs => ⟨(hdom s hs).2.1, (hdom s hs).2.2, fun i hi => by
      have h1 := (hgood i hi s hs).1
      have h2 := hx i
      exact (by linarith : 0 < gevEtaU (gevEtaLine ξ₀ Δ s) (gevU ξ₀ μ₀ σ₀ (x i))).ne'⟩)
  have hsI := Ioo_subset_Icc_self hs
  have hb := hd _ (hdom s hsI).1 ((gevEtaNorm_gevEtaLine_sub_le Δ hsI).trans hNδ)
    (fun i hi => hgood i hi s hsI) Δ e
  rw [hst, zero_sub, sum_gevEtaD_self hξ₀0 hσ₀ hx hn] at hmvt
  rw [← hmvt] at hb
  set a := √(n : ℝ) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hn' : (n : ℝ) = a * a := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
  set Y := gevEtaJ ξ₀ σ₀ e ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n with hY
  set J := gevEtaInfo ξ₀ σ₀ Δ e with hJ
  have e1 : (n : ℝ)⁻¹ * -(a * Y) + J = a⁻¹ * (a * J - Y) := by
    rw [hn']
    field_simp
    ring
  rw [e1, abs_mul, abs_of_pos (inv_pos.2 ha0), inv_mul_le_iff₀ ha0] at hb
  refine hb.trans (le_of_eq ?_)
  ring

/-- The information in the direction of the columns of the inverse. -/
private lemma gevEtaInfo_gevEtaJInv (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : gevFisherInfo ξ₀ σ₀ * A = 1) (d : ℝ × ℝ × ℝ) (j : Fin 3) :
    gevEtaInfo ξ₀ σ₀ d (gevEtaJInv ξ₀ σ₀ fun k => A k j) = gevEtaJ ξ₀ σ₀ d j := by
  have h1 : (gevFisherInfo ξ₀ σ₀).mulVec (fun k => A k j) = Pi.single j 1 := by
    have h2 : (fun k => A k j) = A.mulVec (Pi.single j 1) := by
      funext k
      simp
    rw [h2, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  simp only [gevEtaInfo, gevEtaJ_gevEtaJInv hξ₀0 hσ₀.ne', h1, dotProduct_single, mul_one]

/-- The final arithmetic of the linearization. -/
private lemma gevPath_lin_arith {C C₂ CA N U Z1 e' : ℝ} (hC0 : 0 ≤ C) (hC₂0 : 0 ≤ C₂)
    (hCA0 : 0 ≤ CA) (hN' : 0 ≤ N) (hZ10 : 0 ≤ Z1) (he' : 0 < e') (hUle : U ≤ C₂ * Z1)
    (hNe : N ≤ e' / (6 * (1 + C) * (1 + C₂))) :
    ((3 : ℕ) : ℝ) * C * N * U + e' / (2 * (1 + CA) * (1 + C₂)) * U * CA ≤ e' * (1 + Z1) := by
  set e2 := e' / (2 * (1 + CA) * (1 + C₂)) with he2
  have he20 : 0 < e2 := by positivity
  have h1C₂ : 0 < 1 + C₂ := by linarith
  have hC₂Z : C₂ * Z1 ≤ (1 + C₂) * Z1 := mul_le_mul_of_nonneg_right (by linarith) hZ10
  have hA1 : 3 * C * N * (1 + C₂) ≤ e' / 2 := by
    rw [le_div_iff₀ (by positivity)] at hNe
    have hNc : N * (6 * C * (1 + C₂)) ≤ N * (6 * (1 + C) * (1 + C₂)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) h1C₂.le) hN'
    have e : 3 * C * N * (1 + C₂) = N * (6 * C * (1 + C₂)) / 2 := by ring
    rw [e]
    linarith
  have hA2 : e2 * CA * (1 + C₂) ≤ e' / 2 := by
    have e3 : e2 * (2 * (1 + CA) * (1 + C₂)) = e' := by
      rw [he2]
      field_simp
    have h6 : e2 * (2 * CA * (1 + C₂)) ≤ e2 * (2 * (1 + CA) * (1 + C₂)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) h1C₂.le) he20.le
    have e : e2 * CA * (1 + C₂) = e2 * (2 * CA * (1 + C₂)) / 2 := by ring
    rw [e]
    linarith
  have hT1 : ((3 : ℕ) : ℝ) * C * N * U ≤ e' / 2 * Z1 := by
    have h7 : 0 ≤ 3 * C * N := by positivity
    push_cast
    calc 3 * C * N * U ≤ 3 * C * N * ((1 + C₂) * Z1) :=
          mul_le_mul_of_nonneg_left (hUle.trans hC₂Z) h7
      _ = 3 * C * N * (1 + C₂) * Z1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA1 hZ10
  have hT2 : e2 * U * CA ≤ e' / 2 * Z1 := by
    have h7 : 0 ≤ e2 * CA := by positivity
    calc e2 * U * CA = e2 * CA * U := by ring
      _ ≤ e2 * CA * ((1 + C₂) * Z1) := mul_le_mul_of_nonneg_left (hUle.trans hC₂Z) h7
      _ = e2 * CA * (1 + C₂) * Z1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA2 hZ10
  have e4 : e' * (1 + Z1) = e' + (e' / 2 * Z1 + e' / 2 * Z1) := by ring
  rw [e4]
  linarith

/-- What holds eventually along a path: the point `η₀ + Δₙ` is in the box and solves the
likelihood equations, the segment stays in the domain and in the support. -/
private lemma gevPath_eventually (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    {x : ℕ → ℝ} (hx : ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (x i))
    {θh : ℕ → ℝ × ℝ × ℝ} (hc : Tendsto θh atTop (𝓝 (ξ₀, μ₀, σ₀)))
    (hloc : ∀ᶠ n : ℕ in atTop, IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => x i)) (θh n))
    (hadm : ∀ᶠ n : ℕ in atTop, ∀ i < n, 0 < gevU (θh n).1 (θh n).2.1 (θh n).2.2 (x i)) :
    Tendsto (fun n => gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n))) atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop, gevThetaOf ξ₀ μ₀ σ₀ ((ξ₀, 0, 1) + gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) = θh n ∧
      (∀ e, ∑ i ∈ Finset.range n,
        gevEtaD ((ξ₀, 0, 1) + gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) (gevU ξ₀ μ₀ σ₀ (x i)) e = 0) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, gevEtaLine ξ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) s ∈ gevEtaBox ξ₀ ∧
        (gevEtaLine ξ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) s).1 ≠ 0 ∧
        (gevEtaLine ξ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) s).2.2 ≠ 0) ∧
      (∀ i < n, ∀ s ∈ Icc (0 : ℝ) 1,
        0 < gevEtaU (gevEtaLine ξ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) s) (gevU ξ₀ μ₀ σ₀ (x i))) := by
  set η₀ : ℝ × ℝ × ℝ := (ξ₀, 0, 1) with hη₀
  set Δ : ℕ → ℝ × ℝ × ℝ := fun n => gevEtaIncr ξ₀ μ₀ σ₀ (θh n) with hΔ
  have hadd : ∀ n, η₀ + Δ n = gevEtaOf ξ₀ μ₀ σ₀ (θh n) := fun n => by
    simp only [hΔ, gevEtaIncr, hη₀]
    exact add_sub_cancel _ _
  have hcη : ContinuousAt (gevEtaOf ξ₀ μ₀ σ₀) (ξ₀, μ₀, σ₀) := by
    have hσ : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) (ξ₀, μ₀, σ₀) := by fun_prop
    have hμ : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.1) (ξ₀, μ₀, σ₀) := by fun_prop
    have hξ : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1) (ξ₀, μ₀, σ₀) := by fun_prop
    have h1 : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1 * σ₀ / (ξ₀ * p.2.2)) (ξ₀, μ₀, σ₀) :=
      (hξ.mul continuousAt_const).div (continuousAt_const.mul hσ)
        (mul_ne_zero hξ₀0 hσ₀.ne')
    unfold gevEtaOf
    exact hξ.prodMk (((continuousAt_const.sub h1).add
      ((hξ.div hσ hσ₀.ne').mul (continuousAt_const.sub hμ))).prodMk h1)
  have hη : Tendsto (fun n => gevEtaOf ξ₀ μ₀ σ₀ (θh n)) atTop (𝓝 η₀) := by
    have := hcη.tendsto.comp hc
    rwa [gevEtaOf_self hξ₀0 hσ₀.ne'] at this
  have hN0 : Tendsto (fun n => gevEtaNorm (Δ n)) atTop (𝓝 0) := by
    have hcN : Continuous gevEtaNorm := by unfold gevEtaNorm; fun_prop
    have h1 : Tendsto Δ atTop (𝓝 (η₀ - η₀)) := hη.sub_const η₀
    rw [sub_self] at h1
    have h2 := (hcN.tendsto (0 : ℝ × ℝ × ℝ)).comp h1
    have h3 : gevEtaNorm 0 = 0 := by simp [gevEtaNorm]
    rw [h3] at h2
    exact h2
  refine ⟨hN0, ?_⟩
  have hbox : ∀ᶠ n in atTop, η₀ + Δ n ∈ gevEtaBox ξ₀ := by
    filter_upwards [hη.eventually (gevEtaBox_mem_nhds hξ₀0)] with n hn
    rwa [hadd]
  have hσ₁ : ∀ᶠ n in atTop, 0 < (θh n).2.2 := by
    have : Tendsto (fun n => (θh n).2.2) atTop (𝓝 σ₀) :=
      ((continuous_snd.comp continuous_snd).tendsto (ξ₀, μ₀, σ₀)).comp hc
    exact this.eventually (lt_mem_nhds hσ₀)
  filter_upwards [hloc, hadm, hbox, hσ₁] with n h1 h2 h3 h4
  obtain ⟨-, -, -, h6, h5, -, h7, -⟩ := bounds_of_mem_gevEtaBox hξ₀0 h3
  rw [hadd] at h5 h6 h7
  have h6' : (θh n).1 ≠ 0 := h6
  have h5' : 0 < (θh n).1 / ξ₀ := h5
  have hθ : gevThetaOf ξ₀ μ₀ σ₀ (gevEtaOf ξ₀ μ₀ σ₀ (θh n)) = θh n :=
    gevThetaOf_gevEtaOf hξ₀0 hσ₀.ne' h6' h4.ne'
  refine ⟨by rw [hadd]; exact hθ, fun e => ?_, fun s hs => ?_, fun i hi s hs => ?_⟩
  · rw [hadd]
    have := sum_gevEtaD_eq_zero_of_isLocalMax (μ₀ := μ₀) hξ₀0 hσ₀ (x := fun i : Fin n => x i)
      (θ := θh n) h5' h4 (fun i => h2 i i.2) h1 e
    rwa [Fin.sum_univ_eq_sum_range
      (fun i => gevEtaD (gevEtaOf ξ₀ μ₀ σ₀ (θh n)) (gevU ξ₀ μ₀ σ₀ (x i)) e) n] at this
  · have h8 := gevEtaLine_mem_gevEtaBox h3 hs
    obtain ⟨-, -, -, h9, -, -, h10, -⟩ := bounds_of_mem_gevEtaBox hξ₀0 h8
    exact ⟨h8, h9, by linarith⟩
  · rw [gevEtaU_gevEtaLine]
    have hu : 0 < gevEtaU (η₀ + Δ n) (gevU ξ₀ μ₀ σ₀ (x i)) := by
      have h9 := gevU_gevThetaOf (μ₀ := μ₀) hξ₀0 hσ₀.ne' (η := gevEtaOf ξ₀ μ₀ σ₀ (θh n)) h6
        (by linarith) (x i)
      rw [hθ] at h9
      rw [hadd, ← h9]
      exact h2 i hi
    have hvi := hx i
    rcases hs.1.eq_or_lt with h | h
    · simpa [← h] using hvi
    · have a1 := mul_pos h hu
      have a2 : 0 ≤ (1 - s) * gevU ξ₀ μ₀ σ₀ (x i) := mul_nonneg (by linarith [hs.2]) hvi.le
      linarith

/-- **The rate and the linearization along a sample path.** Let `A = I(θ₀)⁻¹` be a matrix with
`I(θ₀) A = 1`. Let `x₀, x₁, …` be a sample in the support of `θ₀` on which the averages converge
(`hM`, `hT`), and `θ̂ₙ → θ₀` estimators which for all large `n` are local maximizers at which every
observation is in the support. With `Δₙ = η(θ̂ₙ) - η₀`:

* `√n |Δₙ| ≤ (2 C_J/λ) Σⱼ |Zₙⱼ|` for all large `n`;
* for every `e' > 0`, for all large `n`, if `|Δₙ| (1 + max_{i<n} 1/v(xᵢ)) < 1/2`, then
  `Σⱼ |√n (θ̂ₙ - θ₀)ⱼ - (j-th column of A) ⬝ Zₙ| ≤ e' (1 + Σⱼ |Zₙⱼ|)`. -/
theorem gevPath_estimates (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hdev : GevEtaDev ξ₀ ε K)
    (hlam0 : 0 < lam) (hlam : ∀ d : ℝ × ℝ × ℝ, lam * gevEtaNorm d ^ 2 ≤ gevEtaInfo ξ₀ σ₀ d d)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : gevFisherInfo ξ₀ σ₀ * A = 1)
    {x : ℕ → ℝ} (hx : ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (x i))
    {θh : ℕ → ℝ × ℝ × ℝ} (hc : Tendsto θh atTop (𝓝 (ξ₀, μ₀, σ₀)))
    (hloc : ∀ᶠ n : ℕ in atTop, IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => x i)) (θh n))
    (hadm : ∀ᶠ n : ℕ in atTop, ∀ i < n, 0 < gevU (θh n).1 (θh n).2.1 (θh n).2.2 (x i))
    (hM : ∀ j k, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        gevEtaM (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ (x i)) (gevEtaBasis j) (gevEtaBasis k)) atTop
      (𝓝 (-gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k))))
    {t : ℕ → ℝ} (hT : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (gevU ξ₀ μ₀ σ₀ (x i))) atTop (𝓝 (t k)))
    (ht : Tendsto t atTop (𝓝 0)) :
    (∀ᶠ n : ℕ in atTop, √(n : ℝ) * gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) ≤
      2 * gevJBound ξ₀ σ₀ / lam * gevPathZNorm ξ₀ μ₀ σ₀ x n) ∧
    ∀ e' : ℝ, 0 < e' → ∀ᶠ n : ℕ in atTop,
      gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) *
        (1 + runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (x i)) n) < 1 / 2 →
      ∑ j, |√(n : ℝ) * gevThetaDiff ξ₀ μ₀ σ₀ (θh n) j -
          (fun k => A k j) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n| ≤
        e' * (1 + gevPathZNorm ξ₀ μ₀ σ₀ x n) := by
  have hCJ0 : 0 ≤ gevJBound ξ₀ σ₀ := by unfold gevJBound; positivity
  set C₂ := 2 * gevJBound ξ₀ σ₀ / lam with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  obtain ⟨hN0, hev⟩ := gevPath_eventually (μ₀ := μ₀) hξ₀0 hσ₀ hx hc hloc hadm
  have hNsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) ≤ δ := fun δ hδ =>
    (hN0.eventually (gt_mem_nhds hδ)).mono fun _ h => h.le
  obtain ⟨δ₁, hδ₁, hdev₁⟩ := gevPath_dev (σ₀ := σ₀) hdev hx hM hT ht (e' := lam / 2) (by positivity)
  have hrate : ∀ᶠ n : ℕ in atTop, √(n : ℝ) * gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) ≤
      C₂ * gevPathZNorm ξ₀ μ₀ σ₀ x n := by
    filter_upwards [hdev₁, hNsmall δ₁ hδ₁, hev, eventually_gt_atTop 0] with n h1 h2 h3 hn
    obtain ⟨-, h4, h5, h6⟩ := h3
    exact gevPath_rate_step hξ₀0 hσ₀ hlam0 hlam hx hn (h4 _) h5 h6 h2
      (fun η hη hd hu => (h1 η hη hd).1 hu)
  refine ⟨hrate, fun e' he' => ?_⟩
  obtain ⟨C, hC0, hC⟩ := exists_abs_gevThetaOf_sub_sub_le (μ₀ := μ₀) (σ₀ := σ₀) hξ₀0
  set E : Fin 3 → ℝ × ℝ × ℝ := fun j => gevEtaJInv ξ₀ σ₀ (fun k => A k j) with hE
  set CA := ∑ j, gevEtaNorm (E j) with hCA
  have hCA0 : 0 ≤ CA := Finset.sum_nonneg fun _ _ => gevEtaNorm_nonneg _
  set e2 := e' / (2 * (1 + CA) * (1 + C₂)) with he2
  have he20 : 0 < e2 := by positivity
  obtain ⟨δ₂, hδ₂, hdev₂⟩ := gevPath_dev (σ₀ := σ₀) hdev hx hM hT ht (e' := e2) he20
  have hsmall : 0 < min (1 / 4) (e' / (6 * (1 + C) * (1 + C₂))) := by positivity
  filter_upwards [hrate, hdev₂, hNsmall δ₂ hδ₂, hNsmall _ hsmall, hev,
    eventually_gt_atTop 0] with n h0 h1 h2 h3 h4 hn hr
  obtain ⟨hθ, hst, hdom, -⟩ := h4
  set Δ := gevEtaIncr ξ₀ μ₀ σ₀ (θh n) with hΔ
  have hN4 : gevEtaNorm Δ ≤ 1 / 4 := h3.trans (min_le_left _ _)
  have hNe : gevEtaNorm Δ ≤ e' / (6 * (1 + C) * (1 + C₂)) := h3.trans (min_le_right _ _)
  set N := gevEtaNorm Δ with hN
  have hN' : 0 ≤ N := gevEtaNorm_nonneg _
  set a := √(n : ℝ) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  set Z1 := gevPathZNorm ξ₀ μ₀ σ₀ x n with hZ1
  have hZ10 : 0 ≤ Z1 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- all observations are good along the segment
  have hgood : ∀ i < n, ∀ s ∈ Icc (0 : ℝ) 1,
      gevU ξ₀ μ₀ σ₀ (x i) / 2 ≤ gevEtaU (gevEtaLine ξ₀ Δ s) (gevU ξ₀ μ₀ σ₀ (x i)) ∧
      gevEtaU (gevEtaLine ξ₀ Δ s) (gevU ξ₀ μ₀ σ₀ (x i)) ≤ 2 * gevU ξ₀ μ₀ σ₀ (x i) :=
    fun i hi s hs => by
    refine gevEtaU_gevEtaLine_good _ hs (hx i) ?_
    have hle : 1 / gevU ξ₀ μ₀ σ₀ (x i) ≤ runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (x i)) n :=
      le_runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (x i)) hi
    have := mul_le_mul_of_nonneg_left (by linarith : 1 + 1 / gevU ξ₀ μ₀ σ₀ (x i) ≤
      1 + runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (x i)) n) hN'
    linarith
  -- each coordinate of the linearization
  have hcoord : ∀ j, |a * gevEtaJ ξ₀ σ₀ Δ j - (fun k => A k j) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n| ≤
      e2 * (a * N) * gevEtaNorm (E j) := fun j => by
    have h5 := gevPath_lin_step hξ₀0 hσ₀ hx hn (hst (E j)) hdom hgood h2
      (fun η hη hd hu => (h1 η hη hd).2 hu)
    rwa [gevEtaInfo_gevEtaJInv hξ₀0 hσ₀ hA, gevEtaJ_gevEtaJInv hξ₀0 hσ₀.ne'] at h5
  -- the remainder of the change of coordinates
  obtain ⟨r0, r1, r2⟩ := hC Δ hN4
  rw [hθ] at r0 r1 r2
  have hrem : ∀ j, |gevThetaDiff ξ₀ μ₀ σ₀ (θh n) j - gevEtaJ ξ₀ σ₀ Δ j| ≤ C * N ^ 2 := by
    intro j
    fin_cases j
    · exact r0
    · exact r1
    · have : gevThetaDiff ξ₀ μ₀ σ₀ (θh n) 2 - gevEtaJ ξ₀ σ₀ Δ 2 = 0 := r2
      change |gevThetaDiff ξ₀ μ₀ σ₀ (θh n) 2 - gevEtaJ ξ₀ σ₀ Δ 2| ≤ _
      rw [this, abs_zero]
      positivity
  have hterm : ∀ j, |a * gevThetaDiff ξ₀ μ₀ σ₀ (θh n) j -
      (fun k => A k j) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n| ≤
      a * (C * N ^ 2) + e2 * (a * N) * gevEtaNorm (E j) := fun j => by
    have e1 : a * gevThetaDiff ξ₀ μ₀ σ₀ (θh n) j - (fun k => A k j) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n =
        a * (gevThetaDiff ξ₀ μ₀ σ₀ (θh n) j - gevEtaJ ξ₀ σ₀ Δ j) +
          (a * gevEtaJ ξ₀ σ₀ Δ j - (fun k => A k j) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hcoord j))
    rw [abs_mul, abs_of_pos ha0]
    exact mul_le_mul_of_nonneg_left (hrem j) ha0.le
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  have hsum : ∑ j, e2 * (a * N) * gevEtaNorm (E j) = e2 * (a * N) * CA := by
    rw [hCA, Finset.mul_sum]
  rw [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hfin := gevPath_lin_arith (U := a * N) hC0 hC₂0 hCA0 hN' hZ10 he' h0 hNe
  refine le_trans (le_of_eq ?_) hfin
  rw [← he2]
  push_cast
  ring

end Estimates

end ExtremeValueTheory
