/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GumbelMLENormality
import ExtremeValueTheory.Statistics.GPDJointNormalityZero
import ExtremeValueTheory.Statistics.GEVReturnLevelNormality

/-!
# Three-parameter GEV maximum likelihood normality at the Gumbel boundary `ξ₀ = 0`

In `ExtremeValueTheory.Statistics.GEVMLENormality`, asymptotic normality of the three-parameter GEV
MLE is proved for `ξ₀ > -1/2`, `ξ₀ ≠ 0`. Here we treat the Gumbel boundary `ξ₀ = 0`, completing the
regular range `ξ₀ > -1/2` of [Smith 1985] and [Bücher & Segers 2017].

Using the smooth reparametrization `f(z, ξ) = -z · log1pDiv(ξ z)` (with `z = (x - μ)/σ`), the GEV
log-density `ℓ(μ, σ, ξ; x) = -log σ + (1 + ξ) f - exp f` and its first and second directional
derivatives (`gevZeroD`, `gevZeroH`) extend smoothly across `ξ = 0` on the entire admissible region
`σ > 0`, `1 + ξ z > 0`.

## Main results

* `hasDerivAt_log1pDiv`, `hasDerivAt_log1pQuad`: the exact derivative tower `log1pDiv' = -log1pQuad`
  and `log1pQuad' = log1pCube` on `(-1, ∞)`.
* `hasDerivAt_gevZeroLog_line`, `hasDerivAt_gevZeroD_line`: smooth first and second directional
  derivatives of the three-parameter GEV log-density across `ξ = 0`.
* `integral_gevZeroH_eq_neg_gevFisherInfoZero`: **the second Bartlett identity at `ξ = 0`** for all
  six entries of the `3 × 3` Hessian simultaneously, proved via an exact antiderivative on `(0, ∞)`
  without evaluating `ζ(3)`.
* `tendstoInMeasure_runMax_abs_gumbel_div_rpow`: for iid `GEV(0, μ₀, σ₀)` observations,
  `max_{i<n} |Xᵢ - μ₀| / n^α → 0` in probability for every `α > 0` (super-polynomial two-sided
  Gumbel tail).
* `tendstoInDistribution_gevLocalMLE_zero`: **asymptotic normality of three-parameter GEV local
  MLEs at `ξ₀ = 0`**: any measurable consistent sequence `θ̂ₙ = (ξ̂ₙ, μ̂ₙ, σ̂ₙ)` of interior local
  maximizers with `|ξ̂ₙ| · max_{i<n} |Xᵢ - μ₀| → 0` in probability satisfies
  `√n (ξ̂ₙ, μ̂ₙ - μ₀, σ̂ₙ - σ₀) ⇒ N(0, gevMLECovZero σ₀)`.
* `exists_gevLocalMLE_tendstoInDistribution_zero`: **unconditional existence and asymptotic
  normality** of a data-driven measurable three-parameter GEV local MLE at `ξ₀ = 0` (maximizing the
  three-parameter GEV log-likelihood over a shrinking ball of radius `n^{-1/3}` around the
  two-parameter Gumbel MLE, which lies strictly in the interior with probability tending to `1`).
* `tendstoInDistribution_gevLocalMLEReturnLevel_zero`,
  `tendsto_measure_mem_gevLocalMLEReturnLevelPlugInInterval_zero`: three-parameter GEV return-level
  normality and computable plug-in Wald confidence interval at `ξ₀ = 0`.

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72 (1985).
* A. Bücher and J. Segers, *On the maximum likelihood estimator for the Generalized Extreme-Value
  distribution*, Extremes 20 (2017).
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §3.3.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace ExtremeValueTheory

/-! ### The derivative tower for `log1pDiv` and `log1pQuad` on `(-1, ∞)` -/

section Log1pTower

lemma log1pDiv_sub_mul_log1pQuad {t : ℝ} (ht : -1 < t) :
    log1pDiv t - t * log1pQuad t = (1 + t)⁻¹ := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp [log1pDiv, log1pQuad]
  · rw [log1pDiv_of_ne h0, log1pQuad_of_ne h0]
    have h1 : 1 + t ≠ 0 := by linarith
    field_simp
    ring

lemma two_mul_log1pQuad_add_mul_log1pCube {t : ℝ} (ht : -1 < t) :
    2 * log1pQuad t + t * log1pCube t = ((1 + t) ^ 2)⁻¹ := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp [log1pQuad, log1pCube]
  · rw [log1pQuad_of_ne h0, log1pCube_of_ne h0]
    have h1 : 1 + t ≠ 0 := by linarith
    field_simp
    ring

lemma continuousAt_log1pDiv_of_gt {t : ℝ} (ht : -1 < t) : ContinuousAt log1pDiv t := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact continuousAt_log1pDiv_zero
  · have hev : log1pDiv =ᶠ[𝓝 t] fun s => log (1 + s) / s := by
      filter_upwards [isOpen_ne.mem_nhds h0] with s hs
      exact log1pDiv_of_ne hs
    refine ContinuousAt.congr ?_ hev.symm
    have h1 : (1 : ℝ) + t ≠ 0 := by linarith
    fun_prop (disch := assumption)

lemma continuousAt_log1pQuad_of_gt {t : ℝ} (ht : -1 < t) : ContinuousAt log1pQuad t := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact continuousAt_log1pQuad_zero
  · have hev : log1pQuad =ᶠ[𝓝 t] fun s => (log (1 + s) - s / (1 + s)) / s ^ 2 := by
      filter_upwards [isOpen_ne.mem_nhds h0] with s hs
      exact log1pQuad_of_ne hs
    refine ContinuousAt.congr ?_ hev.symm
    have h1 : (1 : ℝ) + t ≠ 0 := by linarith
    have h2 : t ^ 2 ≠ 0 := pow_ne_zero 2 h0
    fun_prop (disch := assumption)

lemma hasDerivAt_log1pDiv {t : ℝ} (ht : -1 < t) : HasDerivAt log1pDiv (-log1pQuad t) t := by
  have hne : ∀ s : ℝ, -1 < s → s ≠ 0 → HasDerivAt log1pDiv (-log1pQuad s) s := fun s hs h0 => by
    have hev : log1pDiv =ᶠ[𝓝 s] fun u => log (1 + u) / u := by
      filter_upwards [isOpen_ne.mem_nhds h0] with u hu
      exact log1pDiv_of_ne hu
    have h1 : (1 : ℝ) + s ≠ 0 := by linarith
    have hlog : HasDerivAt (fun u => log (1 + u)) (1 / (1 + s)) s := by
      simpa using ((hasDerivAt_id s).const_add 1).log h1
    have hd := hlog.div (hasDerivAt_id s) h0
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [log1pQuad_of_ne h0]
    simp only [id_eq]
    field_simp
    ring
  rcases eq_or_ne t 0 with rfl | h0
  · exact hasDerivAt_of_tendsto_punctured (U := Ioi (-1)) (Ioi_mem_nhds (by norm_num))
      (fun s hs hs0 => hne s hs hs0) continuousAt_log1pDiv_zero
      (continuousAt_log1pQuad_zero.neg.tendsto.mono_left nhdsWithin_le_nhds)
  · exact hne t ht h0

lemma hasDerivAt_log1pQuad {t : ℝ} (ht : -1 < t) : HasDerivAt log1pQuad (log1pCube t) t := by
  have hne : ∀ s : ℝ, -1 < s → s ≠ 0 → HasDerivAt log1pQuad (log1pCube s) s := fun s hs h0 => by
    have hev : log1pQuad =ᶠ[𝓝 s] fun u => (log (1 + u) - u / (1 + u)) / u ^ 2 := by
      filter_upwards [isOpen_ne.mem_nhds h0] with u hu
      exact log1pQuad_of_ne hu
    have h1 : (1 : ℝ) + s ≠ 0 := by linarith
    have hlog : HasDerivAt (fun u => log (1 + u)) (1 / (1 + s)) s := by
      simpa using ((hasDerivAt_id s).const_add 1).log h1
    have hrat : HasDerivAt (fun u => u / (1 + u)) (1 / (1 + s) ^ 2) s := by
      have h := (hasDerivAt_id s).div ((hasDerivAt_id s).const_add 1) h1
      refine h.congr_deriv ?_
      simp only [id_eq]; field_simp; ring
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    have hd := (hlog.sub hrat).div hsq (pow_ne_zero 2 h0)
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [log1pCube_of_ne h0]
    simp only [Pi.sub_apply]
    field_simp
    ring
  rcases eq_or_ne t 0 with rfl | h0
  · exact hasDerivAt_of_tendsto_punctured (U := Ioi (-1)) (Ioi_mem_nhds (by norm_num))
      (fun s hs hs0 => hne s hs hs0) continuousAt_log1pQuad_zero
      ((continuousAt_log1pCube (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds)
  · exact hne t ht h0

lemma abs_log1pDiv_le_of_abs_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) : |log1pDiv t| ≤ 2 := by
  rcases eq_or_ne t 0 with rfl | h0
  · simp [log1pDiv]
  have h1 : 1 / 2 ≤ 1 + t := by linarith [neg_abs_le t]
  have hpos : 0 < 1 + t := by linarith
  have hle := log_le_sub_one_of_pos hpos
  have hge := log_le_sub_one_of_pos (inv_pos.2 hpos)
  rw [log_inv] at hge
  rw [log1pDiv_of_ne h0, abs_div, div_le_iff₀ (abs_pos.2 h0)]
  rw [abs_le]
  rcases lt_or_gt_of_ne h0 with hn | hp
  · have ha : |t| = -t := abs_of_neg hn
    rw [ha]
    constructor
    · -- `-2(-t) ≤ log(1+t)`, i.e. `2t ≤ log(1+t)`: from `log(1+t) ≥ 1 - 1/(1+t) = t/(1+t) ≥ 2t` since `t < 0` and `1+t ≥ 1/2`
      have hdiv : 2 * t ≤ t / (1 + t) := by
        rw [le_div_iff₀ hpos]; nlinarith
      have : t / (1 + t) = -(1 / (1 + t) - 1) := by field_simp; ring
      linarith [show -(1 + t)⁻¹ + 1 = t / (1 + t) by field_simp; ring]
    · linarith
  · have ha : |t| = t := abs_of_pos hp
    rw [ha]
    constructor
    · have : 0 ≤ log (1 + t) := log_nonneg (by linarith)
      linarith
    · linarith

lemma abs_log1pQuad_le_of_abs_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) : |log1pQuad t| ≤ 3 := by
  have h := abs_log1pQuad_sub_le ht
  have : |log1pQuad t| - |1 / 2| ≤ |log1pQuad t - 1 / 2| := abs_sub_abs_le_abs_sub _ _
  norm_num at this
  linarith

lemma abs_log1pCube_le_of_abs_le_half {t : ℝ} (ht : |t| ≤ 1 / 2) : |log1pCube t| ≤ 5 := by
  have h := abs_log1pCube_sub_le ht
  rw [sub_neg_eq_add] at h
  have : |log1pCube t| - |-(2 / 3 : ℝ)| ≤ |log1pCube t - -(2 / 3)| := abs_sub_abs_le_abs_sub _ _
  rw [sub_neg_eq_add] at this
  norm_num at this
  linarith

end Log1pTower

/-! ### Smooth three-parameter GEV log-density and directional derivatives across `ξ = 0` -/

section SmoothGEV

/-- Standardized coordinate `z = (x - μ) / σ` for parameter `θ = (μ, σ, ξ)`. -/
noncomputable def gevZeroZ (θ : ℝ × ℝ × ℝ) (x : ℝ) : ℝ := (x - θ.1) / θ.2.1

/-- Smooth transformed exponent `f(θ; x) = -z · log1pDiv(ξ z)` agreeing with `-z` at `ξ = 0`
and with `-log(1 + ξ z)/ξ` for `ξ ≠ 0`. -/
noncomputable def gevZeroF (θ : ℝ × ℝ × ℝ) (x : ℝ) : ℝ :=
  -gevZeroZ θ x * log1pDiv (θ.2.2 * gevZeroZ θ x)

/-- Smooth three-parameter GEV log-density `ℓ(μ, σ, ξ; x) = -log σ + (1 + ξ) f - exp f`. -/
noncomputable def gevZeroLog (θ : ℝ × ℝ × ℝ) (x : ℝ) : ℝ :=
  -log θ.2.1 + (1 + θ.2.2) * gevZeroF θ x - exp (gevZeroF θ x)

/-- Agreement of `gevZeroLog` with `log (gevLocScaleDensity ξ μ σ x)` on the admissible region. -/
lemma gevZeroLog_eq_log_density {θ : ℝ × ℝ × ℝ} {x : ℝ} (hσ : 0 < θ.2.1)
    (hu : 0 < 1 + θ.2.2 * gevZeroZ θ x) :
    gevZeroLog θ x = log (gevLocScaleDensity θ.2.2 θ.1 θ.2.1 x) := by
  rcases eq_or_ne θ.2.2 0 with hξ | hξ
  · simp only [gevZeroLog, gevZeroF, gevZeroZ, hξ, zero_mul, log1pDiv_zero, mul_one, add_zero,
      one_mul]
    rw [log_gevLocScaleDensity_zero hσ]
    ring
  · have hfg : gevZeroF θ x = -log (1 + θ.2.2 * gevZeroZ θ x) / θ.2.2 := by
      rw [gevZeroF, neg_mul, mul_log1pDiv_eq hξ hu]
      ring
    have hexp : exp (gevZeroF θ x) = (1 + θ.2.2 * gevZeroZ θ x) ^ (-1 / θ.2.2) := by
      rw [hfg, rpow_def_of_pos hu]
      congr 1; ring
    have hd : gevLocScaleDensity θ.2.2 θ.1 θ.2.1 x =
        θ.2.1⁻¹ * ((1 + θ.2.2 * gevZeroZ θ x) ^ (-1 / θ.2.2 - 1) *
          exp (-((1 + θ.2.2 * gevZeroZ θ x) ^ (-1 / θ.2.2)))) := by
      have hu' : 0 < 1 + θ.2.2 * ((x - θ.1) / θ.2.1) := hu
      simp only [gevLocScaleDensity, gevDensity, gevZeroZ, hξ, ↓reduceIte, hu']
    rw [hd, log_mul (inv_pos.2 hσ).ne' (by positivity), log_inv,
      log_mul (by positivity) (exp_pos _).ne', log_rpow hu, log_exp, gevZeroLog, hexp, hfg]
    field_simp [hξ]
    ring

/-- First directional derivative of `z = (x - μ)/σ` in direction `v = (v_μ, v_σ, v_ξ)`. -/
noncomputable def gevZeroZ' (θ v : ℝ × ℝ × ℝ) (x : ℝ) : ℝ :=
  -(v.1 + gevZeroZ θ x * v.2.1) / θ.2.1

/-- Second directional derivative of `z = (x - μ)/σ` in directions `v, w`. -/
noncomputable def gevZeroZ'' (θ v w : ℝ × ℝ × ℝ) (x : ℝ) : ℝ :=
  (v.2.1 * (w.1 + gevZeroZ θ x * w.2.1) + w.2.1 * (v.1 + gevZeroZ θ x * v.2.1)) / θ.2.1 ^ 2

/-- First directional derivative of `f(θ; x)` in direction `v`. -/
noncomputable def gevZeroF' (θ v : ℝ × ℝ × ℝ) (x : ℝ) : ℝ :=
  -gevZeroZ' θ v x / (1 + θ.2.2 * gevZeroZ θ x) +
    gevZeroZ θ x ^ 2 * log1pQuad (θ.2.2 * gevZeroZ θ x) * v.2.2

/-- Second directional derivative of `f(θ; x)` in directions `v, w`. -/
noncomputable def gevZeroF'' (θ v w : ℝ × ℝ × ℝ) (x : ℝ) : ℝ :=
  (θ.2.2 * gevZeroZ' θ v x * gevZeroZ' θ w x +
      gevZeroZ θ x * (gevZeroZ' θ v x * w.2.2 + gevZeroZ' θ w x * v.2.2)) /
      (1 + θ.2.2 * gevZeroZ θ x) ^ 2 +
    gevZeroZ θ x ^ 3 * log1pCube (θ.2.2 * gevZeroZ θ x) * (v.2.2 * w.2.2) -
    gevZeroZ'' θ v w x / (1 + θ.2.2 * gevZeroZ θ x)

/-- First directional derivative of the GEV log-density `ℓ` across `ξ = 0`. -/
noncomputable def gevZeroD (θ v : ℝ × ℝ × ℝ) (x : ℝ) : ℝ :=
  -v.2.1 / θ.2.1 + v.2.2 * gevZeroF θ x + (1 + θ.2.2 - exp (gevZeroF θ x)) * gevZeroF' θ v x

/-- Second directional derivative (symmetric Hessian bilinear form) of `ℓ` across `ξ = 0`. -/
noncomputable def gevZeroH (θ v w : ℝ × ℝ × ℝ) (x : ℝ) : ℝ :=
  v.2.1 * w.2.1 / θ.2.1 ^ 2 + v.2.2 * gevZeroF' θ w x + w.2.2 * gevZeroF' θ v x +
    (1 + θ.2.2 - exp (gevZeroF θ x)) * gevZeroF'' θ v w x -
    exp (gevZeroF θ x) * (gevZeroF' θ v x * gevZeroF' θ w x)

/-- Parameter-space step `θ + s • v`. -/
def gevStep (θ v : ℝ × ℝ × ℝ) (s : ℝ) : ℝ × ℝ × ℝ :=
  (θ.1 + s * v.1, θ.2.1 + s * v.2.1, θ.2.2 + s * v.2.2)

/-- Basis vectors in `(μ, σ, ξ)` coordinates. -/
def gevZeroBasis (i : Fin 3) : ℝ × ℝ × ℝ :=
  match i with
  | ⟨0, _⟩ => (1, 0, 0)
  | ⟨1, _⟩ => (0, 1, 0)
  | ⟨2, _⟩ => (0, 0, 1)

lemma gevZeroD_zero_eq_gumbelScore (μ σ : ℝ) (v : ℝ × ℝ × ℝ) (x : ℝ) :
    gevZeroD (μ, σ, 0) v x =
      v.1 * gumbelScoreMu μ σ x + v.2.1 * gumbelScoreSigma μ σ x + v.2.2 * gumbelScoreXi μ σ x := by
  simp only [gevZeroD, gevZeroF, gevZeroF', gevZeroZ', gevZeroZ, zero_mul, log1pDiv_zero,
    log1pQuad, ↓reduceIte, add_zero, div_one, mul_one, gumbelScoreMu, gumbelScoreSigma,
    gumbelScoreXi]
  ring

lemma gevZeroD_basis_zero (μ σ x : ℝ) (i : Fin 3) :
    gevZeroD (μ, σ, 0) (gevZeroBasis i) x = gumbelScoreVec3 μ σ x i := by
  rw [gevZeroD_zero_eq_gumbelScore]
  fin_cases i <;> simp [gevZeroBasis, gumbelScoreVec3]

lemma gevZeroD_eq_sum (θ v : ℝ × ℝ × ℝ) (x : ℝ) :
    gevZeroD θ v x =
      v.1 * gevZeroD θ (gevZeroBasis 0) x + v.2.1 * gevZeroD θ (gevZeroBasis 1) x +
        v.2.2 * gevZeroD θ (gevZeroBasis 2) x := by
  simp only [gevZeroD, gevZeroF', gevZeroZ', gevZeroBasis]
  ring

lemma gevZeroH_eq_sum (θ v w : ℝ × ℝ × ℝ) (x : ℝ) :
    gevZeroH θ v w x =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (![v.1, v.2.1, v.2.2] i) * (![w.1, w.2.1, w.2.2] j) *
          gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) x := by
  have hb0 : gevZeroBasis 0 = (1, 0, 0) := rfl
  have hb1 : gevZeroBasis 1 = (0, 1, 0) := rfl
  have hb2 : gevZeroBasis 2 = (0, 0, 1) := rfl
  simp only [Fin.sum_univ_three, hb0, hb1, hb2, gevZeroH, gevZeroF', gevZeroF'', gevZeroZ', gevZeroZ'',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

lemma hasDerivAt_gevZeroZ_line {θ v : ℝ × ℝ × ℝ} {x s : ℝ} (hσ : 0 < (gevStep θ v s).2.1) :
    HasDerivAt (fun r => gevZeroZ (gevStep θ v r) x) (gevZeroZ' (gevStep θ v s) v x) s := by
  have hnum : HasDerivAt (fun r => x - (θ.1 + r * v.1)) (-v.1) s := by
    simpa using (((hasDerivAt_id s).mul_const v.1).const_add θ.1).const_sub x
  have hden : HasDerivAt (fun r => θ.2.1 + r * v.2.1) v.2.1 s := by
    simpa using ((hasDerivAt_id s).mul_const v.2.1).const_add θ.2.1
  have hd := hnum.div hden hσ.ne'
  refine hd.congr_deriv ?_
  simp only [gevZeroZ', gevZeroZ, gevStep]
  have hne : θ.2.1 + s * v.2.1 ≠ 0 := hσ.ne'
  field_simp
  ring

lemma hasDerivAt_gevZeroZ'_line {θ v w : ℝ × ℝ × ℝ} {x s : ℝ} (hσ : 0 < (gevStep θ v s).2.1) :
    HasDerivAt (fun r => gevZeroZ' (gevStep θ v r) w x) (gevZeroZ'' (gevStep θ v s) v w x) s := by
  have hz := hasDerivAt_gevZeroZ_line (θ := θ) (v := v) (x := x) hσ
  have hden : HasDerivAt (fun r => θ.2.1 + r * v.2.1) v.2.1 s := by
    simpa using ((hasDerivAt_id s).mul_const v.2.1).const_add θ.2.1
  have hnum : HasDerivAt (fun r => -(w.1 + gevZeroZ (gevStep θ v r) x * w.2.1))
      (-(gevZeroZ' (gevStep θ v s) v x * w.2.1)) s :=
    ((hz.mul_const w.2.1).const_add w.1).neg
  have hd := hnum.div hden hσ.ne'
  refine hd.congr_deriv ?_
  simp only [gevZeroZ'', gevZeroZ', gevZeroZ, gevStep]
  have hne : θ.2.1 + s * v.2.1 ≠ 0 := hσ.ne'
  field_simp
  ring

lemma hasDerivAt_gevZeroF_line {θ v : ℝ × ℝ × ℝ} {x s : ℝ} (hσ : 0 < (gevStep θ v s).2.1)
    (hu : 0 < 1 + (gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x) :
    HasDerivAt (fun r => gevZeroF (gevStep θ v r) x) (gevZeroF' (gevStep θ v s) v x) s := by
  have hz := hasDerivAt_gevZeroZ_line (θ := θ) (v := v) (x := x) hσ
  have hξ : HasDerivAt (fun r => θ.2.2 + r * v.2.2) v.2.2 s := by
    simpa using ((hasDerivAt_id s).mul_const v.2.2).const_add θ.2.2
  have ht : HasDerivAt (fun r => (gevStep θ v r).2.2 * gevZeroZ (gevStep θ v r) x)
      (v.2.2 * gevZeroZ (gevStep θ v s) x + (gevStep θ v s).2.2 * gevZeroZ' (gevStep θ v s) v x) s :=
    hξ.mul hz
  have hgt : -1 < (gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x := by linarith
  have hld := (hasDerivAt_log1pDiv hgt).comp s ht
  have hd : HasDerivAt (fun r => gevZeroF (gevStep θ v r) x) _ s := hz.neg.mul hld
  refine hd.congr_deriv ?_
  have hid := log1pDiv_sub_mul_log1pQuad hgt
  simp only [gevZeroF', gevStep, Pi.neg_apply] at hid ⊢
  rw [div_eq_mul_inv, ← hid]
  ring

/-- **First directional derivative of the GEV log-density across `ξ = 0`**. -/
theorem hasDerivAt_gevZeroLog_line {θ v : ℝ × ℝ × ℝ} {x s : ℝ} (hσ : 0 < (gevStep θ v s).2.1)
    (hu : 0 < 1 + (gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x) :
    HasDerivAt (fun r => gevZeroLog (gevStep θ v r) x) (gevZeroD (gevStep θ v s) v x) s := by
  have hσd : HasDerivAt (fun r => θ.2.1 + r * v.2.1) v.2.1 s := by
    simpa using ((hasDerivAt_id s).mul_const v.2.1).const_add θ.2.1
  have hξd : HasDerivAt (fun r => 1 + (θ.2.2 + r * v.2.2)) v.2.2 s := by
    simpa using (((hasDerivAt_id s).mul_const v.2.2).const_add θ.2.2).const_add 1
  have hf := hasDerivAt_gevZeroF_line (θ := θ) (v := v) (x := x) hσ hu
  have hd := ((hσd.log hσ.ne').neg.add (hξd.mul hf)).sub hf.exp
  refine hd.congr_deriv ?_
  simp only [gevZeroD, gevStep]
  ring

lemma hasDerivAt_gevZeroF'_line {θ v w : ℝ × ℝ × ℝ} {x s : ℝ} (hσ : 0 < (gevStep θ v s).2.1)
    (hu : 0 < 1 + (gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x) :
    HasDerivAt (fun r => gevZeroF' (gevStep θ v r) w x) (gevZeroF'' (gevStep θ v s) v w x) s := by
  have hz := hasDerivAt_gevZeroZ_line (θ := θ) (v := v) (x := x) hσ
  have hz' := hasDerivAt_gevZeroZ'_line (θ := θ) (v := v) (w := w) (x := x) hσ
  have hξ : HasDerivAt (fun r => θ.2.2 + r * v.2.2) v.2.2 s := by
    simpa using ((hasDerivAt_id s).mul_const v.2.2).const_add θ.2.2
  have ht : HasDerivAt (fun r => (gevStep θ v r).2.2 * gevZeroZ (gevStep θ v r) x)
      (v.2.2 * gevZeroZ (gevStep θ v s) x + (gevStep θ v s).2.2 * gevZeroZ' (gevStep θ v s) v x) s :=
    hξ.mul hz
  have hu_d := ht.const_add 1
  have hgt : -1 < (gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x := by linarith
  have hq := (hasDerivAt_log1pQuad hgt).comp s ht
  have h1 : HasDerivAt (fun r => -gevZeroZ' (gevStep θ v r) w x /
      (1 + (gevStep θ v r).2.2 * gevZeroZ (gevStep θ v r) x)) _ s :=
    hz'.neg.div hu_d hu.ne'
  have h2 : HasDerivAt (fun r => gevZeroZ (gevStep θ v r) x ^ 2 *
      log1pQuad ((gevStep θ v r).2.2 * gevZeroZ (gevStep θ v r) x) * w.2.2) _ s :=
    ((hz.pow 2).mul hq).mul_const w.2.2
  have hd : HasDerivAt (fun r => gevZeroF' (gevStep θ v r) w x) _ s := h1.add h2
  refine hd.congr_deriv ?_
  have hid := two_mul_log1pQuad_add_mul_log1pCube hgt
  have hu' : 1 + (gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x ≠ 0 := hu.ne'
  have hmul : (2 * log1pQuad ((gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x) +
      (gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x *
        log1pCube ((gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x)) *
      (1 + (gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x) ^ 2 = 1 := by
    rw [hid, inv_mul_cancel₀ (pow_ne_zero 2 hu')]
  simp only [gevZeroF'', gevStep, Function.comp_apply, Pi.neg_apply, Pi.pow_apply, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one] at hmul hu' ⊢
  field_simp [hu']
  linear_combination
    w.2.2 * gevZeroZ (θ.1 + s * v.1, θ.2.1 + s * v.2.1, θ.2.2 + s * v.2.2) x *
      gevZeroZ' (θ.1 + s * v.1, θ.2.1 + s * v.2.1, θ.2.2 + s * v.2.2) v x * hmul

/-- **Second directional derivative of the GEV log-density across `ξ = 0`**. -/
theorem hasDerivAt_gevZeroD_line {θ v w : ℝ × ℝ × ℝ} {x s : ℝ} (hσ : 0 < (gevStep θ v s).2.1)
    (hu : 0 < 1 + (gevStep θ v s).2.2 * gevZeroZ (gevStep θ v s) x) :
    HasDerivAt (fun r => gevZeroD (gevStep θ v r) w x) (gevZeroH (gevStep θ v s) v w x) s := by
  have hσd : HasDerivAt (fun r => θ.2.1 + r * v.2.1) v.2.1 s := by
    simpa using ((hasDerivAt_id s).mul_const v.2.1).const_add θ.2.1
  have hξd : HasDerivAt (fun r => θ.2.2 + r * v.2.2) v.2.2 s := by
    simpa using ((hasDerivAt_id s).mul_const v.2.2).const_add θ.2.2
  have hf := hasDerivAt_gevZeroF_line (θ := θ) (v := v) (x := x) hσ hu
  have hf' := hasDerivAt_gevZeroF'_line (θ := θ) (v := v) (w := w) (x := x) hσ hu
  have h1 : HasDerivAt (fun r => -w.2.1 / (θ.2.1 + r * v.2.1))
      (v.2.1 * w.2.1 / (θ.2.1 + s * v.2.1) ^ 2) s := by
    have h := (hasDerivAt_const s (-w.2.1)).div hσd hσ.ne'
    refine h.congr_deriv ?_; field_simp [hσ.ne']; ring
  have h2 := hf.const_mul w.2.2
  have h3 : HasDerivAt (fun r => (1 + (gevStep θ v r).2.2 - exp (gevZeroF (gevStep θ v r) x)) *
      gevZeroF' (gevStep θ v r) w x) _ s :=
    ((hξd.const_add 1).sub hf.exp).mul hf'
  have hd : HasDerivAt (fun r => gevZeroD (gevStep θ v r) w x) _ s := (h1.add h2).add h3
  refine hd.congr_deriv ?_
  simp only [gevZeroH, gevStep, Pi.sub_apply]
  ring

/-- At an interior local maximizer of `gevLogLikE` where all observations lie in the support, all
three smooth score components vanish (covering both `ξ ≠ 0` and `ξ = 0`). -/
theorem sum_gevZeroD_eq_zero_of_isLocalMax {n : ℕ} {x : Fin n → ℝ} {θ : ℝ × ℝ × ℝ}
    (hσ : 0 < θ.2.1) (hadm : ∀ i, 0 < 1 + θ.2.2 * gevZeroZ θ (x i))
    (hloc : IsLocalMax (fun p : ℝ × ℝ × ℝ => gevLogLikE p.2.2 p.1 p.2.1 x) θ) (v : ℝ × ℝ × ℝ) :
    ∑ i, gevZeroD θ v (x i) = 0 := by
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < (gevStep θ v r).2.1 ∧
      ∀ i, 0 < 1 + (gevStep θ v r).2.2 * gevZeroZ (gevStep θ v r) (x i) := by
    refine ((show Continuous fun r => (gevStep θ v r).2.1 by unfold gevStep; fun_prop).continuousAt.eventually
      (lt_mem_nhds (by simpa [gevStep] using hσ))).and (eventually_all.2 fun i => ?_)
    have hc : ContinuousAt (fun r => 1 + (gevStep θ v r).2.2 * gevZeroZ (gevStep θ v r) (x i)) 0 := by
      unfold gevStep gevZeroZ
      fun_prop (disch := simpa using hσ.ne')
    exact hc.eventually (lt_mem_nhds (by simpa [gevStep] using hadm i))
  have hstep : Tendsto (gevStep θ v) (𝓝 (0 : ℝ)) (𝓝 θ) := by
    have hc : Continuous (gevStep θ v) := by unfold gevStep; fun_prop
    simpa [gevStep] using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hle : ∀ᶠ r in 𝓝 (0 : ℝ), ∑ i, gevZeroLog (gevStep θ v r) (x i) ≤ ∑ i, gevZeroLog θ (x i) := by
    filter_upwards [hnear, hstep.eventually hloc] with r hr hmax
    have heq_r : gevLogLikE (gevStep θ v r).2.2 (gevStep θ v r).1 (gevStep θ v r).2.1 x =
        ((∑ i, gevZeroLog (gevStep θ v r) (x i) : ℝ) : EReal) := by
      rw [gevLogLikE, ereal_coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gevZeroLog_eq_log_density hr.1 (hr.2 i)]
      have hpos : 0 < gevLocScaleDensity (gevStep θ v r).2.2 (gevStep θ v r).1
          (gevStep θ v r).2.1 (x i) := by
        rcases eq_or_ne (gevStep θ v r).2.2 0 with h0 | h0
        · simp only [gevLocScaleDensity, gevDensity, h0, ↓reduceIte]
          have := hr.1; positivity
        · exact gevLocScaleDensity_pos hr.1 h0 (hr.2 i)
      simp [gevLogDensityE, hpos]
    have heq_0 : gevLogLikE θ.2.2 θ.1 θ.2.1 x = ((∑ i, gevZeroLog θ (x i) : ℝ) : EReal) := by
      rw [gevLogLikE, ereal_coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gevZeroLog_eq_log_density hσ (hadm i)]
      have hpos : 0 < gevLocScaleDensity θ.2.2 θ.1 θ.2.1 (x i) := by
        rcases eq_or_ne θ.2.2 0 with h0 | h0
        · simp only [gevLocScaleDensity, gevDensity, h0, ↓reduceIte]; positivity
        · exact gevLocScaleDensity_pos hσ h0 (hadm i)
      simp [gevLogDensityE, hpos]
    change gevLogLikE (gevStep θ v r).2.2 (gevStep θ v r).1 (gevStep θ v r).2.1 x ≤
      gevLogLikE θ.2.2 θ.1 θ.2.1 x at hmax
    rw [heq_r, heq_0] at hmax
    exact EReal.coe_le_coe_iff.1 hmax
  have hloc0 : IsLocalMax (fun r => ∑ i, gevZeroLog (gevStep θ v r) (x i)) 0 := by
    have h0 : gevStep θ v 0 = θ := by simp [gevStep]
    exact hle.mono fun r hr => by simpa [h0] using hr
  have hd : HasDerivAt (fun r => ∑ i, gevZeroLog (gevStep θ v r) (x i))
      (∑ i, gevZeroD θ v (x i)) 0 := by
    have h := HasDerivAt.sum (u := Finset.univ) fun i _ =>
      hasDerivAt_gevZeroLog_line (θ := θ) (v := v) (x := x i) (s := 0)
        (by simpa [gevStep] using hσ) (by simpa [gevStep] using hadm i)
    have h0 : gevStep θ v 0 = θ := by simp [gevStep]
    rw [show (∑ i : Fin n, gevZeroD (gevStep θ v 0) v (x i)) = ∑ i : Fin n, gevZeroD θ v (x i) by
      simp [h0]] at h
    convert h using 1
    funext r; simp
  exact hloc0.hasDerivAt_eq_zero hd

end SmoothGEV

/-! ### The second Bartlett identity at `ξ = 0` (exact antiderivative, no `ζ(3)` needed) -/

section BartlettZero

lemma measurable_gevZeroH_zero (μ σ : ℝ) (v w : ℝ × ℝ × ℝ) :
    Measurable (fun x => gevZeroH (μ, σ, 0) v w x) := by
  simp only [gevZeroH, gevZeroF, gevZeroF', gevZeroF'', gevZeroZ', gevZeroZ'', gevZeroZ,
    zero_mul, add_zero, zero_add, div_one, one_pow, log1pDiv_zero, log1pQuad, log1pCube, ↓reduceIte]
  fun_prop

set_option maxHeartbeats 400000 in
lemma integrable_gevZeroH_zero {μ σ : ℝ} (hσ : 0 < σ) (v w : ℝ × ℝ × ℝ) :
    Integrable (fun x => gevZeroH (μ, σ, 0) v w x) (gevLocScaleCDF 0 μ hσ).measure := by
  rw [integrable_gevLocScaleCDF_iff hσ (measurable_gevZeroH_zero μ σ v w)]
  have hdom : IntegrableOn (fun t : ℝ =>
      exp (-t) * ((1 + t) * (1 + |log t| ^ 4))) (Ioi 0) volume := by
    have h00 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow (a := 0) (by norm_num) 0
    have h04 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow (a := 0) (by norm_num) 4
    have h10 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow (a := 1) (by norm_num) 0
    have h14 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow (a := 1) (by norm_num) 4
    refine ((h00.add h04).add (h10.add h14)).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, rpow_zero, rpow_one, pow_zero, mul_one]; ring
  set a := |v.1 / σ| + |v.2.1 / σ| + |v.2.2| + 1
  set b := |w.1 / σ| + |w.2.1 / σ| + |w.2.2| + 1
  have hmeas_t : Measurable fun t : ℝ =>
      exp (-t) * gevZeroH (μ, σ, 0) v w (μ + σ * gevTransform 0 t) := by
    have htr : Measurable fun t : ℝ => μ + σ * gevTransform 0 t := by
      simp only [gevTransform, ↓reduceIte]; fun_prop
    exact (continuous_exp.comp continuous_neg).measurable.mul
      ((measurable_gevZeroH_zero μ σ v w).comp htr)
  refine (hdom.const_mul (45 * a * b)).mono' hmeas_t.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hz : gevZeroZ (μ, σ, 0) (μ + σ * gevTransform 0 t) = -log t := by
    simp [gevZeroZ, gevTransform]; field_simp [hσ.ne']
  have hexp : exp (-(-log t)) = t := by rw [neg_neg, exp_log ht0]
  have h1 : |v.1 / σ| ≤ a := by simp only [a]; linarith [abs_nonneg (v.2.1 / σ), abs_nonneg v.2.2]
  have h2 : |v.2.1 / σ| ≤ a := by simp only [a]; linarith [abs_nonneg (v.1 / σ), abs_nonneg v.2.2]
  have h3 : |v.2.2| ≤ a := by simp only [a]; linarith [abs_nonneg (v.1 / σ), abs_nonneg (v.2.1 / σ)]
  have k1 : |w.1 / σ| ≤ b := by simp only [b]; linarith [abs_nonneg (w.2.1 / σ), abs_nonneg w.2.2]
  have k2 : |w.2.1 / σ| ≤ b := by simp only [b]; linarith [abs_nonneg (w.1 / σ), abs_nonneg w.2.2]
  have k3 : |w.2.2| ≤ b := by simp only [b]; linarith [abs_nonneg (w.1 / σ), abs_nonneg (w.2.1 / σ)]
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set L := |log t|
  have hL0 : 0 ≤ L := abs_nonneg _
  have hL1 : L ≤ 1 + L ^ 4 := by nlinarith [sq_nonneg (L - 1), sq_nonneg (L ^ 2 - 1)]
  have hL2 : L ^ 2 ≤ 1 + L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 1)]
  have hL3 : L ^ 3 ≤ 1 + L ^ 4 := by nlinarith [sq_nonneg (L - 1), sq_nonneg (L ^ 2 - 1), mul_nonneg hL0 (sq_nonneg (L - 1))]
  have hL4 : L ^ 4 ≤ 1 + L ^ 4 := by linarith
  have hF'v : |gevZeroF' (μ, σ, 0) v (μ + σ * gevTransform 0 t)| ≤ 3 * a * (1 + L ^ 2) := by
    have heq : gevZeroF' (μ, σ, 0) v (μ + σ * gevTransform 0 t) =
        v.1 / σ + v.2.1 / σ * (-log t) + v.2.2 * ((-log t) ^ 2 / 2) := by
      simp only [gevZeroF', gevZeroZ', hz, zero_mul, add_zero, div_one, log1pQuad, ↓reduceIte]
      ring
    rw [heq]
    calc |v.1 / σ + v.2.1 / σ * (-log t) + v.2.2 * ((-log t) ^ 2 / 2)|
        ≤ |v.1 / σ| + |v.2.1 / σ| * L + |v.2.2| * (L ^ 2 / 2) := by
          have := abs_add_le (v.1 / σ + v.2.1 / σ * (-log t)) (v.2.2 * ((-log t) ^ 2 / 2))
          have := abs_add_le (v.1 / σ) (v.2.1 / σ * (-log t))
          simp only [abs_mul, abs_neg, abs_div, abs_pow, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at *
          linarith
      _ ≤ a + a * (1 + L ^ 2) + a * (1 + L ^ 2) := by
          have hL12 : L ≤ 1 + L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
          have : |v.2.1 / σ| * L ≤ a * (1 + L ^ 2) := mul_le_mul h2 hL12 hL0 ha0
          have : |v.2.2| * (L ^ 2 / 2) ≤ a * (1 + L ^ 2) := mul_le_mul h3 (by nlinarith) (by positivity) ha0
          linarith
      _ ≤ 3 * a * (1 + L ^ 2) := by nlinarith
  have hF'w : |gevZeroF' (μ, σ, 0) w (μ + σ * gevTransform 0 t)| ≤ 3 * b * (1 + L ^ 2) := by
    have heq : gevZeroF' (μ, σ, 0) w (μ + σ * gevTransform 0 t) =
        w.1 / σ + w.2.1 / σ * (-log t) + w.2.2 * ((-log t) ^ 2 / 2) := by
      simp only [gevZeroF', gevZeroZ', hz, zero_mul, add_zero, div_one, log1pQuad, ↓reduceIte]
      ring
    rw [heq]
    calc |w.1 / σ + w.2.1 / σ * (-log t) + w.2.2 * ((-log t) ^ 2 / 2)|
        ≤ |w.1 / σ| + |w.2.1 / σ| * L + |w.2.2| * (L ^ 2 / 2) := by
          have := abs_add_le (w.1 / σ + w.2.1 / σ * (-log t)) (w.2.2 * ((-log t) ^ 2 / 2))
          have := abs_add_le (w.1 / σ) (w.2.1 / σ * (-log t))
          simp only [abs_mul, abs_neg, abs_div, abs_pow, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at *
          linarith
      _ ≤ b + b * (1 + L ^ 2) + b * (1 + L ^ 2) := by
          have hL12 : L ≤ 1 + L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
          have : |w.2.1 / σ| * L ≤ b * (1 + L ^ 2) := mul_le_mul k2 hL12 hL0 hb0
          have : |w.2.2| * (L ^ 2 / 2) ≤ b * (1 + L ^ 2) := mul_le_mul k3 (by nlinarith) (by positivity) hb0
          linarith
      _ ≤ 3 * b * (1 + L ^ 2) := by nlinarith
  have hF'' : |gevZeroF'' (μ, σ, 0) v w (μ + σ * gevTransform 0 t)| ≤ 9 * a * b * (1 + L ^ 4) := by
    have heq : gevZeroF'' (μ, σ, 0) v w (μ + σ * gevTransform 0 t) =
        (-log t) * (-(v.1 / σ + v.2.1 / σ * (-log t)) * w.2.2 -
          (w.1 / σ + w.2.1 / σ * (-log t)) * v.2.2) -
        2 / 3 * (-log t) ^ 3 * (v.2.2 * w.2.2) -
        (v.2.1 / σ * (w.1 / σ + w.2.1 / σ * (-log t)) +
          w.2.1 / σ * (v.1 / σ + v.2.1 / σ * (-log t))) := by
      simp only [gevZeroF'', gevZeroZ', gevZeroZ'', hz, zero_mul, add_zero, zero_add, one_pow,
        div_one, log1pCube, ↓reduceIte]
      ring
    rw [heq]
    have hp1 : |v.1 / σ + v.2.1 / σ * (-log t)| ≤ a * (1 + L) := by
      calc |v.1 / σ + v.2.1 / σ * (-log t)|
          ≤ |v.1 / σ| + |v.2.1 / σ| * L := by
            have := abs_add_le (v.1 / σ) (v.2.1 / σ * (-log t))
            simpa [abs_mul, abs_neg] using this
        _ ≤ a + a * L := add_le_add h1 (mul_le_mul_of_nonneg_right h2 hL0)
        _ = a * (1 + L) := by ring
    have hp2 : |w.1 / σ + w.2.1 / σ * (-log t)| ≤ b * (1 + L) := by
      calc |w.1 / σ + w.2.1 / σ * (-log t)|
          ≤ |w.1 / σ| + |w.2.1 / σ| * L := by
            have := abs_add_le (w.1 / σ) (w.2.1 / σ * (-log t))
            simpa [abs_mul, abs_neg] using this
        _ ≤ b + b * L := add_le_add k1 (mul_le_mul_of_nonneg_right k2 hL0)
        _ = b * (1 + L) := by ring
    have hL1L : L * (1 + L) ≤ 2 * (1 + L ^ 4) := by linarith
    have h1L : 1 + L ≤ 2 * (1 + L ^ 4) := by linarith [pow_nonneg hL0 4]
    have t1 : |(-log t) * (-(v.1 / σ + v.2.1 / σ * (-log t)) * w.2.2 -
        (w.1 / σ + w.2.1 / σ * (-log t)) * v.2.2)| ≤ 4 * a * b * (1 + L ^ 4) := by
      rw [abs_mul, abs_neg]
      have hi : |-(v.1 / σ + v.2.1 / σ * (-log t)) * w.2.2 -
          (w.1 / σ + w.2.1 / σ * (-log t)) * v.2.2| ≤ 2 * a * b * (1 + L) := by
        have hsub := abs_sub (-(v.1 / σ + v.2.1 / σ * (-log t)) * w.2.2)
          ((w.1 / σ + w.2.1 / σ * (-log t)) * v.2.2)
        have hA : |-(v.1 / σ + v.2.1 / σ * (-log t)) * w.2.2| ≤ a * (1 + L) * b := by
          rw [abs_mul, abs_neg]; exact mul_le_mul hp1 k3 (abs_nonneg _) (by positivity)
        have hB : |(w.1 / σ + w.2.1 / σ * (-log t)) * v.2.2| ≤ b * (1 + L) * a := by
          rw [abs_mul]; exact mul_le_mul hp2 h3 (abs_nonneg _) (by positivity)
        linarith
      calc L * |-(v.1 / σ + v.2.1 / σ * (-log t)) * w.2.2 -
            (w.1 / σ + w.2.1 / σ * (-log t)) * v.2.2|
          ≤ L * (2 * a * b * (1 + L)) := mul_le_mul_of_nonneg_left hi hL0
        _ = 2 * a * b * (L * (1 + L)) := by ring
        _ ≤ 2 * a * b * (2 * (1 + L ^ 4)) := mul_le_mul_of_nonneg_left hL1L (by positivity)
        _ = 4 * a * b * (1 + L ^ 4) := by ring
    have t2 : |2 / 3 * (-log t) ^ 3 * (v.2.2 * w.2.2)| ≤ a * b * (1 + L ^ 4) := by
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_mul,
        abs_of_pos (show (0 : ℝ) < 2 / 3 by norm_num)]
      have hvw : |v.2.2| * |w.2.2| ≤ a * b := mul_le_mul h3 k3 (abs_nonneg _) ha0
      have : 2 / 3 * L ^ 3 * (|v.2.2| * |w.2.2|) ≤ (1 + L ^ 4) * (a * b) :=
        mul_le_mul (by linarith [pow_nonneg hL0 3]) hvw (by positivity) (by positivity)
      linarith
    have t3 : |v.2.1 / σ * (w.1 / σ + w.2.1 / σ * (-log t)) +
        w.2.1 / σ * (v.1 / σ + v.2.1 / σ * (-log t))| ≤ 4 * a * b * (1 + L ^ 4) := by
      have hA : |v.2.1 / σ * (w.1 / σ + w.2.1 / σ * (-log t))| ≤ a * (b * (1 + L)) := by
        rw [abs_mul]; exact mul_le_mul h2 hp2 (abs_nonneg _) ha0
      have hB : |w.2.1 / σ * (v.1 / σ + v.2.1 / σ * (-log t))| ≤ b * (a * (1 + L)) := by
        rw [abs_mul]; exact mul_le_mul k2 hp1 (abs_nonneg _) hb0
      have hsum := (abs_add_le _ _).trans (add_le_add hA hB)
      have h21 : 2 * a * b * (1 + L) ≤ 2 * a * b * (2 * (1 + L ^ 4)) :=
        mul_le_mul_of_nonneg_left h1L (by positivity)
      linarith
    have htri := (abs_sub
      ((-log t) * (-(v.1 / σ + v.2.1 / σ * (-log t)) * w.2.2 -
        (w.1 / σ + w.2.1 / σ * (-log t)) * v.2.2) -
       2 / 3 * (-log t) ^ 3 * (v.2.2 * w.2.2))
      (v.2.1 / σ * (w.1 / σ + w.2.1 / σ * (-log t)) +
        w.2.1 / σ * (v.1 / σ + v.2.1 / σ * (-log t)))).trans
      (add_le_add (abs_sub _ _) le_rfl)
    linarith only [htri, t1, t2, t3]
  -- Combine all terms in `gevZeroH`
  have hHbd : |gevZeroH (μ, σ, 0) v w (μ + σ * gevTransform 0 t)| ≤
      45 * a * b * ((1 + t) * (1 + L ^ 4)) := by
    have h0 : gevZeroF (μ, σ, 0) (μ + σ * gevTransform 0 t) = -(-log t) := by
      simp [gevZeroF, hz, log1pDiv_zero]
    rw [gevZeroH, h0, hexp]
    dsimp only
    have h1t : |1 + (0 : ℝ) - t| ≤ 1 + t := by
      rw [add_zero]; calc |1 - t| ≤ |(1 : ℝ)| + |t| := abs_sub _ _
        _ = 1 + t := by rw [abs_one, abs_of_pos ht0]
    have hsq : (1 + L ^ 2) ^ 2 ≤ 2 * (1 + L ^ 4) := by nlinarith only [sq_nonneg (1 - L ^ 2)]
    have hL24 : 1 + L ^ 2 ≤ 2 * (1 + L ^ 4) := by linarith only [hL2, pow_nonneg hL0 4]
    have c1 : |v.2.1 * w.2.1 / σ ^ 2| ≤ a * b := by
      rw [show v.2.1 * w.2.1 / σ ^ 2 = (v.2.1 / σ) * (w.2.1 / σ) by ring, abs_mul]
      exact mul_le_mul h2 k2 (abs_nonneg _) ha0
    have c2 : |v.2.2 * gevZeroF' (μ, σ, 0) w (μ + σ * gevTransform 0 t)| ≤ 6 * a * b * (1 + L ^ 4) := by
      rw [abs_mul]
      calc |v.2.2| * |gevZeroF' (μ, σ, 0) w (μ + σ * gevTransform 0 t)|
          ≤ a * (3 * b * (1 + L ^ 2)) := mul_le_mul h3 hF'w (abs_nonneg _) ha0
        _ = 3 * a * b * (1 + L ^ 2) := by ring
        _ ≤ 3 * a * b * (2 * (1 + L ^ 4)) := mul_le_mul_of_nonneg_left hL24 (by positivity)
        _ = 6 * a * b * (1 + L ^ 4) := by ring
    have c3 : |w.2.2 * gevZeroF' (μ, σ, 0) v (μ + σ * gevTransform 0 t)| ≤ 6 * a * b * (1 + L ^ 4) := by
      rw [abs_mul]
      calc |w.2.2| * |gevZeroF' (μ, σ, 0) v (μ + σ * gevTransform 0 t)|
          ≤ b * (3 * a * (1 + L ^ 2)) := mul_le_mul k3 hF'v (abs_nonneg _) hb0
        _ = 3 * a * b * (1 + L ^ 2) := by ring
        _ ≤ 3 * a * b * (2 * (1 + L ^ 4)) := mul_le_mul_of_nonneg_left hL24 (by positivity)
        _ = 6 * a * b * (1 + L ^ 4) := by ring
    have c4 : |(1 + (0 : ℝ) - t) * gevZeroF'' (μ, σ, 0) v w (μ + σ * gevTransform 0 t)| ≤
        9 * a * b * ((1 + t) * (1 + L ^ 4)) := by
      rw [abs_mul]
      calc |1 + (0 : ℝ) - t| * |gevZeroF'' (μ, σ, 0) v w (μ + σ * gevTransform 0 t)|
          ≤ (1 + t) * (9 * a * b * (1 + L ^ 4)) := mul_le_mul h1t hF'' (abs_nonneg _) (by positivity)
        _ = 9 * a * b * ((1 + t) * (1 + L ^ 4)) := by ring
    have c5 : |t * (gevZeroF' (μ, σ, 0) v (μ + σ * gevTransform 0 t) *
        gevZeroF' (μ, σ, 0) w (μ + σ * gevTransform 0 t))| ≤
        18 * a * b * ((1 + t) * (1 + L ^ 4)) := by
      rw [abs_mul, abs_mul, abs_of_pos ht0]
      have hprod := mul_le_mul hF'v hF'w (abs_nonneg _) (by positivity)
      have h9t : 9 * a * b * t ≤ 9 * a * b * (1 + t) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc t * (|gevZeroF' (μ, σ, 0) v (μ + σ * gevTransform 0 t)| *
            |gevZeroF' (μ, σ, 0) w (μ + σ * gevTransform 0 t)|)
          ≤ t * (3 * a * (1 + L ^ 2) * (3 * b * (1 + L ^ 2))) := mul_le_mul_of_nonneg_left hprod ht0.le
        _ = 9 * a * b * t * (1 + L ^ 2) ^ 2 := by ring
        _ ≤ 9 * a * b * (1 + t) * (2 * (1 + L ^ 4)) :=
            mul_le_mul h9t hsq (sq_nonneg _) (by positivity)
        _ = 18 * a * b * ((1 + t) * (1 + L ^ 4)) := by ring
    have htri := (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add c1 c2)) c3)) c4)) c5)
    have h1le : 1 ≤ (1 + t) * (1 + L ^ 4) := by nlinarith only [ht0, pow_nonneg hL0 4]
    have hLle : 1 + L ^ 4 ≤ (1 + t) * (1 + L ^ 4) := by nlinarith only [ht0, pow_nonneg hL0 4]
    have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
    have h1ab : a * b ≤ a * b * ((1 + t) * (1 + L ^ 4)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h1le hab
    have hLab : a * b * (1 + L ^ 4) ≤ a * b * ((1 + t) * (1 + L ^ 4)) :=
      mul_le_mul_of_nonneg_left hLle hab
    have h6 : 6 * a * b * (1 + L ^ 4) ≤ 6 * (a * b * ((1 + t) * (1 + L ^ 4))) := by
      have := mul_le_mul_of_nonneg_left hLab (show (0 : ℝ) ≤ 6 by norm_num)
      linarith only [this]
    have h40 : 40 * (a * b * ((1 + t) * (1 + L ^ 4))) ≤ 45 * a * b * ((1 + t) * (1 + L ^ 4)) := by
      have : 0 ≤ a * b * ((1 + t) * (1 + L ^ 4)) := mul_nonneg hab (by linarith only [h1le])
      linarith only [this]
    linarith only [htri, h1ab, h6, h40]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  calc exp (-t) * |gevZeroH (μ, σ, 0) v w (μ + σ * gevTransform 0 t)|
      ≤ exp (-t) * (45 * a * b * ((1 + t) * (1 + L ^ 4))) :=
        mul_le_mul_of_nonneg_left hHbd (exp_pos _).le
    _ = 45 * a * b * (exp (-t) * ((1 + t) * (1 + L ^ 4))) := by ring

private lemma tendsto_mul_log_pow_zero (k : ℕ) :
    Tendsto (fun t : ℝ => t * (log t) ^ k) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  have hlog : Tendsto (fun t : ℝ => -log t) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  have hc := (h.comp hlog).const_mul ((-1 : ℝ) ^ k)
  rw [mul_zero] at hc
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  simp only [Function.comp_apply, neg_neg, exp_log ht0]
  rw [← mul_assoc, ← mul_pow, show (-1 : ℝ) * -log t = log t by ring, mul_comm]

private lemma tendsto_exp_neg_mul_rpow_log_pow_atTop (m k : ℕ) :
    Tendsto (fun t : ℝ => exp (-t) * t ^ m * (log t) ^ k) atTop (𝓝 0) := by
  have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero (m + k)
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hl0 : 0 ≤ log t := log_nonneg ht
  have hlt : log t ≤ t := by linarith [log_le_sub_one_of_pos ht0]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_nonneg (pow_nonneg ht0.le _),
    abs_of_nonneg (pow_nonneg hl0 _), pow_add]
  have hpk : (log t) ^ k ≤ t ^ k := pow_le_pow_left₀ hl0 hlt k
  calc exp (-t) * t ^ m * (log t) ^ k ≤ exp (-t) * t ^ m * t ^ k :=
        mul_le_mul_of_nonneg_left hpk (by positivity)
    _ = t ^ m * t ^ k * exp (-t) := by ring

/-- **Quadratic form Bartlett identity at `ξ = 0`**:
`E_{GEV(0, μ, σ)}[gevZeroH(v, v)] = -vᵀ gevFisherInfoZero(σ) v`,
proved via an exact antiderivative on `(0, ∞)` without evaluating `ζ(3)`. -/
theorem integral_gevZeroH_self_eq_neg {μ σ : ℝ} (hσ : 0 < σ) (v : ℝ × ℝ × ℝ) :
    ∫ x, gevZeroH (μ, σ, 0) v v x ∂(gevLocScaleCDF 0 μ hσ).measure =
      -(![v.1, v.2.1, v.2.2] ⬝ᵥ gevFisherInfoZero σ *ᵥ ![v.1, v.2.1, v.2.2]) := by
  set a := v.1 / σ
  set b := v.2.1 / σ
  set c := v.2.2
  have hsq := integral_lin_gumbelScore3_sq (μ := μ) hσ ![v.1, v.2.1, v.2.2]
  have hint_H := integrable_gevZeroH_zero (μ := μ) hσ v v
  have hint_S : Integrable (fun x => (gevZeroD (μ, σ, 0) v x) ^ 2)
      (gevLocScaleCDF 0 μ hσ).measure := by
    have hmem := (memLp_lin_gumbelScore3 (μ := μ) hσ v.1 v.2.1 v.2.2).integrable_sq
    refine hmem.congr (ae_of_all _ fun x => ?_)
    dsimp only
    rw [gevZeroD_zero_eq_gumbelScore]
  have hsum_eq : ∫ x, (gevZeroH (μ, σ, 0) v v x + (gevZeroD (μ, σ, 0) v x) ^ 2)
      ∂(gevLocScaleCDF 0 μ hσ).measure = 0 := by
    have hm : Measurable (fun x => gevZeroH (μ, σ, 0) v v x + (gevZeroD (μ, σ, 0) v x) ^ 2) := by
      have h1 := measurable_gevZeroH_zero μ σ v v
      have h2 : Measurable (fun x => gevZeroD (μ, σ, 0) v x) := by
        simp_rw [gevZeroD_zero_eq_gumbelScore]
        have := measurable_gumbelScoreMu μ σ; have := measurable_gumbelScoreSigma μ σ
        have := measurable_gumbelScoreXi μ σ; fun_prop
      fun_prop
    rw [integral_gevLocScaleCDF hσ hm]
    -- Define the exact antiderivative `Q(t) = -e^{-t} * t * ((t - 1) (fp t)² - fpp t)`
    set fp : ℝ → ℝ := fun t => a - b * log t + c / 2 * (log t) ^ 2
    set fpp : ℝ → ℝ := fun t => -2 * (b - c * log t) * (a - b * log t) + 2 / 3 * c ^ 2 * (log t) ^ 3
    set Q : ℝ → ℝ := fun t => -exp (-t) * t * ((t - 1) * (fp t) ^ 2 - fpp t)
    have hderiv : ∀ t ∈ Ioi (0 : ℝ),
        HasDerivAt Q (exp (-t) * (gevZeroH (μ, σ, 0) v v (μ + σ * gevTransform 0 t) +
          (gevZeroD (μ, σ, 0) v (μ + σ * gevTransform 0 t)) ^ 2)) t := by
      intro t ht
      have ht0 : 0 < t := ht
      have hlog : HasDerivAt log (1 / t) t := by simpa [one_div] using Real.hasDerivAt_log ht0.ne'
      have hfp : HasDerivAt fp ((-b + c * log t) / t) t := by
        have h1 := (hasDerivAt_const t a).sub (hlog.const_mul b)
        have h2 := (hlog.pow 2).const_mul (c / 2)
        refine (h1.add h2).congr_deriv ?_
        field_simp [ht0.ne']; ring
      have hfpp : HasDerivAt fpp
          ((2 * c * (a - b * log t) + 2 * b * (b - c * log t) + 2 * c ^ 2 * (log t) ^ 2) / t) t := by
        have h1 : HasDerivAt (fun u => -2 * (b - c * log u)) (-2 * (0 - c * (1 / t))) t :=
          ((hasDerivAt_const t b).sub (hlog.const_mul c)).const_mul (-2)
        have h2 : HasDerivAt (fun u => a - b * log u) (0 - b * (1 / t)) t :=
          (hasDerivAt_const t a).sub (hlog.const_mul b)
        have h3 : HasDerivAt (fun u => 2 / 3 * c ^ 2 * (log u) ^ 3)
            (2 / 3 * c ^ 2 * (3 * (log t) ^ 2 * (1 / t))) t := by
          simpa using (hlog.pow 3).const_mul (2 / 3 * c ^ 2)
        refine ((h1.mul h2).add h3).congr_deriv ?_
        field_simp [ht0.ne']; ring
      have hexp : HasDerivAt (fun u => -exp (-u) * u) (exp (-t) * (t - 1)) t := by
        have h1 : HasDerivAt (fun u => -exp (-u)) (exp (-t)) t := by
          have := (hasDerivAt_id t).neg.exp.neg
          refine this.congr_deriv ?_; simp only [Pi.neg_apply, id_eq]; ring
        have h := h1.mul (hasDerivAt_id t)
        refine h.congr_deriv ?_; simp only [id_eq]; ring
      have hA : HasDerivAt (fun u => (u - 1) * (fp u) ^ 2 - fpp u)
          ((fp t) ^ 2 + (t - 1) * (2 * fp t * ((-b + c * log t) / t)) -
            (2 * c * (a - b * log t) + 2 * b * (b - c * log t) + 2 * c ^ 2 * (log t) ^ 2) / t) t := by
        have h1 : HasDerivAt (fun u => (u - 1) * (fp u) ^ 2)
            (1 * (fp t) ^ 2 + (t - 1) * (2 * fp t * ((-b + c * log t) / t))) t := by
          have hfp2 : HasDerivAt (fun u => (fp u) ^ 2) (2 * fp t * ((-b + c * log t) / t)) t :=
            (hfp.pow 2).congr_deriv (by ring)
          exact ((hasDerivAt_id t).sub_const 1).mul hfp2
        refine (h1.sub hfpp).congr_deriv ?_; ring
      have hd := hexp.mul hA
      refine hd.congr_deriv ?_
      have hz : gevZeroZ (μ, σ, 0) (μ + σ * gevTransform 0 t) = -log t := by
        simp [gevZeroZ, gevTransform]; field_simp [hσ.ne']
      have he : exp (-(-log t)) = t := by rw [neg_neg, exp_log ht0]
      have hHval : gevZeroH (μ, σ, 0) v v (μ + σ * gevTransform 0 t) =
          b ^ 2 + 2 * c * fp t + (1 - t) * fpp t - t * (fp t) ^ 2 := by
        simp only [gevZeroH, gevZeroF, gevZeroF', gevZeroF'', gevZeroZ', gevZeroZ'', hz, zero_mul,
          add_zero, zero_add, log1pDiv_zero, log1pQuad, log1pCube, ↓reduceIte, mul_one, div_one,
          one_pow, he, fp, fpp, a, b, c]
        field_simp [hσ.ne']
        ring
      have hDval : gevZeroD (μ, σ, 0) v (μ + σ * gevTransform 0 t) =
          (1 - t) * fp t - (b - c * log t) := by
        simp only [gevZeroD, gevZeroF, gevZeroF', gevZeroZ', hz, zero_mul, add_zero, log1pDiv_zero,
          log1pQuad, ↓reduceIte, mul_one, div_one, he, fp, a, b, c]
        field_simp [hσ.ne']
        ring
      rw [hHval, hDval]
      simp only [fp, fpp]
      field_simp [ht0.ne']
      ring
    have hQ0 : Tendsto Q (𝓝[>] 0) (𝓝 0) := by
      have hpoly : Tendsto (fun t : ℝ => t * ((t - 1) * (fp t) ^ 2 - fpp t)) (𝓝[>] 0) (𝓝 0) := by
        have h0 := tendsto_mul_log_pow_zero 0
        have h1 := tendsto_mul_log_pow_zero 1
        have h2 := tendsto_mul_log_pow_zero 2
        have h3 := tendsto_mul_log_pow_zero 3
        have h4 := tendsto_mul_log_pow_zero 4
        have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
          tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
        have ht1 : Tendsto (fun t : ℝ => t - 1) (𝓝[>] 0) (𝓝 (-1)) := by
          simpa using ht0.sub_const 1
        have hfp_t : Tendsto (fun t : ℝ => t * (fp t) ^ 2) (𝓝[>] 0) (𝓝 0) := by
          have hc := (((h0.const_mul (a ^ 2)).add (h1.const_mul (-2 * a * b))).add
            ((h2.const_mul (b ^ 2 + a * c)).add (h3.const_mul (-b * c)))).add
            (h4.const_mul (c ^ 2 / 4))
          have hc0 : (a ^ 2 * 0 + -2 * a * b * 0 + ((b ^ 2 + a * c) * 0 + -b * c * 0) +
              c ^ 2 / 4 * 0 : ℝ) = 0 := by ring
          rw [hc0] at hc
          refine hc.congr fun t => ?_
          simp only [fp]; ring
        have hfpp_t : Tendsto (fun t : ℝ => t * fpp t) (𝓝[>] 0) (𝓝 0) := by
          have hc := ((h0.const_mul (-2 * a * b)).add (h1.const_mul (2 * b ^ 2 + 2 * a * c))).add
            ((h2.const_mul (-2 * b * c)).add (h3.const_mul (2 / 3 * c ^ 2)))
          have hc0 : (-2 * a * b * 0 + (2 * b ^ 2 + 2 * a * c) * 0 +
              (-2 * b * c * 0 + 2 / 3 * c ^ 2 * 0) : ℝ) = 0 := by ring
          rw [hc0] at hc
          refine hc.congr fun t => ?_
          simp only [fpp]; ring
        have hcomb := (ht1.mul hfp_t).sub hfpp_t
        simp only [mul_zero, sub_zero] at hcomb
        refine hcomb.congr fun t => by ring
      have hexp0 : Tendsto (fun t : ℝ => -exp (-t)) (𝓝[>] 0) (𝓝 (-1)) := by
        have hc : ContinuousAt (fun t : ℝ => -exp (-t)) 0 := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      have := hexp0.mul hpoly
      simp only [mul_zero] at this
      refine this.congr fun t => by simp only [Q]; ring
    have hQinf : Tendsto Q atTop (𝓝 0) := by
      have hterm : ∀ m k : ℕ, Tendsto (fun t : ℝ => exp (-t) * t ^ m * (log t) ^ k) atTop (𝓝 0) :=
        tendsto_exp_neg_mul_rpow_log_pow_atTop
      have hA : Tendsto (fun t : ℝ => exp (-t) * t * ((t - 1) * (fp t) ^ 2)) atTop (𝓝 0) := by
        have hp2 := (((((hterm 2 0).const_mul (a ^ 2)).add ((hterm 2 1).const_mul (-2 * a * b))).add
          (((hterm 2 2).const_mul (b ^ 2 + a * c)).add ((hterm 2 3).const_mul (-b * c)))).add
          ((hterm 2 4).const_mul (c ^ 2 / 4)))
        have hp1 := (((((hterm 1 0).const_mul (a ^ 2)).add ((hterm 1 1).const_mul (-2 * a * b))).add
          (((hterm 1 2).const_mul (b ^ 2 + a * c)).add ((hterm 1 3).const_mul (-b * c)))).add
          ((hterm 1 4).const_mul (c ^ 2 / 4)))
        have hdiff := hp2.sub hp1
        have h0 : (a ^ 2 * 0 + -2 * a * b * 0 + ((b ^ 2 + a * c) * 0 + -b * c * 0) + c ^ 2 / 4 * 0 -
            (a ^ 2 * 0 + -2 * a * b * 0 + ((b ^ 2 + a * c) * 0 + -b * c * 0) + c ^ 2 / 4 * 0) : ℝ) = 0 := by ring
        rw [h0] at hdiff
        refine hdiff.congr fun t => ?_; simp only [fp]; ring
      have hB : Tendsto (fun t : ℝ => exp (-t) * t * fpp t) atTop (𝓝 0) := by
        have hc := ((((hterm 1 0).const_mul (-2 * a * b)).add
          ((hterm 1 1).const_mul (2 * b ^ 2 + 2 * a * c))).add
          (((hterm 1 2).const_mul (-2 * b * c)).add ((hterm 1 3).const_mul (2 / 3 * c ^ 2))))
        have h0 : (-2 * a * b * 0 + (2 * b ^ 2 + 2 * a * c) * 0 +
            (-2 * b * c * 0 + 2 / 3 * c ^ 2 * 0) : ℝ) = 0 := by ring
        rw [h0] at hc
        refine hc.congr fun t => ?_; simp only [fpp]; ring
      have hcomb := (hA.sub hB).neg
      simp only [sub_zero, neg_zero] at hcomb
      refine hcomb.congr fun t => by simp only [Q]; ring
    set g : ℝ → ℝ := fun t => exp (-t) * (gevZeroH (μ, σ, 0) v v (μ + σ * gevTransform 0 t) +
      (gevZeroD (μ, σ, 0) v (μ + σ * gevTransform 0 t)) ^ 2)
    have hint_t : IntegrableOn g (Ioi 0) volume :=
      (integrable_gevLocScaleCDF_iff hσ hm).1 (hint_H.add hint_S)
    have hIoi_eps : ∀ ε : ℝ, 0 < ε → ∫ t in Ioi ε, g t = 0 - Q ε := fun ε hε =>
      integral_Ioi_of_hasDerivAt_of_tendsto (hderiv ε hε).continuousAt.continuousWithinAt
        (fun t ht => hderiv t (hε.trans ht)) (hint_t.mono_set (Ioi_subset_Ioi hε.le)) hQinf
    have hlim1 : Tendsto (fun n : ℕ => ∫ t in Ioi (1 / ((n : ℝ) + 1)), g t) atTop (𝓝 0) := by
      have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          tendsto_one_div_add_atTop_nhds_zero_nat
          (Eventually.of_forall fun n => mem_Ioi.2 (by positivity))
      have h1 := (hQ0.comp hseq).const_sub 0
      rw [sub_zero] at h1
      refine h1.congr fun n => (hIoi_eps _ (by positivity)).symm
    have hlim2 : Tendsto (fun n : ℕ => ∫ t in Ioi (1 / ((n : ℝ) + 1)), g t) atTop
        (𝓝 (∫ t in Ioi (0 : ℝ), g t)) := by
      have heq : ∀ n : ℕ, ∫ t in Ioi (1 / ((n : ℝ) + 1)), g t =
          ∫ t in Ioi (0 : ℝ), (Ioi (1 / ((n : ℝ) + 1))).indicator g t := fun n => by
        rw [setIntegral_indicator measurableSet_Ioi,
          inter_eq_self_of_subset_right (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) by positivity))]
      simp_rw [heq]
      refine tendsto_integral_of_dominated_convergence (fun t => ‖g t‖)
        (fun n => (hint_t.aestronglyMeasurable.indicator measurableSet_Ioi))
        hint_t.norm (fun n => ae_of_all _ fun t => ?_) ?_
      · by_cases h : t ∈ Ioi (1 / ((n : ℝ) + 1))
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
          (gt_mem_nhds (mem_Ioi.1 ht))] with n hn
        exact (Set.indicator_of_mem hn g).symm
    exact tendsto_nhds_unique hlim2 hlim1
  rw [integral_add hint_H hint_S] at hsum_eq
  have hS_eq : ∫ x, (gevZeroD (μ, σ, 0) v x) ^ 2 ∂(gevLocScaleCDF 0 μ hσ).measure =
      ![v.1, v.2.1, v.2.2] ⬝ᵥ gevFisherInfoZero σ *ᵥ ![v.1, v.2.1, v.2.2] := by
    rw [← hsq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [gevZeroD_zero_eq_gumbelScore]
    simp
  linarith

/-- **The second Bartlett identity at `ξ = 0` for every entry `(i, j)` of the `3 × 3` Hessian**:
`E_{GEV(0, μ, σ)}[∂_i ∂_j ℓ(μ, σ, 0; X)] = -gevFisherInfoZero(σ)_{ij}`. -/
theorem integral_gevZeroH_eq_neg_gevFisherInfoZero {μ σ : ℝ} (hσ : 0 < σ) (i j : Fin 3) :
    ∫ x, gevZeroH (μ, σ, 0) (gevZeroBasis i) (gevZeroBasis j) x ∂(gevLocScaleCDF 0 μ hσ).measure =
      -gevFisherInfoZero σ i j := by
  set u := gevZeroBasis i
  set w := gevZeroBasis j
  set uv : ℝ × ℝ × ℝ := (u.1 + w.1, u.2.1 + w.2.1, u.2.2 + w.2.2)
  have hpol : ∀ x, gevZeroH (μ, σ, 0) u w x =
      (gevZeroH (μ, σ, 0) uv uv x - gevZeroH (μ, σ, 0) u u x - gevZeroH (μ, σ, 0) w w x) / 2 := by
    intro x
    simp only [gevZeroH, gevZeroF', gevZeroF'', gevZeroZ', gevZeroZ'', uv]
    ring
  simp_rw [hpol]
  have h1 := integrable_gevZeroH_zero (μ := μ) hσ uv uv
  have h2 := integrable_gevZeroH_zero (μ := μ) hσ u u
  have h3 := integrable_gevZeroH_zero (μ := μ) hσ w w
  have h12 : Integrable (fun x => gevZeroH (μ, σ, 0) uv uv x - gevZeroH (μ, σ, 0) u u x)
      (gevLocScaleCDF 0 μ hσ).measure := h1.sub h2
  rw [integral_div, integral_sub h12 h3, integral_sub h1 h2,
    integral_gevZeroH_self_eq_neg hσ uv, integral_gevZeroH_self_eq_neg hσ u,
    integral_gevZeroH_self_eq_neg hσ w]
  have hsym : ∀ a b : Fin 3, gevFisherInfoZero σ a b = gevFisherInfoZero σ b a := fun a b => by
    have := (posDef_gevFisherInfoZero hσ).isHermitian
    have h := congrFun (congrFun this b) a
    simpa [Matrix.conjTranspose_apply] using h
  fin_cases i <;> fin_cases j <;>
    simp [u, w, uv, gevZeroBasis, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
      hsym 1 0, hsym 2 0, hsym 2 1] <;>
    ring

end BartlettZero

/-! ### Super-polynomial two-sided maximum bound for Gumbel observations -/

section GumbelRunMax

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- For a `GEV(0, μ₀, σ₀)` random variable, `P(|(X - μ₀)/σ₀| ≥ s) ≤ 2 e^{-s/2}` for `s ≥ 0`. -/
lemma measure_gumbel_abs_ge_le {μ₀ σ₀ s : ℝ} (hσ₀ : 0 < σ₀) (hs : 0 ≤ s) :
    (gevLocScaleCDF 0 μ₀ hσ₀).measure {x | s ≤ |(x - μ₀) / σ₀|} ≤
      ENNReal.ofReal (2 * exp (-s / 2)) := by
  set ν := (gevLocScaleCDF 0 μ₀ hσ₀).measure
  have hsub : {x : ℝ | s ≤ |(x - μ₀) / σ₀|} ⊆
      Iic (μ₀ - σ₀ * (s / 2)) ∪ Ioi (μ₀ + σ₀ * (s / 2)) := by
    intro x hx
    simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_Ioi] at hx ⊢
    rcases eq_or_lt_of_le hs with rfl | hspos
    · rcases le_or_gt x μ₀ with h | h
      · left; linarith
      · right; linarith
    · rcases le_abs.1 hx with h | h
      · right; rw [le_div_iff₀ hσ₀] at h; nlinarith
      · left; rw [← neg_div, le_div_iff₀ hσ₀] at h; nlinarith
  have hleft : ν (Iic (μ₀ - σ₀ * (s / 2))) ≤ ENNReal.ofReal (exp (-s / 2)) := by
    have hm := (gevLocScaleCDF 0 μ₀ hσ₀).measure_Iic (μ₀ - σ₀ * (s / 2))
    rw [show ν (Iic (μ₀ - σ₀ * (s / 2))) = ENNReal.ofReal (gevLocScaleCDF 0 μ₀ hσ₀ (μ₀ - σ₀ * (s / 2)))
      from hm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hval : gevLocScaleCDF 0 μ₀ hσ₀ (μ₀ - σ₀ * (s / 2)) = exp (-exp (s / 2)) := by
      simp only [gevLocScaleCDF_apply, gevFun, ↓reduceIte]
      congr 3; field_simp [hσ₀.ne']; ring
    rw [hval]
    refine exp_le_exp.2 ?_
    linarith [add_one_le_exp (s / 2)]
  have hright : ν (Ioi (μ₀ + σ₀ * (s / 2))) ≤ ENNReal.ofReal (exp (-s / 2)) := by
    have hIic := (gevLocScaleCDF 0 μ₀ hσ₀).measure_Iic (μ₀ + σ₀ * (s / 2))
    have hcompl : Ioi (μ₀ + σ₀ * (s / 2)) = (Iic (μ₀ + σ₀ * (s / 2)))ᶜ := by ext x; simp
    rw [hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ]
    have hval : gevLocScaleCDF 0 μ₀ hσ₀ (μ₀ + σ₀ * (s / 2)) = exp (-exp (-s / 2)) := by
      simp only [gevLocScaleCDF_apply, gevFun, ↓reduceIte]
      congr 3; field_simp [hσ₀.ne']; ring
    change 1 - (gevLocScaleCDF 0 μ₀ hσ₀).measure (Iic (μ₀ + σ₀ * (s / 2))) ≤ _
    rw [hIic, hval, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [add_one_le_exp (-exp (-s / 2))]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  calc ν (Iic (μ₀ - σ₀ * (s / 2))) + ν (Ioi (μ₀ + σ₀ * (s / 2)))
      ≤ ENNReal.ofReal (exp (-s / 2)) + ENNReal.ofReal (exp (-s / 2)) :=
        add_le_add hleft hright
    _ = ENNReal.ofReal (2 * exp (-s / 2)) := by
        rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le, two_mul]

omit [IsProbabilityMeasure P] in
/-- For iid `GEV(0, μ₀, σ₀)` observations and any `α > 0`,
`max_{i<n} |(Xᵢ - μ₀)/σ₀| / n^α → 0` in probability. -/
theorem tendstoInMeasure_runMax_abs_gumbel_div_rpow {μ₀ σ₀ α : ℝ} (hσ₀ : 0 < σ₀) (hα : 0 < α)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => runMax (fun i => |(X i ω - μ₀) / σ₀|) n / (n : ℝ) ^ α)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / α)
  have hkα : 1 < (k : ℝ) * α := by
    have := (div_lt_iff₀ hα).1 hk
    linarith
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * (2 * exp (-(ε * (n : ℝ) ^ α) / 2))))
      atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
    have hpow : Tendsto (fun t : ℝ => t ^ k * exp (-t)) atTop (𝓝 0) :=
      tendsto_pow_mul_exp_neg_atTop_nhds_zero k
    have hrate : Tendsto (fun n : ℕ => ε / 2 * (n : ℝ) ^ α) atTop atTop :=
      (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop |>.const_mul_atTop (by positivity)
    have hcomp := (hpow.comp hrate).const_mul (2 * (ε / 2)⁻¹ ^ k)
    rw [mul_zero] at hcomp
    refine squeeze_zero_norm' ?_ hcomp
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Function.comp_apply]
    have heq : 2 * (ε / 2)⁻¹ ^ k * ((ε / 2 * (n : ℝ) ^ α) ^ k * exp (-(ε / 2 * (n : ℝ) ^ α))) =
        2 * ((n : ℝ) ^ α) ^ k * exp (-(ε * (n : ℝ) ^ α) / 2) := by
      rw [mul_pow, show -(ε / 2 * (n : ℝ) ^ α) = -(ε * (n : ℝ) ^ α) / 2 by ring]
      have hε2 : (ε / 2) ^ k ≠ 0 := pow_ne_zero k (by positivity)
      rw [inv_pow]
      field_simp [hε2]
    rw [heq]
    have hle : (n : ℝ) ≤ ((n : ℝ) ^ α) ^ k := by
      rw [← rpow_natCast, ← rpow_mul hn0.le, show α * (k : ℝ) = (k : ℝ) * α by ring]
      simpa using rpow_le_rpow_of_exponent_le hn1 hkα.le
    calc (n : ℝ) * (2 * exp (-(ε * (n : ℝ) ^ α) / 2))
        = 2 * (n : ℝ) * exp (-(ε * (n : ℝ) ^ α) / 2) := by ring
      _ ≤ 2 * ((n : ℝ) ^ α) ^ k * exp (-(ε * (n : ℝ) ^ α) / 2) := by gcongr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hna : 0 < (n : ℝ) ^ α := rpow_pos_of_pos hn0 α
  set s := ε * (n : ℝ) ^ α with hs_def
  have hs0 : 0 < s := mul_pos hε hna
  have hsub : {ω | ε ≤ ‖runMax (fun i => |(X i ω - μ₀) / σ₀|) n / (n : ℝ) ^ α - 0‖} ⊆
      ⋃ i ∈ Finset.range n, {ω | s ≤ |(X i ω - μ₀) / σ₀|} := by
    intro ω hω
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (runMax_nonneg _ _) hna.le)] at hω
    rw [le_div_iff₀ hna] at hω
    obtain ⟨i, hi, hfi⟩ := exists_le_of_le_runMax _ hs0 hω
    exact mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, hfi⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hmeas : MeasurableSet {x : ℝ | s ≤ |(x - μ₀) / σ₀|} :=
    measurableSet_le measurable_const (by fun_prop)
  have hterm : ∀ i ∈ Finset.range n,
      P {ω | s ≤ |(X i ω - μ₀) / σ₀|} ≤ ENNReal.ofReal (2 * exp (-s / 2)) := fun i _ => by
    have : {ω | s ≤ |(X i ω - μ₀) / σ₀|} = X i ⁻¹' {x : ℝ | s ≤ |(x - μ₀) / σ₀|} := rfl
    rw [this, ← Measure.map_apply_of_aemeasurable (hX i).aemeasurable hmeas, (hX i).map_eq]
    exact measure_gumbel_abs_ge_le hσ₀ hs0.le
  refine (Finset.sum_le_sum hterm).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n), hs_def]

end GumbelRunMax

/-! ### Uniform envelope and continuity of the GEV Hessian on the good region -/

section GoodRegion

/-- The closed parameter box around `(μ₀, σ₀, 0)` in `(μ, σ, ξ)` coordinates. -/
def gevZeroNbhd (μ₀ σ₀ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc (μ₀ - σ₀ / 8) (μ₀ + σ₀ / 8) ×ˢ Icc (7 * σ₀ / 8) (9 * σ₀ / 8) ×ˢ Icc (-(1 / 8)) (1 / 8)

lemma gevZeroNbhd_mem_nhds {μ₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    gevZeroNbhd μ₀ σ₀ ∈ 𝓝 (μ₀, σ₀, (0 : ℝ)) :=
  prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
    (prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
      (Icc_mem_nhds (by norm_num) (by norm_num)))

lemma mem_gevZeroNbhd_bounds {μ₀ σ₀ : ℝ} {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ gevZeroNbhd μ₀ σ₀) :
    |θ.1 - μ₀| ≤ σ₀ / 8 ∧ 7 * σ₀ / 8 ≤ θ.2.1 ∧ θ.2.1 ≤ 9 * σ₀ / 8 ∧ |θ.2.2| ≤ 1 / 8 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := hθ
  exact ⟨abs_sub_le_iff.2 ⟨by linarith, by linarith⟩, h3, h4, abs_le.2 ⟨h5, h6⟩⟩

lemma gevStep_mem_gevZeroNbhd {μ₀ σ₀ : ℝ} {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ gevZeroNbhd μ₀ σ₀)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s ∈ gevZeroNbhd μ₀ σ₀ := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := hθ
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [gevStep] <;> nlinarith

/-- Integrable dominating envelope for the three-parameter GEV Hessian near `ξ = 0`:
`(1 + |z₀|)⁴ · (1 + exp(-3 z₀))`, `z₀ = (x - μ₀)/σ₀`. -/
noncomputable def gevZeroEnv (μ₀ σ₀ x : ℝ) : ℝ :=
  (1 + |(x - μ₀) / σ₀|) ^ 4 * (1 + exp (-3 * ((x - μ₀) / σ₀)))

lemma gevZeroEnv_nonneg (μ₀ σ₀ x : ℝ) : 0 ≤ gevZeroEnv μ₀ σ₀ x := by
  unfold gevZeroEnv; positivity

lemma measurable_gevZeroEnv (μ₀ σ₀ : ℝ) : Measurable (gevZeroEnv μ₀ σ₀) := by
  unfold gevZeroEnv; fun_prop

/-- `gevZeroEnv` is integrable under `GEV(0, μ₀, σ₀)`. -/
theorem integrable_gevZeroEnv {μ₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    Integrable (gevZeroEnv μ₀ σ₀) (gevLocScaleCDF 0 μ₀ hσ₀).measure := by
  rw [integrable_gevLocScaleCDF_iff hσ₀ (measurable_gevZeroEnv μ₀ σ₀)]
  have hterm : ∀ (a : ℝ), -1 < a →
      IntegrableOn (fun t => exp (-t) * (t ^ a * (1 + |log t|) ^ 4)) (Ioi 0) := fun a ha => by
    have h0 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow ha 0
    have h1 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow ha 1
    have h2 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow ha 2
    have h3 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow ha 3
    have h4 := integrableOn_exp_neg_mul_rpow_mul_abs_log_pow ha 4
    have hsum := (((h0.add (h1.const_mul 4)).add (h2.const_mul 6)).add (h3.const_mul 4)).add h4
    refine hsum.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, pow_zero, pow_one, mul_one]; ring
  have hcomb := (hterm 0 (by norm_num)).add (hterm 3 (by norm_num))
  refine hcomb.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  have hz : (μ₀ + σ₀ * gevTransform 0 t - μ₀) / σ₀ = -log t := by
    simp [gevTransform]; field_simp [hσ₀.ne']
  have hexp : exp (-3 * -log t) = t ^ (3 : ℝ) := by
    rw [rpow_def_of_pos ht0]; congr 1; ring
  simp only [Pi.add_apply, gevZeroEnv, hz, abs_neg, hexp, rpow_zero, one_mul]
  ring

/-- On `gevZeroNbhd μ₀ σ₀`, `|z| ≤ 2 (1 + |z₀|)`. -/
lemma abs_gevZeroZ_le {μ₀ σ₀ x : ℝ} (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ × ℝ}
    (hθ : θ ∈ gevZeroNbhd μ₀ σ₀) :
    |gevZeroZ θ x| ≤ 2 * (1 + |(x - μ₀) / σ₀|) := by
  obtain ⟨hμ, hσlo, -, -⟩ := mem_gevZeroNbhd_bounds hθ
  have hσpos : 0 < θ.2.1 := by linarith
  have heq : gevZeroZ θ x = (σ₀ / θ.2.1) * ((x - μ₀) / σ₀) + (μ₀ - θ.1) / θ.2.1 := by
    rw [gevZeroZ]; field_simp [hσ₀.ne', hσpos.ne']; ring
  rw [heq]
  have hrat : σ₀ / θ.2.1 ≤ 8 / 7 := by rw [div_le_iff₀ hσpos]; linarith
  have hshift : |(μ₀ - θ.1) / θ.2.1| ≤ 1 / 7 := by
    rw [abs_div, abs_of_pos hσpos, abs_sub_comm, div_le_iff₀ hσpos]; linarith
  calc |(σ₀ / θ.2.1) * ((x - μ₀) / σ₀) + (μ₀ - θ.1) / θ.2.1|
      ≤ |(σ₀ / θ.2.1) * ((x - μ₀) / σ₀)| + |(μ₀ - θ.1) / θ.2.1| := abs_add_le _ _
    _ = (σ₀ / θ.2.1) * |(x - μ₀) / σ₀| + |(μ₀ - θ.1) / θ.2.1| := by
        rw [abs_mul, abs_of_pos (div_pos hσ₀ hσpos)]
    _ ≤ 8 / 7 * |(x - μ₀) / σ₀| + 1 / 7 := by
        nlinarith [abs_nonneg ((x - μ₀) / σ₀)]
    _ ≤ 2 * (1 + |(x - μ₀) / σ₀|) := by linarith [abs_nonneg ((x - μ₀) / σ₀)]

/-- On `gevZeroNbhd μ₀ σ₀` with `|ξ z| ≤ 1/2`, `exp (gevZeroF θ x) ≤ 3 (1 + exp (-3 z₀))`. -/
lemma exp_gevZeroF_le {μ₀ σ₀ x : ℝ} (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ × ℝ}
    (hθ : θ ∈ gevZeroNbhd μ₀ σ₀) (ht : |θ.2.2 * gevZeroZ θ x| ≤ 1 / 2) :
    exp (gevZeroF θ x) ≤ 3 * (1 + exp (-3 * ((x - μ₀) / σ₀))) := by
  obtain ⟨hμ, hσlo, -, -⟩ := mem_gevZeroNbhd_bounds hθ
  have hσpos : 0 < θ.2.1 := by linarith
  set z := gevZeroZ θ x
  set z₀ := (x - μ₀) / σ₀
  by_cases hz : 0 ≤ z
  · have hld0 : 0 ≤ log1pDiv (θ.2.2 * z) := by
      rcases eq_or_ne (θ.2.2 * z) 0 with h0 | h0
      · rw [h0, log1pDiv_zero]; norm_num
      · rw [log1pDiv_of_ne h0]
        have hpos : 0 < 1 + θ.2.2 * z := by linarith [neg_abs_le (θ.2.2 * z)]
        rcases lt_or_gt_of_ne h0 with hn | hp
        · exact div_nonneg_of_nonpos (log_nonpos hpos.le (by linarith)) hn.le
        · exact div_nonneg (log_nonneg (by linarith)) hp.le
    have hf0 : gevZeroF θ x ≤ 0 := by
      rw [gevZeroF]; nlinarith
    have he1 : exp (gevZeroF θ x) ≤ 1 := exp_le_one_iff.2 hf0
    linarith [exp_pos (-3 * z₀)]
  · push Not at hz
    have hld2 : log1pDiv (θ.2.2 * z) ≤ 2 := (le_abs_self _).trans (abs_log1pDiv_le_of_abs_le_half ht)
    have hf_le : gevZeroF θ x ≤ 2 * (-z) := by
      rw [gevZeroF]; nlinarith
    have hrel : z₀ = (θ.2.1 / σ₀) * z + (θ.1 - μ₀) / σ₀ := by
      simp only [z, z₀, gevZeroZ]; field_simp [hσ₀.ne', hσpos.ne']; ring
    have hσrat : 7 / 8 ≤ θ.2.1 / σ₀ := by rw [le_div_iff₀ hσ₀]; linarith
    have hμrat : (θ.1 - μ₀) / σ₀ ≤ 1 / 8 := by
      rw [div_le_iff₀ hσ₀]; linarith [(abs_le.1 hμ).2]
    have hz₀_le : z₀ ≤ 7 / 8 * z + 1 / 8 := by nlinarith
    have hneg_z : -z ≤ 8 / 7 * (-z₀) + 1 / 7 := by linarith
    have hz₀_neg : -1 / 8 ≤ -z₀ := by linarith
    have h2z : 2 * (-z) ≤ -3 * z₀ + 1 := by linarith
    have hexp_le : exp (gevZeroF θ x) ≤ exp 1 * exp (-3 * z₀) := by
      rw [← exp_add]; exact exp_le_exp.2 (by linarith)
    have he3 : exp 1 ≤ 3 := by linarith [exp_one_lt_d9]
    nlinarith [exp_pos (-3 * z₀)]

/-- **Uniform envelope bound for the `3 × 3` GEV Hessian on the good region**:
for `θ ∈ gevZeroNbhd μ₀ σ₀` and `|ξ z| ≤ 1/2`, every basis Hessian entry is bounded by
`C₀ * gevZeroEnv μ₀ σ₀ x`. -/
theorem abs_gevZeroH_basis_le {μ₀ σ₀ x : ℝ} (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ × ℝ}
    (hθ : θ ∈ gevZeroNbhd μ₀ σ₀) (ht : |θ.2.2 * gevZeroZ θ x| ≤ 1 / 2) (i j : Fin 3) :
    |gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) x| ≤
      7000 * (1 + σ₀⁻¹ ^ 2) * gevZeroEnv μ₀ σ₀ x := by
  obtain ⟨hμ, hσlo, hσhi, hξbd⟩ := mem_gevZeroNbhd_bounds hθ
  have hσpos : 0 < θ.2.1 := by linarith
  have hinv_σ : θ.2.1⁻¹ ≤ 2 * σ₀⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hσpos, show 2 * σ₀⁻¹ * θ.2.1 = 2 * θ.2.1 / σ₀ by ring,
      le_div_iff₀ hσ₀]
    linarith
  have hinv_σ2 : θ.2.1⁻¹ ^ 2 ≤ 4 * σ₀⁻¹ ^ 2 := by
    have := pow_le_pow_left₀ (inv_nonneg.2 hσpos.le) hinv_σ 2
    linarith
  set Z := 1 + |(x - μ₀) / σ₀|
  have hZ1 : 1 ≤ Z := by simp only [Z]; linarith [abs_nonneg ((x - μ₀) / σ₀)]
  have hZ2 : Z ≤ Z ^ 2 := le_self_pow₀ hZ1 two_ne_zero
  have hZ3 : Z ^ 2 ≤ Z ^ 3 := by nlinarith
  have hZ4 : Z ^ 3 ≤ Z ^ 4 := by nlinarith
  have hZ14 : 1 ≤ Z ^ 4 := one_le_pow₀ hZ1
  have hz : |gevZeroZ θ x| ≤ 2 * Z := abs_gevZeroZ_le hσ₀ hθ
  have hu : 1 / 2 ≤ 1 + θ.2.2 * gevZeroZ θ x := by linarith [neg_abs_le (θ.2.2 * gevZeroZ θ x)]
  have hupos : 0 < 1 + θ.2.2 * gevZeroZ θ x := by linarith
  have hinv_u : (1 + θ.2.2 * gevZeroZ θ x)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hupos two_pos]; linarith
  have hq : |log1pQuad (θ.2.2 * gevZeroZ θ x)| ≤ 3 := abs_log1pQuad_le_of_abs_le_half ht
  have hc : |log1pCube (θ.2.2 * gevZeroZ θ x)| ≤ 5 := abs_log1pCube_le_of_abs_le_half ht
  have hw : exp (gevZeroF θ x) ≤ 3 * (1 + exp (-3 * ((x - μ₀) / σ₀))) :=
    exp_gevZeroF_le hσ₀ hθ ht
  have h1w : |1 + θ.2.2 - exp (gevZeroF θ x)| ≤ 5 * (1 + exp (-3 * ((x - μ₀) / σ₀))) := by
    have hξle : |1 + θ.2.2| ≤ 2 := by
      calc |1 + θ.2.2| ≤ |(1 : ℝ)| + |θ.2.2| := abs_add_le _ _
        _ ≤ 2 := by rw [abs_one]; linarith
    calc |1 + θ.2.2 - exp (gevZeroF θ x)|
        ≤ |1 + θ.2.2| + |exp (gevZeroF θ x)| := abs_sub _ _
      _ = |1 + θ.2.2| + exp (gevZeroF θ x) := by rw [abs_of_pos (exp_pos _)]
      _ ≤ 2 + 3 * (1 + exp (-3 * ((x - μ₀) / σ₀))) := by linarith
      _ ≤ 5 * (1 + exp (-3 * ((x - μ₀) / σ₀))) := by linarith [exp_pos (-3 * ((x - μ₀) / σ₀))]
  set M := 1 + σ₀⁻¹
  have hM1 : 1 ≤ M := by simp only [M]; linarith [inv_pos.2 hσ₀]
  have hMsq : M ^ 2 ≤ 2 * (1 + σ₀⁻¹ ^ 2) := by
    simp only [M]; nlinarith [sq_nonneg (1 - σ₀⁻¹)]
  -- Bounds on `gevZeroZ'`, `gevZeroZ''`, `gevZeroF'`, `gevZeroF''` for basis vectors
  have hbasis : ∀ k : Fin 3,
      |(gevZeroBasis k).1| ≤ 1 ∧ |(gevZeroBasis k).2.1| ≤ 1 ∧ |(gevZeroBasis k).2.2| ≤ 1 := by
    intro k; fin_cases k <;> simp [gevZeroBasis]
  have hZ' : ∀ k : Fin 3, |gevZeroZ' θ (gevZeroBasis k) x| ≤ 6 * M * Z := by
    intro k
    obtain ⟨hb1, hb2, -⟩ := hbasis k
    rw [gevZeroZ', abs_div, abs_neg, abs_of_pos hσpos, div_eq_mul_inv]
    have hnum : |(gevZeroBasis k).1 + gevZeroZ θ x * (gevZeroBasis k).2.1| ≤ 3 * Z := by
      calc |(gevZeroBasis k).1 + gevZeroZ θ x * (gevZeroBasis k).2.1|
          ≤ |(gevZeroBasis k).1| + |gevZeroZ θ x| * |(gevZeroBasis k).2.1| := by
            simpa [abs_mul] using abs_add_le (gevZeroBasis k).1 (gevZeroZ θ x * (gevZeroBasis k).2.1)
        _ ≤ 1 + (2 * Z) * 1 := add_le_add hb1 (mul_le_mul hz hb2 (abs_nonneg _) (by positivity))
        _ ≤ 3 * Z := by linarith
    have hinv_M : θ.2.1⁻¹ ≤ 2 * M := by simp only [M]; linarith
    calc |(gevZeroBasis k).1 + gevZeroZ θ x * (gevZeroBasis k).2.1| * θ.2.1⁻¹
        ≤ (3 * Z) * (2 * M) := mul_le_mul hnum hinv_M (inv_nonneg.2 hσpos.le) (by positivity)
      _ = 6 * M * Z := by ring
  have hZ'' : ∀ k l : Fin 3, |gevZeroZ'' θ (gevZeroBasis k) (gevZeroBasis l) x| ≤ 24 * M ^ 2 * Z := by
    intro k l
    obtain ⟨hk1, hk2, -⟩ := hbasis k
    obtain ⟨hl1, hl2, -⟩ := hbasis l
    rw [gevZeroZ'', abs_div, abs_pow, abs_of_pos hσpos, div_eq_mul_inv, ← inv_pow]
    have hnum1 : |(gevZeroBasis k).2.1 * ((gevZeroBasis l).1 + gevZeroZ θ x * (gevZeroBasis l).2.1)| ≤
        3 * Z := by
      rw [abs_mul]
      have h1 : |(gevZeroBasis l).1 + gevZeroZ θ x * (gevZeroBasis l).2.1| ≤ 3 * Z := by
        calc _ ≤ |(gevZeroBasis l).1| + |gevZeroZ θ x| * |(gevZeroBasis l).2.1| := by
              simpa [abs_mul] using abs_add_le (gevZeroBasis l).1 (gevZeroZ θ x * (gevZeroBasis l).2.1)
          _ ≤ 1 + (2 * Z) * 1 := add_le_add hl1 (mul_le_mul hz hl2 (abs_nonneg _) (by positivity))
          _ ≤ 3 * Z := by linarith
      calc |(gevZeroBasis k).2.1| * |(gevZeroBasis l).1 + gevZeroZ θ x * (gevZeroBasis l).2.1|
          ≤ 1 * (3 * Z) := mul_le_mul hk2 h1 (abs_nonneg _) zero_le_one
        _ = 3 * Z := one_mul _
    have hnum2 : |(gevZeroBasis l).2.1 * ((gevZeroBasis k).1 + gevZeroZ θ x * (gevZeroBasis k).2.1)| ≤
        3 * Z := by
      rw [abs_mul]
      have h1 : |(gevZeroBasis k).1 + gevZeroZ θ x * (gevZeroBasis k).2.1| ≤ 3 * Z := by
        calc _ ≤ |(gevZeroBasis k).1| + |gevZeroZ θ x| * |(gevZeroBasis k).2.1| := by
              simpa [abs_mul] using abs_add_le (gevZeroBasis k).1 (gevZeroZ θ x * (gevZeroBasis k).2.1)
          _ ≤ 1 + (2 * Z) * 1 := add_le_add hk1 (mul_le_mul hz hk2 (abs_nonneg _) (by positivity))
          _ ≤ 3 * Z := by linarith
      calc |(gevZeroBasis l).2.1| * |(gevZeroBasis k).1 + gevZeroZ θ x * (gevZeroBasis k).2.1|
          ≤ 1 * (3 * Z) := mul_le_mul hl2 h1 (abs_nonneg _) zero_le_one
        _ = 3 * Z := one_mul _
    have hinv2 : θ.2.1⁻¹ ^ 2 ≤ 4 * M ^ 2 := by
      have h1 : θ.2.1⁻¹ ≤ 2 * M := by simp only [M]; linarith
      have := pow_le_pow_left₀ (inv_nonneg.2 hσpos.le) h1 2
      linarith
    calc _ ≤ (3 * Z + 3 * Z) * (4 * M ^ 2) :=
          mul_le_mul ((abs_add_le _ _).trans (add_le_add hnum1 hnum2)) hinv2 (by positivity) (by positivity)
      _ = 24 * M ^ 2 * Z := by ring
  have hF' : ∀ k : Fin 3, |gevZeroF' θ (gevZeroBasis k) x| ≤ 24 * M * Z ^ 2 := by
    intro k
    obtain ⟨-, -, hk3⟩ := hbasis k
    rw [gevZeroF']
    have t1 : |-gevZeroZ' θ (gevZeroBasis k) x / (1 + θ.2.2 * gevZeroZ θ x)| ≤ 12 * M * Z ^ 2 := by
      rw [abs_div, abs_neg, abs_of_pos hupos, div_eq_mul_inv]
      calc |gevZeroZ' θ (gevZeroBasis k) x| * (1 + θ.2.2 * gevZeroZ θ x)⁻¹
          ≤ (6 * M * Z) * 2 := mul_le_mul (hZ' k) hinv_u (inv_nonneg.2 hupos.le) (by positivity)
        _ = 12 * M * Z := by ring
        _ ≤ 12 * M * Z ^ 2 := mul_le_mul_of_nonneg_left hZ2 (by positivity)
    have t2 : |gevZeroZ θ x ^ 2 * log1pQuad (θ.2.2 * gevZeroZ θ x) * (gevZeroBasis k).2.2| ≤
        12 * M * Z ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow]
      have hz2 : |gevZeroZ θ x| ^ 2 ≤ 4 * Z ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hz 2; linarith
      have h1 : |gevZeroZ θ x| ^ 2 * |log1pQuad (θ.2.2 * gevZeroZ θ x)| ≤ (4 * Z ^ 2) * 3 :=
        mul_le_mul hz2 hq (abs_nonneg _) (by positivity)
      calc _ ≤ ((4 * Z ^ 2) * 3) * 1 := mul_le_mul h1 hk3 (abs_nonneg _) (by positivity)
        _ = 12 * 1 * Z ^ 2 := by ring
        _ ≤ 12 * M * Z ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg Z)
    linarith [abs_add_le (-gevZeroZ' θ (gevZeroBasis k) x / (1 + θ.2.2 * gevZeroZ θ x))
      (gevZeroZ θ x ^ 2 * log1pQuad (θ.2.2 * gevZeroZ θ x) * (gevZeroBasis k).2.2)]
  have hMle : M ≤ M ^ 2 := le_self_pow₀ hM1 two_ne_zero
  have hM2_ge1 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
  have hZ24 : Z ^ 2 ≤ Z ^ 4 := hZ3.trans hZ4
  have hZ14' : Z ≤ Z ^ 4 := hZ2.trans hZ24
  have hF'' : |gevZeroF'' θ (gevZeroBasis i) (gevZeroBasis j) x| ≤ 250 * M ^ 2 * Z ^ 4 := by
    obtain ⟨-, -, hi3⟩ := hbasis i
    obtain ⟨-, -, hj3⟩ := hbasis j
    rw [gevZeroF'']
    have hinv_u2 : ((1 + θ.2.2 * gevZeroZ θ x) ^ 2)⁻¹ ≤ 4 := by
      rw [← inv_pow]; have := pow_le_pow_left₀ (inv_nonneg.2 hupos.le) hinv_u 2; linarith
    have t1 : |(θ.2.2 * gevZeroZ' θ (gevZeroBasis i) x * gevZeroZ' θ (gevZeroBasis j) x +
        gevZeroZ θ x * (gevZeroZ' θ (gevZeroBasis i) x * (gevZeroBasis j).2.2 +
          gevZeroZ' θ (gevZeroBasis j) x * (gevZeroBasis i).2.2)) /
        (1 + θ.2.2 * gevZeroZ θ x) ^ 2| ≤ 120 * M ^ 2 * Z ^ 4 := by
      rw [abs_div, abs_pow, abs_of_pos hupos, div_eq_mul_inv]
      have ha : |θ.2.2 * gevZeroZ' θ (gevZeroBasis i) x * gevZeroZ' θ (gevZeroBasis j) x| ≤
          6 * M ^ 2 * Z ^ 2 := by
        rw [abs_mul, abs_mul]
        have h1 : |θ.2.2| * |gevZeroZ' θ (gevZeroBasis i) x| ≤ (1 / 8) * (6 * M * Z) :=
          mul_le_mul hξbd (hZ' i) (abs_nonneg _) (by norm_num)
        have h2 := mul_le_mul h1 (hZ' j) (abs_nonneg _) (by positivity)
        have h3 : 1 / 8 * (6 * M * Z) * (6 * M * Z) = 9 / 2 * (M ^ 2 * Z ^ 2) := by ring
        have h4 : 0 ≤ M ^ 2 * Z ^ 2 := by positivity
        linarith
      have hb : |gevZeroZ θ x * (gevZeroZ' θ (gevZeroBasis i) x * (gevZeroBasis j).2.2 +
          gevZeroZ' θ (gevZeroBasis j) x * (gevZeroBasis i).2.2)| ≤ 24 * M ^ 2 * Z ^ 2 := by
        rw [abs_mul]
        have hsum : |gevZeroZ' θ (gevZeroBasis i) x * (gevZeroBasis j).2.2 +
            gevZeroZ' θ (gevZeroBasis j) x * (gevZeroBasis i).2.2| ≤ 12 * M * Z := by
          have h1 : |gevZeroZ' θ (gevZeroBasis i) x * (gevZeroBasis j).2.2| ≤ 6 * M * Z := by
            rw [abs_mul]; calc _ ≤ (6 * M * Z) * 1 := mul_le_mul (hZ' i) hj3 (abs_nonneg _) (by positivity)
              _ = 6 * M * Z := mul_one _
          have h2 : |gevZeroZ' θ (gevZeroBasis j) x * (gevZeroBasis i).2.2| ≤ 6 * M * Z := by
            rw [abs_mul]; calc _ ≤ (6 * M * Z) * 1 := mul_le_mul (hZ' j) hi3 (abs_nonneg _) (by positivity)
              _ = 6 * M * Z := mul_one _
          linarith [abs_add_le (gevZeroZ' θ (gevZeroBasis i) x * (gevZeroBasis j).2.2)
            (gevZeroZ' θ (gevZeroBasis j) x * (gevZeroBasis i).2.2)]
        calc |gevZeroZ θ x| * _ ≤ (2 * Z) * (12 * M * Z) :=
              mul_le_mul hz hsum (abs_nonneg _) (by positivity)
          _ = 24 * M * Z ^ 2 := by ring
          _ ≤ 24 * M ^ 2 * Z ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg Z)
      have hnum : |θ.2.2 * gevZeroZ' θ (gevZeroBasis i) x * gevZeroZ' θ (gevZeroBasis j) x +
          gevZeroZ θ x * (gevZeroZ' θ (gevZeroBasis i) x * (gevZeroBasis j).2.2 +
            gevZeroZ' θ (gevZeroBasis j) x * (gevZeroBasis i).2.2)| ≤ 30 * M ^ 2 * Z ^ 2 :=
        (abs_add_le _ _).trans (by linarith)
      calc _ ≤ (30 * M ^ 2 * Z ^ 2) * 4 := mul_le_mul hnum hinv_u2 (by positivity) (by positivity)
        _ = 120 * M ^ 2 * Z ^ 2 := by ring
        _ ≤ 120 * M ^ 2 * Z ^ 4 := mul_le_mul_of_nonneg_left hZ24 (by positivity)
    have t2 : |gevZeroZ θ x ^ 3 * log1pCube (θ.2.2 * gevZeroZ θ x) *
        ((gevZeroBasis i).2.2 * (gevZeroBasis j).2.2)| ≤ 40 * M ^ 2 * Z ^ 4 := by
      rw [abs_mul, abs_mul, abs_pow, abs_mul]
      have hz3 : |gevZeroZ θ x| ^ 3 ≤ 8 * Z ^ 3 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hz 3; linarith
      have h1 : |gevZeroZ θ x| ^ 3 * |log1pCube (θ.2.2 * gevZeroZ θ x)| ≤ (8 * Z ^ 3) * 5 :=
        mul_le_mul hz3 hc (abs_nonneg _) (by positivity)
      have h2 : |(gevZeroBasis i).2.2| * |(gevZeroBasis j).2.2| ≤ 1 := by
        calc _ ≤ 1 * 1 := mul_le_mul hi3 hj3 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc _ ≤ ((8 * Z ^ 3) * 5) * 1 := mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 40 * 1 * Z ^ 3 := by ring
        _ ≤ 40 * M ^ 2 * Z ^ 4 :=
            mul_le_mul (by linarith) hZ4 (pow_nonneg (by linarith) 3) (by positivity)
    have t3 : |gevZeroZ'' θ (gevZeroBasis i) (gevZeroBasis j) x / (1 + θ.2.2 * gevZeroZ θ x)| ≤
        48 * M ^ 2 * Z ^ 4 := by
      rw [abs_div, abs_of_pos hupos, div_eq_mul_inv]
      calc _ ≤ (24 * M ^ 2 * Z) * 2 := mul_le_mul (hZ'' i j) hinv_u (inv_nonneg.2 hupos.le) (by positivity)
        _ = 48 * M ^ 2 * Z := by ring
        _ ≤ 48 * M ^ 2 * Z ^ 4 := mul_le_mul_of_nonneg_left hZ14' (by positivity)
    have htri := (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3)
    have hnn : 0 ≤ M ^ 2 * Z ^ 4 := by positivity
    linarith
  -- Combine all 5 terms of `gevZeroH`
  obtain ⟨-, hi2, hi3⟩ := hbasis i
  obtain ⟨-, hj2, hj3⟩ := hbasis j
  rw [gevZeroH]
  set E := 1 + exp (-3 * ((x - μ₀) / σ₀))
  have hE1 : 1 ≤ E := by simp only [E]; linarith [exp_pos (-3 * ((x - μ₀) / σ₀))]
  have hZE1 : 1 ≤ Z ^ 4 * E := by
    simpa using mul_le_mul hZ14 hE1 zero_le_one (by positivity)
  have hZ2E : Z ^ 2 ≤ Z ^ 4 * E := by
    simpa using mul_le_mul hZ24 hE1 zero_le_one (by positivity)
  have c1 : |(gevZeroBasis i).2.1 * (gevZeroBasis j).2.1 / θ.2.1 ^ 2| ≤ 4 * M ^ 2 * Z ^ 4 * E := by
    rw [abs_div, abs_mul, abs_pow, abs_of_pos hσpos, div_eq_mul_inv, ← inv_pow]
    have h1 : |(gevZeroBasis i).2.1| * |(gevZeroBasis j).2.1| ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul hi2 hj2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hinv2 : θ.2.1⁻¹ ^ 2 ≤ 4 * M ^ 2 := by
      have h := pow_le_pow_left₀ (inv_nonneg.2 hσpos.le) (show θ.2.1⁻¹ ≤ 2 * M by simp only [M]; linarith) 2
      linarith
    calc _ ≤ 1 * (4 * M ^ 2) := mul_le_mul h1 hinv2 (by positivity) zero_le_one
      _ = 4 * M ^ 2 * 1 := by ring
      _ ≤ 4 * M ^ 2 * (Z ^ 4 * E) := mul_le_mul_of_nonneg_left hZE1 (by positivity)
      _ = 4 * M ^ 2 * Z ^ 4 * E := by ring
  have c2 : |(gevZeroBasis i).2.2 * gevZeroF' θ (gevZeroBasis j) x| ≤ 24 * M ^ 2 * Z ^ 4 * E := by
    rw [abs_mul]
    calc _ ≤ 1 * (24 * M * Z ^ 2) := mul_le_mul hi3 (hF' j) (abs_nonneg _) zero_le_one
      _ = 24 * M * Z ^ 2 := one_mul _
      _ ≤ 24 * M ^ 2 * (Z ^ 4 * E) :=
          mul_le_mul (by linarith) hZ2E (sq_nonneg Z) (by positivity)
      _ = 24 * M ^ 2 * Z ^ 4 * E := by ring
  have c3 : |(gevZeroBasis j).2.2 * gevZeroF' θ (gevZeroBasis i) x| ≤ 24 * M ^ 2 * Z ^ 4 * E := by
    rw [abs_mul]
    calc _ ≤ 1 * (24 * M * Z ^ 2) := mul_le_mul hj3 (hF' i) (abs_nonneg _) zero_le_one
      _ = 24 * M * Z ^ 2 := one_mul _
      _ ≤ 24 * M ^ 2 * (Z ^ 4 * E) :=
          mul_le_mul (by linarith) hZ2E (sq_nonneg Z) (by positivity)
      _ = 24 * M ^ 2 * Z ^ 4 * E := by ring
  have c4 : |(1 + θ.2.2 - exp (gevZeroF θ x)) * gevZeroF'' θ (gevZeroBasis i) (gevZeroBasis j) x| ≤
      1250 * M ^ 2 * Z ^ 4 * E := by
    rw [abs_mul]
    calc _ ≤ (5 * E) * (250 * M ^ 2 * Z ^ 4) := mul_le_mul h1w hF'' (abs_nonneg _) (by positivity)
      _ = 1250 * M ^ 2 * Z ^ 4 * E := by ring
  have c5 : |exp (gevZeroF θ x) * (gevZeroF' θ (gevZeroBasis i) x * gevZeroF' θ (gevZeroBasis j) x)| ≤
      1728 * M ^ 2 * Z ^ 4 * E := by
    rw [abs_mul, abs_mul, abs_of_pos (exp_pos _)]
    have hprod := mul_le_mul (hF' i) (hF' j) (abs_nonneg _) (by positivity)
    calc exp (gevZeroF θ x) * (|gevZeroF' θ (gevZeroBasis i) x| * |gevZeroF' θ (gevZeroBasis j) x|)
        ≤ (3 * E) * (24 * M * Z ^ 2 * (24 * M * Z ^ 2)) :=
          mul_le_mul hw hprod (by positivity) (by positivity)
      _ = 1728 * M ^ 2 * Z ^ 4 * E := by ring
  have htri := (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add c1 c2)) c3)) c4)) c5)
  have hEnv : Z ^ 4 * E = gevZeroEnv μ₀ σ₀ x := rfl
  rw [← hEnv]
  have hsum_bd : 4 * M ^ 2 * Z ^ 4 * E + 24 * M ^ 2 * Z ^ 4 * E + 24 * M ^ 2 * Z ^ 4 * E +
      1250 * M ^ 2 * Z ^ 4 * E + 1728 * M ^ 2 * Z ^ 4 * E = 3030 * M ^ 2 * (Z ^ 4 * E) := by ring
  have hfinal : 3030 * M ^ 2 * (Z ^ 4 * E) ≤ 7000 * (1 + σ₀⁻¹ ^ 2) * (Z ^ 4 * E) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith [show 3030 * M ^ 2 ≤ 3030 * (2 * (1 + σ₀⁻¹ ^ 2)) by linarith,
      show 0 ≤ 1 + σ₀⁻¹ ^ 2 by positivity]
  linarith

lemma continuousAt_gevZeroH_basis {θ : ℝ × ℝ × ℝ} {x : ℝ} (hσ : 0 < θ.2.1)
    (hu : 0 < 1 + θ.2.2 * gevZeroZ θ x) (i j : Fin 3) :
    ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroH p.1 (gevZeroBasis i) (gevZeroBasis j) p.2)
      (θ, x) := by
  have hZ : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroZ p.1 p.2) (θ, x) := by
    unfold gevZeroZ; fun_prop (disch := exact hσ.ne')
  have hT : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.2 * gevZeroZ p.1 p.2) (θ, x) :=
    (by fun_prop : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.2) (θ, x)).mul hZ
  have hgt : -1 < θ.2.2 * gevZeroZ θ x := by linarith
  have hld : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => log1pDiv (p.1.2.2 * gevZeroZ p.1 p.2)) (θ, x) :=
    ContinuousAt.comp (g := log1pDiv) (continuousAt_log1pDiv_of_gt hgt) hT
  have hlq : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => log1pQuad (p.1.2.2 * gevZeroZ p.1 p.2)) (θ, x) :=
    ContinuousAt.comp (g := log1pQuad) (continuousAt_log1pQuad_of_gt hgt) hT
  have hlc : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => log1pCube (p.1.2.2 * gevZeroZ p.1 p.2)) (θ, x) :=
    ContinuousAt.comp (g := log1pCube) (continuousAt_log1pCube hgt) hT
  have hF : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroF p.1 p.2) (θ, x) :=
    hZ.neg.mul hld
  have hZ' : ∀ k : Fin 3, ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroZ' p.1 (gevZeroBasis k) p.2)
      (θ, x) := fun k => by
    unfold gevZeroZ' gevZeroZ; fun_prop (disch := exact hσ.ne')
  have hZ'' : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroZ'' p.1 (gevZeroBasis i) (gevZeroBasis j) p.2)
      (θ, x) := by
    unfold gevZeroZ''
    have hσ2 : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.1 ^ 2) (θ, x) := by fun_prop
    exact (((continuousAt_const.mul (continuousAt_const.add (hZ.mul continuousAt_const))).add
      (continuousAt_const.mul (continuousAt_const.add (hZ.mul continuousAt_const)))).div
      hσ2 (pow_ne_zero 2 hσ.ne'))
  have hU : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => 1 + p.1.2.2 * gevZeroZ p.1 p.2) (θ, x) :=
    continuousAt_const.add hT
  have hF' : ∀ k : Fin 3, ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroF' p.1 (gevZeroBasis k) p.2)
      (θ, x) := fun k => by
    unfold gevZeroF'
    exact ((hZ' k).neg.div hU hu.ne').add (((hZ.pow 2).mul hlq).mul continuousAt_const)
  have hξ : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.2) (θ, x) := by fun_prop
  have hF'' : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroF'' p.1 (gevZeroBasis i) (gevZeroBasis j) p.2)
      (θ, x) := by
    unfold gevZeroF''
    have hc1 : ContinuousAt (fun _ : (ℝ × ℝ × ℝ) × ℝ => (gevZeroBasis j).2.2) (θ, x) := continuousAt_const
    have hc2 : ContinuousAt (fun _ : (ℝ × ℝ × ℝ) × ℝ => (gevZeroBasis i).2.2) (θ, x) := continuousAt_const
    have hc3 : ContinuousAt (fun _ : (ℝ × ℝ × ℝ) × ℝ => (gevZeroBasis i).2.2 * (gevZeroBasis j).2.2) (θ, x) :=
      continuousAt_const
    have h1 := ((hξ.mul (hZ' i)).mul (hZ' j)).add (hZ.mul (((hZ' i).mul hc1).add ((hZ' j).mul hc2)))
    have h2 := ((hZ.pow 3).mul hlc).mul hc3
    exact ((h1.div (hU.pow 2) (pow_ne_zero 2 hu.ne')).add h2).sub (hZ''.div hU hu.ne')
  unfold gevZeroH
  have hσ2 : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.1 ^ 2) (θ, x) := by fun_prop
  have hExpF : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => exp (gevZeroF p.1 p.2)) (θ, x) :=
    Real.continuous_exp.continuousAt.comp hF
  exact (((((continuousAt_const.div hσ2 (pow_ne_zero 2 hσ.ne')).add
    (continuousAt_const.mul (hF' j))).add (continuousAt_const.mul (hF' i))).add
    (((continuousAt_const.add hξ).sub hExpF).mul hF'')).sub
    (hExpF.mul ((hF' i).mul (hF' j))))

/-- Uniform continuity of `gevZeroH` in `θ` near `(μ₀, σ₀, 0)` uniformly over `|(x - μ₀)/σ₀| ≤ M`. -/
lemma exists_delta_gevZeroH_sub_le {μ₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀) (M : ℝ) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    ∃ δ > 0, δ ≤ min (σ₀ / 8) (1 / (8 * (M + 1))) ∧
      ∀ θ : ℝ × ℝ × ℝ, |θ.1 - μ₀| ≤ δ → |θ.2.1 - σ₀| ≤ δ → |θ.2.2| ≤ δ →
        ∀ x : ℝ, |(x - μ₀) / σ₀| ≤ M →
          |gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) x -
            gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) x| ≤ ε := by
  set r := min (σ₀ / 8) (1 / (8 * (M + 1))) with hr_def
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  set Kθ : Set (ℝ × ℝ × ℝ) :=
    Icc (μ₀ - r) (μ₀ + r) ×ˢ Icc (σ₀ - r) (σ₀ + r) ×ˢ Icc (-r) r
  set Kx : Set ℝ := Icc (μ₀ - M * σ₀) (μ₀ + M * σ₀)
  have hK : IsCompact (Kθ ×ˢ Kx) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc
  have hcont : ContinuousOn (fun p : (ℝ × ℝ × ℝ) × ℝ =>
      gevZeroH p.1 (gevZeroBasis i) (gevZeroBasis j) p.2) (Kθ ×ˢ Kx) := by
    intro ⟨θ, x⟩ ⟨hθ, hx⟩
    have hθ_nbhd : θ ∈ gevZeroNbhd μ₀ σ₀ := by
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := hθ
      have hr1 : r ≤ σ₀ / 8 := min_le_left _ _
      have hr2 : r ≤ 1 / 8 := (min_le_right _ _).trans (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    have hσ : 0 < θ.2.1 := by linarith [(mem_gevZeroNbhd_bounds hθ_nbhd).2.1]
    have hxM : |(x - μ₀) / σ₀| ≤ M := by
      rw [abs_div, abs_of_pos hσ₀, div_le_iff₀ hσ₀, abs_le]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hz : |gevZeroZ θ x| ≤ 2 * (1 + M) :=
      (abs_gevZeroZ_le hσ₀ hθ_nbhd).trans (by linarith)
    have hξr : |θ.2.2| ≤ 1 / (8 * (M + 1)) :=
      (abs_le.2 hθ.2.2).trans (min_le_right _ _)
    have ht : |θ.2.2 * gevZeroZ θ x| ≤ 1 / 4 := by
      rw [abs_mul]
      calc |θ.2.2| * |gevZeroZ θ x| ≤ (1 / (8 * (M + 1))) * (2 * (1 + M)) :=
            mul_le_mul hξr hz (abs_nonneg _) (by positivity)
        _ = 1 / 4 := by field_simp [show (M + 1 : ℝ) ≠ 0 by linarith]; ring
    have hu : 0 < 1 + θ.2.2 * gevZeroZ θ x := by linarith [neg_abs_le (θ.2.2 * gevZeroZ θ x)]
    exact (continuousAt_gevZeroH_basis hσ hu i j).continuousWithinAt
  obtain ⟨ρ, hρ, hunif⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hcont)
    ε hε
  refine ⟨min r (ρ / 2), lt_min hr (by positivity), min_le_left _ _, fun θ h1 h2 h3 x hx => ?_⟩
  have hd_le_r : min r (ρ / 2) ≤ r := min_le_left _ _
  have hd_lt_ρ : min r (ρ / 2) < ρ := (min_le_right _ _).trans_lt (by linarith)
  have hθK : θ ∈ Kθ := ⟨⟨by linarith [(abs_le.1 h1).1], by linarith [(abs_le.1 h1).2]⟩,
    ⟨by linarith [(abs_le.1 h2).1], by linarith [(abs_le.1 h2).2]⟩,
    ⟨by linarith [(abs_le.1 h3).1], by linarith [(abs_le.1 h3).2]⟩⟩
  have hθ₀K : (μ₀, σ₀, (0 : ℝ)) ∈ Kθ :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hxK : x ∈ Kx := by
    rw [abs_div, abs_of_pos hσ₀, div_le_iff₀ hσ₀, abs_le] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hdist : dist (θ, x) ((μ₀, σ₀, (0 : ℝ)), x) < ρ := by
    rw [Prod.dist_eq, dist_self, max_lt_iff]
    refine ⟨?_, hρ⟩
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨?_, ?_⟩
    · rw [Real.dist_eq]; exact lt_of_le_of_lt h1 hd_lt_ρ
    · rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, sub_zero]
      exact ⟨lt_of_le_of_lt h2 hd_lt_ρ, lt_of_le_of_lt h3 hd_lt_ρ⟩
  have hlt := hunif (θ, x) ⟨hθK, hxK⟩ ((μ₀, σ₀, 0), x) ⟨hθ₀K, hxK⟩ hdist
  rw [Real.dist_eq] at hlt
  exact hlt.le

/-- Tail of `gevZeroEnv` outside `|(x - μ₀)/σ₀| ≤ M`. -/
noncomputable def gevZeroEnvTail (μ₀ σ₀ M x : ℝ) : ℝ :=
  ({x | M < |(x - μ₀) / σ₀|}).indicator (gevZeroEnv μ₀ σ₀) x

lemma gevZeroEnvTail_nonneg (μ₀ σ₀ M x : ℝ) : 0 ≤ gevZeroEnvTail μ₀ σ₀ M x :=
  Set.indicator_nonneg (fun y _ => gevZeroEnv_nonneg μ₀ σ₀ y) x

lemma measurable_gevZeroEnvTail (μ₀ σ₀ M : ℝ) : Measurable (gevZeroEnvTail μ₀ σ₀ M) :=
  (measurable_gevZeroEnv μ₀ σ₀).indicator (measurableSet_lt measurable_const (by fun_prop))

lemma integrable_gevZeroEnvTail {μ₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀) (M : ℝ) :
    Integrable (gevZeroEnvTail μ₀ σ₀ M) (gevLocScaleCDF 0 μ₀ hσ₀).measure :=
  (integrable_gevZeroEnv hσ₀).mono' (measurable_gevZeroEnvTail μ₀ σ₀ M).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gevZeroEnvTail_nonneg μ₀ σ₀ M x)]
      exact Set.indicator_le_self' (fun y _ => gevZeroEnv_nonneg μ₀ σ₀ y) x)

lemma tendsto_integral_gevZeroEnvTail {μ₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    Tendsto (fun k : ℕ => ∫ x, gevZeroEnvTail μ₀ σ₀ (k : ℝ) x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure)
      atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) (gevZeroEnv μ₀ σ₀)
    (fun k => (measurable_gevZeroEnvTail μ₀ σ₀ k).aestronglyMeasurable)
    (integrable_gevZeroEnv hσ₀)
    (fun k => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gevZeroEnvTail_nonneg μ₀ σ₀ k x)]
      exact Set.indicator_le_self' (fun y _ => gevZeroEnv_nonneg μ₀ σ₀ y) x)
    (ae_of_all _ fun x => by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨m, hm⟩ := exists_nat_ge |(x - μ₀) / σ₀|
      filter_upwards [eventually_ge_atTop m] with k hk
      have hle : |(x - μ₀) / σ₀| ≤ (k : ℝ) := hm.trans (by exact_mod_cast hk)
      simp [gevZeroEnvTail, not_lt.2 hle])
  simpa using h

end GoodRegion

/-! ### Averaged segment Hessian and matrix convergence in probability -/

section LocalMLENormality

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- Segment-averaged Hessian entry `∫_0^1 gevZeroH (θ₀ + s(θ - θ₀)) eᵢ eⱼ x ds`. -/
noncomputable def gevZeroSegH (μ₀ σ₀ : ℝ) (θ : ℝ × ℝ × ℝ) (i j : Fin 3) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1,
    gevZeroH (gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s) (gevZeroBasis i) (gevZeroBasis j) x

/-- Exact FTC identity along the segment from `(μ₀, σ₀, 0)` to `θ`:
`gevZeroD θ eᵢ x - gevZeroD (μ₀, σ₀, 0) eᵢ x = ∑_j (θ - θ₀)_j · gevZeroSegH μ₀ σ₀ θ i j x`. -/
lemma gevZeroD_sub_eq_sum_segH {μ₀ σ₀ x : ℝ} (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ × ℝ}
    (hθ : θ ∈ gevZeroNbhd μ₀ σ₀)
    (ht : ∀ s ∈ Icc (0 : ℝ) 1,
      |(gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s).2.2 *
        gevZeroZ (gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s) x| ≤ 1 / 2)
    (i : Fin 3) :
    gevZeroD θ (gevZeroBasis i) x - gevZeroD (μ₀, σ₀, 0) (gevZeroBasis i) x =
      ∑ j : Fin 3, (![θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2] j) * gevZeroSegH μ₀ σ₀ θ i j x := by
  set d : ℝ × ℝ × ℝ := (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2)
  set γ : ℝ → ℝ × ℝ × ℝ := gevStep (μ₀, σ₀, 0) d
  have hgood : ∀ s ∈ uIcc (0 : ℝ) 1, 0 < (γ s).2.1 ∧ 0 < 1 + (γ s).2.2 * gevZeroZ (γ s) x := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hm := gevStep_mem_gevZeroNbhd hθ hs.1 hs.2
    have hσ : 0 < (γ s).2.1 := by linarith [(mem_gevZeroNbhd_bounds hm).2.1]
    have hu : 0 < 1 + (γ s).2.2 * gevZeroZ (γ s) x := by
      linarith [neg_abs_le ((γ s).2.2 * gevZeroZ (γ s) x), ht s hs]
    exact ⟨hσ, hu⟩
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun r => gevZeroD (γ r) (gevZeroBasis i) x)
        (gevZeroH (γ s) d (gevZeroBasis i) x) s := fun s hs =>
    hasDerivAt_gevZeroD_line (hgood s hs).1 (hgood s hs).2
  have hcont_j : ∀ j : Fin 3,
      ContinuousOn (fun s => gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) x) (uIcc 0 1) := by
    intro j s hs
    have hγc : ContinuousAt (fun r => (γ r, x)) s := by
      unfold γ gevStep; fun_prop
    exact (ContinuousAt.comp (f := fun r => (γ r, x))
      (g := fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroH p.1 (gevZeroBasis i) (gevZeroBasis j) p.2)
      (continuousAt_gevZeroH_basis (hgood s hs).1 (hgood s hs).2 i j) hγc).continuousWithinAt
  have hsym_H : ∀ s, gevZeroH (γ s) d (gevZeroBasis i) x =
      ∑ j : Fin 3, (![d.1, d.2.1, d.2.2] j) * gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) x := by
    intro s
    have h1 := gevZeroH_eq_sum (γ s) d (gevZeroBasis i) x
    have hsym : ∀ a b : Fin 3, gevZeroH (γ s) (gevZeroBasis a) (gevZeroBasis b) x =
        gevZeroH (γ s) (gevZeroBasis b) (gevZeroBasis a) x := fun a b => by
      simp only [gevZeroH, gevZeroF'', gevZeroZ'']; ring
    have hb0 : gevZeroBasis 0 = (1, 0, 0) := rfl
    have hb1 : gevZeroBasis 1 = (0, 1, 0) := rfl
    have hb2 : gevZeroBasis 2 = (0, 0, 1) := rfl
    rw [h1]
    fin_cases i <;>
      simp [Fin.sum_univ_three, hb0, hb1, hb2] <;>
      simp only [← hb0, ← hb1, ← hb2, hsym 1 0, hsym 2 0, hsym 2 1]
  have hint_j : ∀ j : Fin 3,
      IntervalIntegrable (fun s => (![d.1, d.2.1, d.2.2] j) *
        gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) x) volume 0 1 := fun j =>
    ((hcont_j j).const_mul _).intervalIntegrable
  have hint : IntervalIntegrable (fun s => gevZeroH (γ s) d (gevZeroBasis i) x) volume 0 1 := by
    simp_rw [hsym_H]
    exact IntervalIntegrable.sum Finset.univ fun j _ => hint_j j
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hγ1 : γ 1 = θ := by simp [γ, d, gevStep]
  have hγ0 : γ 0 = (μ₀, σ₀, 0) := by simp [γ, gevStep]
  rw [hγ1, hγ0] at hftc
  rw [← hftc]
  simp_rw [hsym_H]
  rw [intervalIntegral.integral_finsetSum fun j _ => hint_j j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- Second-order Taylor expansion of `gevZeroLog` along the segment from `(μ₀, σ₀, 0)` to `θ`:
`ℓ(θ) - ℓ(θ₀) = D(θ₀)[d] + ∫_0^1 (1 - s) H(θ₀ + s d)[d, d] ds`. -/
lemma gevZeroLog_sub_eq_taylor {μ₀ σ₀ x : ℝ} (hσ₀ : 0 < σ₀) {θ : ℝ × ℝ × ℝ}
    (hθ : θ ∈ gevZeroNbhd μ₀ σ₀)
    (ht : ∀ s ∈ Icc (0 : ℝ) 1,
      |(gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s).2.2 *
        gevZeroZ (gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s) x| ≤ 1 / 2) :
    gevZeroLog θ x - gevZeroLog (μ₀, σ₀, 0) x =
      gevZeroD (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) x +
      ∫ s in (0 : ℝ)..1, (1 - s) *
        gevZeroH (gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s)
          (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) x := by
  set d : ℝ × ℝ × ℝ := (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2)
  set γ : ℝ → ℝ × ℝ × ℝ := gevStep (μ₀, σ₀, 0) d
  have hgood : ∀ s ∈ uIcc (0 : ℝ) 1, 0 < (γ s).2.1 ∧ 0 < 1 + (γ s).2.2 * gevZeroZ (γ s) x := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hm := gevStep_mem_gevZeroNbhd hθ hs.1 hs.2
    have hσ : 0 < (γ s).2.1 := by linarith [(mem_gevZeroNbhd_bounds hm).2.1]
    have hu : 0 < 1 + (γ s).2.2 * gevZeroZ (γ s) x := by
      linarith [neg_abs_le ((γ s).2.2 * gevZeroZ (γ s) x), ht s hs]
    exact ⟨hσ, hu⟩
  set g : ℝ → ℝ := fun s => gevZeroLog (γ s) x + (1 - s) * gevZeroD (γ s) d x
  have hgderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt g ((1 - s) * gevZeroH (γ s) d d x) s := fun s hs => by
    have h1 := hasDerivAt_gevZeroLog_line (θ := (μ₀, σ₀, 0)) (v := d) (x := x) (s := s)
      (hgood s hs).1 (hgood s hs).2
    have h2 := hasDerivAt_gevZeroD_line (θ := (μ₀, σ₀, 0)) (v := d) (w := d) (x := x) (s := s)
      (hgood s hs).1 (hgood s hs).2
    have h3 : HasDerivAt (fun r : ℝ => 1 - r) (-1) s := by simpa using (hasDerivAt_id s).const_sub 1
    refine (h1.add (h3.mul h2)).congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun s => (1 - s) * gevZeroH (γ s) d d x) (uIcc 0 1) := by
    have hH : ContinuousOn (fun s => gevZeroH (γ s) d d x) (uIcc 0 1) := by
      have hrew : (fun s => gevZeroH (γ s) d d x) = fun s =>
          ∑ i : Fin 3, ∑ j : Fin 3, (![d.1, d.2.1, d.2.2] i) * (![d.1, d.2.1, d.2.2] j) *
            gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) x :=
        funext fun s => gevZeroH_eq_sum _ _ _ _
      rw [hrew]
      refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
      refine continuousOn_const.mul ?_
      intro s hs
      have hγc : ContinuousAt (fun r => (γ r, x)) s := by unfold γ gevStep; fun_prop
      exact (ContinuousAt.comp (f := fun r => (γ r, x))
        (g := fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroH p.1 (gevZeroBasis i) (gevZeroBasis j) p.2)
        (continuousAt_gevZeroH_basis (hgood s hs).1 (hgood s hs).2 i j) hγc).continuousWithinAt
    exact (continuous_const.sub continuous_id).continuousOn.mul hH
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hgderiv hcont.intervalIntegrable
  have hg1 : g 1 = gevZeroLog θ x := by simp [g, γ, d, gevStep]
  have hg0 : g 0 = gevZeroLog (μ₀, σ₀, 0) x + gevZeroD (μ₀, σ₀, 0) d x := by simp [g, γ, gevStep]
  rw [hg1, hg0] at hftc
  linarith

/-- Uniform Hessian closeness in probability: for any `ε > 0`, if `θ̂ₙ → (μ₀, σ₀, 0)` in
probability and `|ξ̂ₙ| · max_{i<n} |(Xᵢ - μ₀)/σ₀| → 0` in probability, then the averaged segment
Hessian `Bₙ(i, j)` converges in probability to `-gevFisherInfoZero σ₀ i j`. -/
theorem tendstoInMeasure_avg_gevZeroSegH {μ₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P)
    (hind : iIndepFun X P) {θh : ℕ → Ω → ℝ × ℝ × ℝ}
    (hθcons : TendstoInMeasure P θh atTop (fun _ => (μ₀, σ₀, (0 : ℝ))))
    (hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0)) (i j : Fin 3) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω))
      atTop (fun _ => -gevFisherInfoZero σ₀ i j) := by
  set C₀ : ℝ := 7000 * (1 + σ₀⁻¹ ^ 2)
  have hC₀ : 0 < C₀ := by positivity
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  -- Step 1: choose cutoff `M : ℕ` so `2 * C₀ * E[gevZeroEnvTail M] < ε / 4`
  have htail_lim := tendsto_integral_gevZeroEnvTail (μ₀ := μ₀) hσ₀
  obtain ⟨M, hM_int⟩ := (htail_lim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (8 * C₀) by positivity))).exists
  -- Step 2: choose `δ > 0` for uniform continuity of `gevZeroH` on `|z₀| ≤ M`
  obtain ⟨δ, hδ, hδ_le, hδ_unif⟩ := exists_delta_gevZeroH_sub_le (μ₀ := μ₀) hσ₀ (M : ℝ)
    (Nat.cast_nonneg M) (show (0 : ℝ) < ε / 4 by positivity) i j
  have hδ_σ : δ ≤ σ₀ / 8 := hδ_le.trans (min_le_left _ _)
  have hδ_8 : δ ≤ 1 / 8 := hδ_le.trans ((min_le_right _ _).trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [Nat.cast_nonneg (α := ℝ) M]))
  -- Step 3: SLLN for `gevZeroH (μ₀, σ₀, 0)` and for `gevZeroEnvTail M`
  have hidX : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
    ⟨(hX k).aemeasurable, (hX 0).aemeasurable, by rw [(hX k).map_eq, (hX 0).map_eq]⟩
  have hslln : ∀ (g : ℝ → ℝ), Measurable g →
      Integrable g (gevLocScaleCDF 0 μ₀ hσ₀).measure →
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (X k ω))
        atTop (𝓝 (∫ x, g x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure)) := fun g hgm hgi => by
    have hae := strong_law_ae (fun k ω => g (X k ω))
      ((hX 0).integrable_comp hgi)
      (fun a b hab => (hind.indepFun hab).comp hgm hgm)
      (fun k => (hidX k).comp hgm)
    have hint_eq : ∫ ω, g (X 0 ω) ∂P = ∫ x, g x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure :=
      (hX 0).integral_comp hgm.aestronglyMeasurable
    filter_upwards [hae] with ω hω
    rw [hint_eq] at hω
    simpa [smul_eq_mul] using hω
  have hH_ae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
      atTop (𝓝 (-gevFisherInfoZero σ₀ i j)) := by
    have h := hslln _ (measurable_gevZeroH_zero μ₀ σ₀ (gevZeroBasis i) (gevZeroBasis j))
      (integrable_gevZeroH_zero hσ₀ _ _)
    rwa [integral_gevZeroH_eq_neg_gevFisherInfoZero hσ₀ i j] at h
  have hT_ae : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω))
      atTop (𝓝 (∫ x, gevZeroEnvTail μ₀ σ₀ (M : ℝ) x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure)) :=
    hslln _ (measurable_gevZeroEnvTail μ₀ σ₀ M) (integrable_gevZeroEnvTail hσ₀ M)
  have hH_meas : TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
      atTop (fun _ => -gevFisherInfoZero σ₀ i j) :=
    tendstoInMeasure_of_tendsto_ae (fun n => by
      have hm := measurable_gevZeroH_zero μ₀ σ₀ (gevZeroBasis i) (gevZeroBasis j)
      have hXm := fun k => (hX k).aemeasurable
      exact ((Finset.aemeasurable_fun_sum _ fun k _ => hm.comp_aemeasurable (hXm k)).const_mul
        (n : ℝ)⁻¹).aestronglyMeasurable) hH_ae
  have hT_meas : TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω))
      atTop (fun _ => ∫ x, gevZeroEnvTail μ₀ σ₀ (M : ℝ) x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure) :=
    tendstoInMeasure_of_tendsto_ae (fun n => by
      have hm := measurable_gevZeroEnvTail μ₀ σ₀ M
      have hXm := fun k => (hX k).aemeasurable
      exact ((Finset.aemeasurable_fun_sum _ fun k _ => hm.comp_aemeasurable (hXm k)).const_mul
        (n : ℝ)⁻¹).aestronglyMeasurable) hT_ae
  -- Four bad-event probabilities that each tend to `0`
  have h1 : Tendsto (fun n : ℕ => P {ω | δ ≤ dist (θh n ω) (μ₀, σ₀, (0 : ℝ))}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.1 hθcons) δ hδ
  have h2 : Tendsto (fun n : ℕ => P {ω | (1 / 8 : ℝ) ≤
      |(θh n ω).2.2| * runMax (fun k => |(X k ω - μ₀) / σ₀|) n}) atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_norm.1 hξmax) (1 / 8) (by norm_num)
    refine h.congr fun n => ?_
    congr 1; ext ω
    have hnn : 0 ≤ |(θh n ω).2.2| * runMax (fun k => |(X k ω - μ₀) / σ₀|) n :=
      mul_nonneg (abs_nonneg _) (runMax_nonneg _ _)
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn]
  have h3 : Tendsto (fun n : ℕ => P {ω | ε / 4 ≤
      |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
        (-gevFisherInfoZero σ₀ i j)|}) atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_norm.1 hH_meas) (ε / 4) (by positivity)
    simpa [Real.norm_eq_abs] using h
  set μT := ∫ x, gevZeroEnvTail μ₀ σ₀ (M : ℝ) x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure
  have hη : 0 < ε / (8 * C₀) - μT := sub_pos.2 hM_int
  have h4 : Tendsto (fun n : ℕ => P {ω | ε / (8 * C₀) - μT ≤
      |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) - μT|})
      atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_norm.1 hT_meas) (ε / (8 * C₀) - μT) hη
    simpa [Real.norm_eq_abs] using h
  have hsum_lim : Tendsto (fun n : ℕ =>
      P {ω | δ ≤ dist (θh n ω) (μ₀, σ₀, (0 : ℝ))} +
      P {ω | (1 / 8 : ℝ) ≤ |(θh n ω).2.2| * runMax (fun k => |(X k ω - μ₀) / σ₀|) n} +
      P {ω | ε / 4 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
        (-gevFisherInfoZero σ₀ i j)|} +
      P {ω | ε / (8 * C₀) - μT ≤
        |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) - μT|})
      atTop (𝓝 0) := by
    simpa using ((h1.add h2).add h3).add h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum_lim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsub : {ω | ε ≤ ‖(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω) -
      (-gevFisherInfoZero σ₀ i j)‖} ⊆
      ({ω | δ ≤ dist (θh n ω) (μ₀, σ₀, (0 : ℝ))} ∪
       {ω | (1 / 8 : ℝ) ≤ |(θh n ω).2.2| * runMax (fun k => |(X k ω - μ₀) / σ₀|) n}) ∪
      ({ω | ε / 4 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
          (-gevFisherInfoZero σ₀ i j)|} ∪
       {ω | ε / (8 * C₀) - μT ≤
          |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) - μT|}) := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hnot
    obtain ⟨⟨hθlt, hξlt⟩, ⟨hHlt, hTlt⟩⟩ := hnot
    have hθ1 : |(θh n ω).1 - μ₀| ≤ δ := by
      have : dist (θh n ω).1 μ₀ < δ := (le_max_left _ _).trans_lt hθlt
      rw [Real.dist_eq] at this; exact this.le
    have hθ2 : |(θh n ω).2.1 - σ₀| ≤ δ := by
      have : dist (θh n ω).2.1 σ₀ < δ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hθlt
      rw [Real.dist_eq] at this; exact this.le
    have hθ3 : |(θh n ω).2.2| ≤ δ := by
      have : dist (θh n ω).2.2 0 < δ := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hθlt
      rw [Real.dist_eq, sub_zero] at this; exact this.le
    have hθ_nbhd : θh n ω ∈ gevZeroNbhd μ₀ σ₀ :=
      ⟨⟨by linarith [(abs_le.1 hθ1).1], by linarith [(abs_le.1 hθ1).2]⟩,
       ⟨by linarith [(abs_le.1 hθ2).1], by linarith [(abs_le.1 hθ2).2]⟩,
       by linarith [(abs_le.1 hθ3).1], by linarith [(abs_le.1 hθ3).2]⟩
    -- Pointwise bound on `|gevZeroSegH - gevZeroH (μ₀, σ₀, 0)|` for every `k < n`
    have hpt : ∀ k ∈ Finset.range n,
        |gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω) -
          gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)| ≤
        ε / 4 + 2 * C₀ * gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) := by
      intro k hk
      have hk_lt : k < n := Finset.mem_range.1 hk
      set d : ℝ × ℝ × ℝ := ((θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2)
      set γ : ℝ → ℝ × ℝ × ℝ := gevStep (μ₀, σ₀, 0) d
      have hseg_t : ∀ s ∈ Icc (0 : ℝ) 1, |(γ s).2.2 * gevZeroZ (γ s) (X k ω)| ≤ 1 / 2 := by
        intro s hs
        have hm := gevStep_mem_gevZeroNbhd hθ_nbhd hs.1 hs.2
        have hz := abs_gevZeroZ_le hσ₀ hm (x := X k ω)
        have hξs : |(γ s).2.2| ≤ |(θh n ω).2.2| := by
          simp only [γ, d, gevStep, zero_add, abs_mul, abs_of_nonneg hs.1]
          nlinarith [hs.2, abs_nonneg (θh n ω).2.2]
        have hrm : |(X k ω - μ₀) / σ₀| ≤ runMax (fun m => |(X m ω - μ₀) / σ₀|) n :=
          le_runMax (fun m => |(X m ω - μ₀) / σ₀|) hk_lt
        rw [abs_mul]
        calc |(γ s).2.2| * |gevZeroZ (γ s) (X k ω)|
            ≤ |(θh n ω).2.2| * (2 * (1 + |(X k ω - μ₀) / σ₀|)) :=
              mul_le_mul hξs hz (abs_nonneg _) (abs_nonneg _)
          _ ≤ |(θh n ω).2.2| * (2 * (1 + runMax (fun m => |(X m ω - μ₀) / σ₀|) n)) := by
              gcongr
          _ = 2 * |(θh n ω).2.2| + 2 * (|(θh n ω).2.2| * runMax (fun m => |(X m ω - μ₀) / σ₀|) n) := by
              ring
          _ ≤ 2 * (1 / 8) + 2 * (1 / 8) := by linarith [hθ3.trans hδ_8]
          _ = 1 / 2 := by norm_num
      have hconst_int : gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) =
          ∫ _s in (0 : ℝ)..1, gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) := by
        simp
      have hcont_s : ContinuousOn (fun s => gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
          (uIcc 0 1) := by
        intro s hs
        rw [uIcc_of_le zero_le_one] at hs
        have hm := gevStep_mem_gevZeroNbhd hθ_nbhd hs.1 hs.2
        have hσs : 0 < (γ s).2.1 := by linarith [(mem_gevZeroNbhd_bounds hm).2.1]
        have hus : 0 < 1 + (γ s).2.2 * gevZeroZ (γ s) (X k ω) := by
          linarith [neg_abs_le ((γ s).2.2 * gevZeroZ (γ s) (X k ω)), hseg_t s hs]
        have hγc : ContinuousAt (fun r => (γ r, X k ω)) s := by unfold γ gevStep; fun_prop
        exact (ContinuousAt.comp (f := fun r => (γ r, X k ω))
          (g := fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroH p.1 (gevZeroBasis i) (gevZeroBasis j) p.2)
          (continuousAt_gevZeroH_basis hσs hus i j) hγc).continuousWithinAt
      rw [gevZeroSegH, hconst_int, ← intervalIntegral.integral_sub hcont_s.intervalIntegrable
        intervalIntegrable_const]
      have hle_s : ∀ s ∈ Ioc (0 : ℝ) 1,
          |gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
            gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)| ≤
          ε / 4 + 2 * C₀ * gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) := by
        intro s hs
        have hsIcc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
        by_cases hM : |(X k ω - μ₀) / σ₀| ≤ (M : ℝ)
        · have h1s : |(γ s).1 - μ₀| ≤ δ := by
            simp only [γ, d, gevStep, add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1.le]
            nlinarith [hs.2, abs_nonneg ((θh n ω).1 - μ₀)]
          have h2s : |(γ s).2.1 - σ₀| ≤ δ := by
            simp only [γ, d, gevStep, add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1.le]
            nlinarith [hs.2, abs_nonneg ((θh n ω).2.1 - σ₀)]
          have h3s : |(γ s).2.2| ≤ δ := by
            simp only [γ, d, gevStep, zero_add, abs_mul, abs_of_nonneg hs.1.le]
            nlinarith [hs.2, abs_nonneg (θh n ω).2.2]
          have hu := hδ_unif (γ s) h1s h2s h3s (X k ω) hM
          linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * C₀)
            (gevZeroEnvTail_nonneg μ₀ σ₀ M (X k ω))]
        · push Not at hM
          have htail_eq : gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) = gevZeroEnv μ₀ σ₀ (X k ω) :=
            Set.indicator_of_mem (show X k ω ∈ {x | (M : ℝ) < |(x - μ₀) / σ₀|} from hM) _
          rw [htail_eq]
          have hb1 := abs_gevZeroH_basis_le hσ₀ (gevStep_mem_gevZeroNbhd hθ_nbhd hs.1.le hs.2)
            (hseg_t s hsIcc) i j
          have h0_nbhd : (μ₀, σ₀, (0 : ℝ)) ∈ gevZeroNbhd μ₀ σ₀ :=
            ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by norm_num, by norm_num⟩
          have hb0 := abs_gevZeroH_basis_le hσ₀ h0_nbhd (by simp) i j (x := X k ω)
          have htri := abs_sub (gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
            (gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
          linarith
      have hint_bd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (f := fun s => gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
          gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
        (C := ε / 4 + 2 * C₀ * gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω))
        (fun s hs => by
          rw [uIoc_of_le zero_le_one] at hs
          simpa [Real.norm_eq_abs] using hle_s s hs)
      simpa [Real.norm_eq_abs] using hint_bd
    -- Sum over `k < n`
    have hdiff_avg : |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω) -
        (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)| ≤
        ε / 4 + 2 * C₀ * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hn0)]
      calc (n : ℝ)⁻¹ * |∑ k ∈ Finset.range n, (gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω) -
              gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))|
          ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, |gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω) -
              gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hn0.le)
        _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (ε / 4 + 2 * C₀ * gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (inv_nonneg.2 hn0.le)
        _ = ε / 4 + 2 * C₀ * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.mul_sum]
            field_simp [hn0.ne']
    have hT_bd : (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) < ε / (8 * C₀) := by
      linarith [(abs_lt.1 hTlt).2]
    have h2CT : 2 * C₀ * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) <
        ε / 4 := by
      have h1 := mul_lt_mul_of_pos_left hT_bd (show (0 : ℝ) < 2 * C₀ by positivity)
      have heq : 2 * C₀ * (ε / (8 * C₀)) = ε / 4 := by field_simp [hC₀.ne']; ring
      linarith
    simp only [mem_ofPred_eq, Real.norm_eq_abs] at hω
    have htri := abs_sub_le
      ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω))
      ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
      (-gevFisherInfoZero σ₀ i j)
    linarith
  refine (measure_mono hsub).trans ?_
  calc P _ ≤ (P _ + P _) + (P _ + P _) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ = _ := by ring

/-- The trivariate score CLT at `ξ = 0`, linearly transformed by `B = (gevFisherInfoZero σ)⁻¹`. -/
theorem tendstoInDistribution_gumbelScore3Lin {μ₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P)
    (hind : iIndepFun X P) {B S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.PosSemidef)
    (hB : B * gevFisherInfoZero σ₀ * B.transpose = S)
    {W : Ω' → EuclideanSpace ℝ (Fin 3)} (hW : HasLaw W (multivariateGaussian 0 S) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n,
        WithLp.toLp 2 (B.mulVec (gumbelScoreVec3 μ₀ σ₀ (X i ω))))
      atTop W (fun _ => P) P' := by
  have hmeas_lin : Measurable fun x : ℝ => WithLp.toLp 2 (B.mulVec (gumbelScoreVec3 μ₀ σ₀ x)) := by
    refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.measurable_sum _ fun j _ => Measurable.const_mul ?_ _
    exact (continuous_apply j).measurable.comp ((WithLp.measurable_ofLp 2 _).comp
      (measurable_gumbelScoreVec3 μ₀ σ₀))
  refine TendstoInDistribution.of_inner hW.aemeasurable (fun n => ?_) fun v => ?_
  · exact (Finset.aemeasurable_fun_sum _ fun i _ =>
      hmeas_lin.comp_aemeasurable (hX i).aemeasurable).const_smul (√(n : ℝ))⁻¹
  set t : Fin 3 → ℝ := fun i => v i with ht
  set u : Fin 3 → ℝ := B.transpose.mulVec t with hu
  set f : ℝ → ℝ := fun x => u 0 * gumbelScoreMu μ₀ σ₀ x + u 1 * gumbelScoreSigma μ₀ σ₀ x +
    u 2 * gumbelScoreXi μ₀ σ₀ x with hf_def
  have hf : Measurable f := by
    have := measurable_gumbelScoreMu μ₀ σ₀; have := measurable_gumbelScoreSigma μ₀ σ₀
    have := measurable_gumbelScoreXi μ₀ σ₀; unfold f; fun_prop
  have hinner : ∀ x, ⟪WithLp.toLp 2 (B.mulVec (gumbelScoreVec3 μ₀ σ₀ x)), v⟫ = f x := fun x => by
    have h1 : f x = u ⬝ᵥ (gumbelScoreVec3 μ₀ σ₀ x).ofLp := by
      simp [hf_def, dotProduct, Fin.sum_univ_three, gumbelScoreVec3]
    have h2 : u ⬝ᵥ (gumbelScoreVec3 μ₀ σ₀ x).ofLp = t ⬝ᵥ B.mulVec (gumbelScoreVec3 μ₀ σ₀ x).ofLp := by
      simp only [hu]
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    rw [h1, h2]
    simp [PiLp.inner_apply, dotProduct, ht, Fin.sum_univ_three, mul_comm]
  set Y : ℕ → Ω → ℝ := fun i => f ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => f) (fun _ => hf)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hf
  have hmemLp : MemLp (Y 0) 2 P := by
    rw [← memLp_map_measure_iff hf.aestronglyMeasurable (hX 0).aemeasurable, (hX 0).map_eq]
    exact memLp_lin_gumbelScore3 hσ₀ _ _ _
  have hint : ∀ g : ℝ → ℝ, Measurable g →
      P[g ∘ X 0] = ∫ x, g x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure :=
    fun g hg => (hX 0).integral_comp hg.aestronglyMeasurable
  have hmean : P[Y 0] = 0 := by
    rw [hint f hf]
    exact integral_lin_gumbelScore (μ := μ₀) hσ₀ (u 0) (u 1) (u 2)
  have hvar : Var[Y 0; P] = v ⬝ᵥ S *ᵥ v := by
    rw [variance_of_integral_eq_zero (hf.comp_aemeasurable (hX 0).aemeasurable) hmean]
    have := hint (fun x => f x ^ 2) (hf.pow_const 2)
    simp only [Function.comp_def] at this ⊢
    have key : u ⬝ᵥ gevFisherInfoZero σ₀ *ᵥ u = t ⬝ᵥ S *ᵥ t := by
      rw [← hB]
      simp only [hu]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec t B,
        ← Matrix.mulVec_transpose]
    rw [this, integral_lin_gumbelScore3_sq hσ₀]
    exact key
  have hZt : HasLaw (fun ω => ⟪W ω, v⟫) (gaussianReal 0 Var[Y 0; P].toNNReal) P' := by
    rw [hvar]
    exact hasLaw_inner_multivariateGaussian hS hW v
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZt hmemLp hind' hident
  rw [hmean] at hclt
  convert hclt using 3 with n ω
  rw [inner_smul_left, sum_inner]
  simp [Y, hinner]

/-- Norm bound `‖E *ᵥ v‖ ≤ (∑ i, ∑ j, |E i j|) * ‖v‖` on `EuclideanSpace ℝ (Fin 3)`. -/
private lemma norm_mulVec_le_sum_abs (E : Matrix (Fin 3) (Fin 3) ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    ‖WithLp.toLp 2 (E.mulVec v.ofLp)‖ ≤ (∑ i : Fin 3, ∑ j : Fin 3, |E i j|) * ‖v‖ := by
  have hcoord : ∀ i : Fin 3, |(E.mulVec v.ofLp) i| ≤ (∑ j : Fin 3, |E i j|) * ‖v‖ := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    calc |∑ j : Fin 3, E i j * v j|
        ≤ ∑ j : Fin 3, |E i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3, |E i j| * ‖v‖ := Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j)
              (abs_nonneg _)
      _ = (∑ j : Fin 3, |E i j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
  have hl1 : ‖WithLp.toLp 2 (E.mulVec v.ofLp)‖ ≤ ∑ i : Fin 3, |(E.mulVec v.ofLp) i| := by
    have hsq : ‖WithLp.toLp 2 (E.mulVec v.ofLp)‖ ^ 2 = ∑ i : Fin 3, |(E.mulVec v.ofLp) i| ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs]
    have hle : ∑ i : Fin 3, |(E.mulVec v.ofLp) i| ^ 2 ≤ (∑ i : Fin 3, |(E.mulVec v.ofLp) i|) ^ 2 := by
      simp only [Fin.sum_univ_three]
      nlinarith [abs_nonneg ((E.mulVec v.ofLp) 0), abs_nonneg ((E.mulVec v.ofLp) 1),
        abs_nonneg ((E.mulVec v.ofLp) 2)]
    nlinarith [norm_nonneg (WithLp.toLp 2 (E.mulVec v.ofLp)),
      Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg ((E.mulVec v.ofLp) i)]
  calc ‖WithLp.toLp 2 (E.mulVec v.ofLp)‖
      ≤ ∑ i : Fin 3, |(E.mulVec v.ofLp) i| := hl1
    _ ≤ ∑ i : Fin 3, (∑ j : Fin 3, |E i j|) * ‖v‖ := Finset.sum_le_sum fun i _ => hcoord i
    _ = (∑ i : Fin 3, ∑ j : Fin 3, |E i j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm

/-- **Asymptotic normality of three-parameter GEV local MLEs at `ξ₀ = 0`** in `(μ, σ, ξ)` order:
if `θ̂ₙ = (μ̂ₙ, σ̂ₙ, ξ̂ₙ)` are measurable estimators such that:
1. `θ̂ₙ → (μ₀, σ₀, 0)` in probability,
2. `|ξ̂ₙ| · max_{i<n} |(Xᵢ - μ₀)/σ₀| → 0` in probability, and
3. with probability tending to `1`, `θ̂ₙ` is an admissible local maximizer of `gevLogLikE`,
then `√n (μ̂ₙ - μ₀, σ̂ₙ - σ₀, ξ̂ₙ) ⇒ N(0, (gevFisherInfoZero σ₀)⁻¹)`. -/
theorem tendstoInDistribution_gevLocalMLE_zero_muSigmaXi {μ₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P)
    (hind : iIndepFun X P) {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : TendstoInMeasure P θh atTop (fun _ => (μ₀, σ₀, (0 : ℝ))))
    (hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0))
    (hloc : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.2.2 p.1 p.2.1 (fun i : Fin n => X i ω)) (θh n ω)})
      atTop (𝓝 0))
    {W : Ω' → EuclideanSpace ℝ (Fin 3)}
    (hW : HasLaw W (multivariateGaussian 0 (gevFisherInfoZero σ₀)⁻¹) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2])
      atTop W (fun _ => P) P' := by
  set I₀ := gevFisherInfoZero σ₀
  set I₀inv := I₀⁻¹
  have hI₀pos : I₀.PosDef := posDef_gevFisherInfoZero hσ₀
  have hI₀inv_pos : I₀inv.PosDef := hI₀pos.inv
  have hI₀_sym : I₀.transpose = I₀ := by
    have := hI₀pos.isHermitian
    ext i j; simpa [Matrix.conjTranspose_apply] using congrFun (congrFun this i) j
  have hI₀inv_sym : I₀inv.transpose = I₀inv := by
    have := hI₀inv_pos.isHermitian
    ext i j; simpa [Matrix.conjTranspose_apply] using congrFun (congrFun this i) j
  have hdet : IsUnit I₀.det := isUnit_iff_ne_zero.2 hI₀pos.det_pos.ne'
  have hmul : I₀inv * I₀ = 1 := Matrix.nonsing_inv_mul I₀ hdet
  have hB : I₀inv * I₀ * I₀inv.transpose = I₀inv := by
    rw [hmul, Matrix.one_mul, hI₀inv_sym]
  -- Normalized linear score `V n ω = I₀⁻¹ *ᵥ S n ω ⇒ W`
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω =>
    (√(n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, WithLp.toLp 2 (I₀inv.mulVec (gumbelScoreVec3 μ₀ σ₀ (X k ω)))
  set T : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω =>
    √(n : ℝ) • !₂[(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2]
  have hV : TendstoInDistribution V atTop W (fun _ => P) P' :=
    tendstoInDistribution_gumbelScore3Lin hσ₀ hX hind hI₀inv_pos.posSemidef hB hW
  have hTm : ∀ n, AEMeasurable (T n) P := fun n => by
    have hm := hθm n
    have h0 : AEMeasurable (fun ω => (θh n ω).1 - μ₀) P := (measurable_fst.comp_aemeasurable hm).sub_const _
    have h1 : AEMeasurable (fun ω => (θh n ω).2.1 - σ₀) P :=
      ((measurable_fst.comp measurable_snd).comp_aemeasurable hm).sub_const _
    have h2 : AEMeasurable (fun ω => (θh n ω).2.2) P :=
      (measurable_snd.comp measurable_snd).comp_aemeasurable hm
    have hpi : AEMeasurable (fun ω => ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2]) P :=
      aemeasurable_pi_iff.2 fun i => by fin_cases i <;> simpa using ‹_›
    exact ((WithLp.measurable_toLp 2 _).comp_aemeasurable hpi).const_smul (√(n : ℝ))
  -- Entrywise convergence of `B n ω i j → -I₀ i j` in probability
  set B : ℕ → Ω → Matrix (Fin 3) (Fin 3) ℝ := fun n ω =>
    Matrix.of fun i j => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω)
  set E : ℕ → Ω → Matrix (Fin 3) (Fin 3) ℝ := fun n ω => 1 + I₀inv * B n ω
  have hB_lim : ∀ i j : Fin 3,
      TendstoInMeasure P (fun n ω => B n ω i j) atTop (fun _ => -I₀ i j) := fun i j =>
    tendstoInMeasure_avg_gevZeroSegH hσ₀ hX hind hcons hξmax i j
  -- Show `e n ω := ∑ i, ∑ j, |E n ω i j| → 0` in probability
  set e : ℕ → Ω → ℝ := fun n ω => ∑ i : Fin 3, ∑ j : Fin 3, |E n ω i j|
  have he_lim : TendstoInMeasure P e atTop (fun _ => 0) := by
    have hE_eq : ∀ n ω (i j : Fin 3),
        E n ω i j = ∑ l : Fin 3, I₀inv i l * (B n ω l j - (-I₀ l j)) := fun n ω i j => by
      have h10 : (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = (I₀inv * I₀) i j := by rw [hmul]
      simp only [E, Matrix.add_apply, Matrix.mul_apply, h10]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => by ring
    set C_I : ℝ := 1 + ∑ i : Fin 3, ∑ l : Fin 3, |I₀inv i l|
    have hCI : 0 < C_I := by
      have : 0 ≤ ∑ i : Fin 3, ∑ l : Fin 3, |I₀inv i l| :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    set δB : ℝ := ε / (9 * C_I)
    have hδB : 0 < δB := by positivity
    have hlim9 : Tendsto (fun n : ℕ =>
        ∑ l : Fin 3, ∑ j : Fin 3, P {ω | δB ≤ |B n ω l j - (-I₀ l j)|}) atTop (𝓝 0) := by
      have : (0 : ENNReal) = ∑ _l : Fin 3, ∑ _j : Fin 3, (0 : ENNReal) := by simp
      rw [this]
      refine tendsto_finsetSum _ fun l _ => tendsto_finsetSum _ fun j _ => ?_
      simpa [Real.norm_eq_abs] using (tendstoInMeasure_iff_norm.1 (hB_lim l j)) δB hδB
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim9
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
    have hsub : {ω | ε ≤ ‖e n ω - 0‖} ⊆ ⋃ l : Fin 3, ⋃ j : Fin 3, {ω | δB ≤ |B n ω l j - (-I₀ l j)|} := by
      intro ω hω
      by_contra hnot
      simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hnot
      have hE_le : ∀ i j : Fin 3, |E n ω i j| ≤ (∑ l : Fin 3, |I₀inv i l|) * δB := fun i j => by
        rw [hE_eq n ω i j]
        calc |∑ l : Fin 3, I₀inv i l * (B n ω l j - (-I₀ l j))|
            ≤ ∑ l : Fin 3, |I₀inv i l * (B n ω l j - (-I₀ l j))| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ l : Fin 3, |I₀inv i l| * δB := Finset.sum_le_sum fun l _ => by
                rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hnot l j).le (abs_nonneg _)
          _ = (∑ l : Fin 3, |I₀inv i l|) * δB := (Finset.sum_mul _ _ _).symm
      have he_le : e n ω ≤ 3 * C_I * δB := by
        calc e n ω = ∑ i : Fin 3, ∑ j : Fin 3, |E n ω i j| := rfl
          _ ≤ ∑ i : Fin 3, ∑ _j : Fin 3, (∑ l : Fin 3, |I₀inv i l|) * δB :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hE_le i j
          _ = 3 * (∑ i : Fin 3, ∑ l : Fin 3, |I₀inv i l|) * δB := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                Nat.cast_ofNat, ← Finset.mul_sum, ← Finset.sum_mul]
              ring
          _ ≤ 3 * C_I * δB := by
              have hle_CI : ∑ i : Fin 3, ∑ l : Fin 3, |I₀inv i l| ≤ C_I := by simp only [C_I]; linarith
              exact mul_le_mul_of_nonneg_right (by linarith) hδB.le
      have he0 : 0 ≤ e n ω := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
      simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg he0] at hω
      have h3C : 3 * C_I * δB = ε / 3 := by simp only [δB]; field_simp [hCI.ne']; ring
      linarith
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le P _).trans ?_)
    exact Finset.sum_le_sum fun l _ => measure_iUnion_fintype_le P _
  -- Show `T - V → 0` in probability via `‖T - V‖ ≤ 2 * e * ‖V‖` on the high-probability good event!
  have hdiff : TendstoInMeasure P (T - V) atTop 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    have hη5 : 0 < η / 5 := ENNReal.div_pos hη.ne' (by norm_num)
    obtain ⟨M, hM⟩ := hV.exists_measure_le_norm_le hη5
    set M' := max M 1 with hM'
    have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
    set δe : ℝ := min (1 / 2) (ε / (2 * M'))
    have hδe : 0 < δe := lt_min (by norm_num) (by positivity)
    set δθ : ℝ := min (σ₀ / 8) (1 / 8)
    have hδθ : 0 < δθ := lt_min (by positivity) (by norm_num)
    have hp1 : ∀ᶠ n in atTop, P {ω | δθ ≤ dist (θh n ω) (μ₀, σ₀, (0 : ℝ))} ≤ η / 5 :=
      (((tendstoInMeasure_iff_dist.1 hcons) δθ hδθ).eventually (gt_mem_nhds hη5)).mono fun _ h => h.le
    have hp2 : ∀ᶠ n in atTop, P {ω | (1 / 8 : ℝ) ≤
        |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n} ≤ η / 5 := by
      have h := (tendstoInMeasure_iff_norm.1 hξmax) (1 / 8) (by norm_num)
      refine (h.eventually (gt_mem_nhds hη5)).mono fun n hn => ?_
      have heq : {ω | (1 / 8 : ℝ) ≤ |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n} =
          {ω | (1 / 8 : ℝ) ≤ ‖|(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n - 0‖} := by
        ext ω
        have hnn : 0 ≤ |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n :=
          mul_nonneg (abs_nonneg _) (runMax_nonneg _ _)
        simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn]
      rw [heq]; exact hn.le
    have hp3 : ∀ᶠ n in atTop, P {ω | ¬ IsLocalMax
        (fun p : ℝ × ℝ × ℝ => gevLogLikE p.2.2 p.1 p.2.1 (fun i : Fin n => X i ω)) (θh n ω)} ≤ η / 5 :=
      (hloc.eventually (gt_mem_nhds hη5)).mono fun _ h => h.le
    have hp4 : ∀ᶠ n in atTop, P {ω | δe ≤ e n ω} ≤ η / 5 := by
      have h := (tendstoInMeasure_iff_norm.1 he_lim) δe hδe
      refine (h.eventually (gt_mem_nhds hη5)).mono fun n hn => ?_
      have heq : {ω | δe ≤ e n ω} = {ω | δe ≤ ‖e n ω - 0‖} := by
        ext ω
        have hnn : 0 ≤ e n ω := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
        simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn]
      rw [heq]; exact hn.le
    filter_upwards [eventually_ge_atTop 1, hM, hp1, hp2, hp3, hp4] with n hn hMn h1 h2 h3 h4
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq0 : 0 < √(n : ℝ) := sqrt_pos.2 hn0
    have hsub : {ω | ε ≤ ‖(T - V) n ω - 0‖} ⊆
        ({ω | M ≤ ‖V n ω‖} ∪ {ω | δθ ≤ dist (θh n ω) (μ₀, σ₀, (0 : ℝ))}) ∪
        ({ω | (1 / 8 : ℝ) ≤ |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n} ∪
         ({ω | ¬ IsLocalMax (fun p : ℝ × ℝ × ℝ => gevLogLikE p.2.2 p.1 p.2.1 (fun i : Fin n => X i ω))
            (θh n ω)} ∪ {ω | δe ≤ e n ω})) := by
      intro ω hω
      by_contra hnot
      simp only [mem_union, mem_ofPred_eq, not_or, not_le, not_not] at hnot
      obtain ⟨⟨hVlt, hθlt⟩, ⟨hξlt, hlocω, helt⟩⟩ := hnot
      have hθ1 : |(θh n ω).1 - μ₀| ≤ δθ := by
        have : dist (θh n ω).1 μ₀ < δθ := (le_max_left _ _).trans_lt hθlt
        rw [Real.dist_eq] at this; exact this.le
      have hθ2 : |(θh n ω).2.1 - σ₀| ≤ δθ := by
        have : dist (θh n ω).2.1 σ₀ < δθ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hθlt
        rw [Real.dist_eq] at this; exact this.le
      have hθ3 : |(θh n ω).2.2| ≤ δθ := by
        have : dist (θh n ω).2.2 0 < δθ := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hθlt
        rw [Real.dist_eq, sub_zero] at this; exact this.le
      have hθ_nbhd : θh n ω ∈ gevZeroNbhd μ₀ σ₀ :=
        ⟨⟨by linarith [(abs_le.1 hθ1).1, min_le_left (σ₀ / 8) (1 / 8)],
          by linarith [(abs_le.1 hθ1).2, min_le_left (σ₀ / 8) (1 / 8)]⟩,
         ⟨by linarith [(abs_le.1 hθ2).1, min_le_left (σ₀ / 8) (1 / 8)],
          by linarith [(abs_le.1 hθ2).2, min_le_left (σ₀ / 8) (1 / 8)]⟩,
         by linarith [(abs_le.1 hθ3).1, min_le_right (σ₀ / 8) (1 / 8)],
         by linarith [(abs_le.1 hθ3).2, min_le_right (σ₀ / 8) (1 / 8)]⟩
      have hσθ : 0 < (θh n ω).2.1 := by linarith [(mem_gevZeroNbhd_bounds hθ_nbhd).2.1]
      -- All observations `k < n` stay inside `|ξ(s) z_k(s)| ≤ 1/2` along the segment
      have hseg : ∀ k < n, ∀ s ∈ Icc (0 : ℝ) 1,
          |(gevStep (μ₀, σ₀, 0) ((θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2) s).2.2 *
            gevZeroZ (gevStep (μ₀, σ₀, 0) ((θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2) s) (X k ω)| ≤ 1 / 2 := by
        intro k hk s hs
        have hm := gevStep_mem_gevZeroNbhd hθ_nbhd hs.1 hs.2
        have hz := abs_gevZeroZ_le hσ₀ hm (x := X k ω)
        have hξs : |(gevStep (μ₀, σ₀, 0) ((θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2) s).2.2| ≤
            |(θh n ω).2.2| := by
          simp only [gevStep, zero_add, abs_mul, abs_of_nonneg hs.1]
          nlinarith [hs.2, abs_nonneg (θh n ω).2.2]
        have hrm : |(X k ω - μ₀) / σ₀| ≤ runMax (fun m => |(X m ω - μ₀) / σ₀|) n :=
          le_runMax (fun m => |(X m ω - μ₀) / σ₀|) hk
        rw [abs_mul]
        calc _ ≤ |(θh n ω).2.2| * (2 * (1 + |(X k ω - μ₀) / σ₀|)) :=
              mul_le_mul hξs hz (abs_nonneg _) (abs_nonneg _)
          _ ≤ |(θh n ω).2.2| * (2 * (1 + runMax (fun m => |(X m ω - μ₀) / σ₀|) n)) := by gcongr
          _ = 2 * |(θh n ω).2.2| + 2 * (|(θh n ω).2.2| * runMax (fun m => |(X m ω - μ₀) / σ₀|) n) := by ring
          _ ≤ 2 * (1 / 8) + 2 * (1 / 8) := by linarith [hθ3.trans (min_le_right _ _)]
          _ = 1 / 2 := by norm_num
      -- Admissibility at `θh n ω` (from `s = 1`)
      have hadm : ∀ k : Fin n, 0 < 1 + (θh n ω).2.2 * gevZeroZ (θh n ω) (X k ω) := fun k => by
        have hs1 := hseg k.1 k.2 1 ⟨zero_le_one, le_rfl⟩
        have hst : gevStep (μ₀, σ₀, 0) ((θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2) 1 = θh n ω := by
          simp [gevStep]
        rw [hst] at hs1
        linarith [neg_abs_le ((θh n ω).2.2 * gevZeroZ (θh n ω) (X k ω))]
      -- Score vanishes at `θh n ω`
      have hscore0 : ∀ i : Fin 3, ∑ k ∈ Finset.range n, gevZeroD (θh n ω) (gevZeroBasis i) (X k ω) = 0 := by
        intro i
        have hfin := sum_gevZeroD_eq_zero_of_isLocalMax hσθ hadm hlocω (gevZeroBasis i)
        rwa [Fin.sum_univ_eq_sum_range (fun k => gevZeroD (θh n ω) (gevZeroBasis i) (X k ω)) n] at hfin
      -- FTC gives `B n ω *ᵥ T n ω = -S n ω`
      set S_vec : Fin 3 → ℝ := fun i =>
        (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω) i
      have hBT : (B n ω).mulVec (T n ω).ofLp = -S_vec := by
        ext i
        have hsum_ftc : ∑ k ∈ Finset.range n,
            (gevZeroD (θh n ω) (gevZeroBasis i) (X k ω) -
              gevZeroD (μ₀, σ₀, 0) (gevZeroBasis i) (X k ω)) =
            ∑ k ∈ Finset.range n, ∑ j : Fin 3,
              (![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j) *
                gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω) :=
          Finset.sum_congr rfl fun k hk =>
            gevZeroD_sub_eq_sum_segH hσ₀ hθ_nbhd (hseg k (Finset.mem_range.1 hk)) i
        rw [Finset.sum_sub_distrib, hscore0 i, zero_sub, Finset.sum_comm] at hsum_ftc
        have hD0 : ∀ k, gevZeroD (μ₀, σ₀, 0) (gevZeroBasis i) (X k ω) =
            gumbelScoreVec3 μ₀ σ₀ (X k ω) i := fun k => gevZeroD_basis_zero μ₀ σ₀ (X k ω) i
        simp_rw [hD0] at hsum_ftc
        simp only [B, T, S_vec, Matrix.mulVec, dotProduct, Matrix.of_apply, PiLp.smul_apply,
          smul_eq_mul, Pi.neg_apply]
        have hlhs : ∑ j : Fin 3, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω)) *
            (√(n : ℝ) * ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j) =
            (√(n : ℝ))⁻¹ * ∑ j : Fin 3, ∑ k ∈ Finset.range n,
              ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j *
                gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum]
          have hsq2 : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
          have : (n : ℝ)⁻¹ * √(n : ℝ) = (√(n : ℝ))⁻¹ :=
            calc (n : ℝ)⁻¹ * √(n : ℝ) = (√(n : ℝ) * √(n : ℝ))⁻¹ * √(n : ℝ) := by rw [hsq2]
              _ = (√(n : ℝ))⁻¹ := by rw [mul_inv, mul_assoc, inv_mul_cancel₀ hsq0.ne', mul_one]
          calc ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω)) *
                (√(n : ℝ) * ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j)
              = ((n : ℝ)⁻¹ * √(n : ℝ)) * (![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j *
                  ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω)) := by ring
            _ = (√(n : ℝ))⁻¹ * (![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j *
                  ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω)) := by rw [this]
        rw [hlhs, ← hsum_ftc]
        ring
      -- Check `V n ω = toLp 2 (I₀inv *ᵥ S_vec)`
      have hV_eq : (V n ω).ofLp = I₀inv.mulVec S_vec := by
        ext i
        simp only [V, S_vec, Matrix.mulVec, dotProduct, PiLp.smul_apply, WithLp.ofLp_sum,
          Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
      -- Exact identity `T n ω - V n ω = toLp 2 (E n ω *ᵥ T n ω)`
      have hTV : T n ω - V n ω = WithLp.toLp 2 ((E n ω).mulVec (T n ω).ofLp) := by
        ext i
        have h1 : ((E n ω).mulVec (T n ω).ofLp) i =
            (T n ω).ofLp i + (I₀inv.mulVec ((B n ω).mulVec (T n ω).ofLp)) i := by
          simp only [E, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Pi.add_apply]
        simp only [PiLp.sub_apply]
        rw [hV_eq, h1, hBT, Matrix.mulVec_neg]
        simp [sub_eq_add_neg]
      have hnorm_TV : ‖T n ω - V n ω‖ ≤ e n ω * ‖T n ω‖ := by
        rw [hTV]; exact norm_mulVec_le_sum_abs (E n ω) (T n ω)
      have he_half : e n ω ≤ 1 / 2 := helt.le.trans (min_le_left _ _)
      have hT_le : ‖T n ω‖ ≤ 2 * ‖V n ω‖ := by
        have htri : ‖T n ω‖ ≤ ‖T n ω - V n ω‖ + ‖V n ω‖ := by
          simpa [sub_add_cancel] using norm_add_le (T n ω - V n ω) (V n ω)
        nlinarith [norm_nonneg (T n ω)]
      have hTV_lt : ‖T n ω - V n ω‖ < ε := by
        have hV_M' : ‖V n ω‖ < M' := lt_of_lt_of_le hVlt (le_max_left _ _)
        have h1 : e n ω * ‖T n ω‖ ≤ e n ω * (2 * ‖V n ω‖) :=
          mul_le_mul_of_nonneg_left hT_le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        have h3 : δe * (2 * M') ≤ ε := by
          have : δe ≤ ε / (2 * M') := min_le_right _ _
          have := mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ 2 * M' by positivity)
          rwa [div_mul_cancel₀ _ (by positivity)] at this
        have h2 : e n ω * (2 * ‖V n ω‖) < ε :=
          calc e n ω * (2 * ‖V n ω‖) ≤ δe * (2 * ‖V n ω‖) :=
                mul_le_mul_of_nonneg_right helt.le (by positivity)
            _ < δe * (2 * M') := mul_lt_mul_of_pos_left (by linarith) hδe
            _ ≤ ε := h3
        linarith
      simp only [mem_ofPred_eq, Pi.sub_apply, sub_zero] at hω
      linarith
    have hle5 : (η / 5) + (η / 5) + ((η / 5) + ((η / 5) + (η / 5))) = η := by
      have h5 : (5 : ENNReal) ≠ 0 := by norm_num
      have h5t : (5 : ENNReal) ≠ ⊤ := by norm_num
      have hsum : (η / 5) + (η / 5) + ((η / 5) + ((η / 5) + (η / 5))) = 5 * (η / 5) := by ring
      rw [hsum, mul_comm, ENNReal.div_mul_cancel h5 h5t]
    refine (measure_mono hsub).trans ?_
    have hm1 := (measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add hMn h1))
      ((measure_union_le _ _).trans (add_le_add h2
        ((measure_union_le _ _).trans (add_le_add h3 h4)))))
    exact hm1.trans hle5.le
  exact tendstoInDistribution_of_tendstoInMeasure_sub T W hV hdiff hTm

/-- The asymptotic covariance of the three-parameter GEV MLE at `ξ₀ = 0`, in the library's
parameter order `(ξ, μ, σ)`: `(gevFisherInfoZero σ)⁻¹` permuted by `(2, 0, 1)`. -/
noncomputable def gevMLECovZero (σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (gevFisherInfoZero σ)⁻¹.submatrix ![2, 0, 1] ![2, 0, 1]

theorem posDef_gevMLECovZero {σ : ℝ} (hσ : 0 < σ) : (gevMLECovZero σ).PosDef :=
  (posDef_gevFisherInfoZero hσ).inv.submatrix (by decide)

theorem posSemidef_gevMLECovZero {σ : ℝ} (hσ : 0 < σ) : (gevMLECovZero σ).PosSemidef :=
  (posDef_gevMLECovZero hσ).posSemidef

/-- **Asymptotic normality of three-parameter GEV local MLEs at `ξ₀ = 0`**, in `(ξ, μ, σ)` order:
`√n (ξ̂ₙ, μ̂ₙ - μ₀, σ̂ₙ - σ₀) ⇒ N(0, gevMLECovZero σ₀)`. -/
theorem tendstoInDistribution_gevLocalMLE_zero {μ₀ σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P)
    (hind : iIndepFun X P) {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : TendstoInMeasure P θh atTop (fun _ => ((0 : ℝ), μ₀, σ₀)))
    (hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).1| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0))
    (hloc : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω)})
      atTop (𝓝 0))
    {W : Ω' → EuclideanSpace ℝ (Fin 3)}
    (hW : HasLaw W (multivariateGaussian 0 (gevMLECovZero σ₀)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀])
      atTop W (fun _ => P) P' := by
  set sw : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p => (p.2.1, p.2.2, p.1)
  have hsw_cont : Continuous sw := by unfold sw; fun_prop
  set θh' : ℕ → Ω → ℝ × ℝ × ℝ := fun n ω => sw (θh n ω)
  have hθ'm : ∀ n, AEMeasurable (θh' n) P := fun n => hsw_cont.measurable.comp_aemeasurable (hθm n)
  have hcons' : TendstoInMeasure P θh' atTop (fun _ => (μ₀, σ₀, (0 : ℝ))) :=
    hcons.comp_continuousAt hsw_cont.continuousAt
  have hloc' : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.2.2 p.1 p.2.1 (fun i : Fin n => X i ω)) (θh' n ω)})
      atTop (𝓝 0) := by
    refine hloc.congr fun n => ?_
    congr 1; ext ω
    simp only [mem_ofPred_eq, not_iff_not]
    constructor
    · intro h
      have hsw_inv : Continuous (fun p : ℝ × ℝ × ℝ => (p.2.2, p.1, p.2.1)) := by fun_prop
      have h' : IsLocalMax (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω))
          ((θh' n ω).2.2, (θh' n ω).1, (θh' n ω).2.1) := by simpa [θh', sw] using h
      exact (hsw_inv.continuousAt.tendsto.eventually h').mono fun p hp => hp
    · intro h
      exact (hsw_cont.continuousAt.tendsto.eventually h).mono fun p hp => by simpa [sw] using hp
  set Pmat : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  have hPcov : Pmat * (gevFisherInfoZero σ₀)⁻¹ * Pmat.transpose = gevMLECovZero σ₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Pmat, gevMLECovZero, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_three, Matrix.submatrix_apply]
  -- Apply the `(μ, σ, ξ)` theorem and map by the permutation `Pmat`
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (gevFisherInfoZero σ₀)⁻¹)
      (multivariateGaussian 0 (gevFisherInfoZero σ₀)⁻¹) := HasLaw.id
  have hmain := tendstoInDistribution_gevLocalMLE_zero_muSigmaXi hσ₀ hX hind hθ'm hcons' hξmax hloc' hZ
  set f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun v => WithLp.toLp 2 (Pmat.mulVec v.ofLp)
  have hf_cont : Continuous f := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp (continuous_pi fun i => ?_)
    simp only [Matrix.mulVec, dotProduct]
    refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
    exact (continuous_apply j).comp (PiLp.continuous_ofLp 2 _)
  have hcomp := hmain.continuous_comp hf_cont
  have hW_eq : TendstoInDistribution (fun (n : ℕ) ω => f (√(n : ℝ) •
      !₂[(θh' n ω).1 - μ₀, (θh' n ω).2.1 - σ₀, (θh' n ω).2.2])) atTop W (fun _ => P) P' := by
    refine TendstoInDistribution.of_inner hW.aemeasurable hcomp.forall_aemeasurable fun v => ?_
    have hinner_cont : Continuous fun x : EuclideanSpace ℝ (Fin 3) => ⟪x, v⟫ :=
      continuous_inner.comp (continuous_id.prodMk continuous_const)
    have h1 := hcomp.continuous_comp hinner_cont
    have hW_v : HasLaw (fun ω => ⟪W ω, v⟫)
        (gaussianReal 0 (v ⬝ᵥ gevMLECovZero σ₀ *ᵥ v).toNNReal) P' :=
      hasLaw_inner_multivariateGaussian (posSemidef_gevMLECovZero hσ₀) hW v
    set u : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (Pmat.transpose.mulVec v.ofLp)
    have hfv : ∀ x : EuclideanSpace ℝ (Fin 3), ⟪f x, v⟫ = ⟪x, u⟫ := fun x => by
      simp [f, u, PiLp.inner_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pmat,
        Matrix.transpose_apply]
      ring
    have hu_var : u ⬝ᵥ (gevFisherInfoZero σ₀)⁻¹ *ᵥ u = v ⬝ᵥ gevMLECovZero σ₀ *ᵥ v := by
      rw [← hPcov]
      have h1 : u.ofLp = Pmat.transpose.mulVec v.ofLp := rfl
      change u.ofLp ⬝ᵥ (gevFisherInfoZero σ₀)⁻¹ *ᵥ u.ofLp =
        v.ofLp ⬝ᵥ (Pmat * (gevFisherInfoZero σ₀)⁻¹ * Pmat.transpose) *ᵥ v.ofLp
      rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v.ofLp Pmat,
        ← Matrix.mulVec_transpose]
    have hZ_v : HasLaw (fun x => ⟪f x, v⟫)
        (gaussianReal 0 (v ⬝ᵥ gevMLECovZero σ₀ *ᵥ v).toNNReal)
        (multivariateGaussian 0 (gevFisherInfoZero σ₀)⁻¹) := by
      have h := hasLaw_inner_multivariateGaussian (posDef_gevFisherInfoZero hσ₀).inv.posSemidef hZ u
      rw [hu_var] at h
      exact h.congr (ae_of_all _ fun x => hfv x)
    refine ⟨h1.forall_aemeasurable, hW_v.aemeasurable, ?_⟩
    have hmap : (⟨P'.map (fun ω => ⟪W ω, v⟫), inferInstance⟩ : ProbabilityMeasure ℝ) =
        ⟨(multivariateGaussian 0 (gevFisherInfoZero σ₀)⁻¹).map ((fun x => ⟪x, v⟫) ∘ (f ∘ id)),
          inferInstance⟩ :=
      ProbabilityMeasure.toMeasure_injective (hW_v.map_eq.trans hZ_v.map_eq.symm)
    rw [hmap]
    exact h1.tendsto
  refine hW_eq.congr (fun n => Eventually.of_forall fun ω => ?_) (ae_of_all _ fun _ => rfl)
  ext i
  fin_cases i <;> simp [f, Pmat, θh', sw, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end LocalMLENormality

/-! ### Unconditional existence of a data-driven 3-parameter GEV local MLE at `ξ₀ = 0` -/

section ExistenceZero

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

private lemma measurable_gevLocScaleDensity_joint :
    Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => gevLocScaleDensity p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  unfold gevLocScaleDensity gevDensity
  have hξ : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.1 := measurable_fst.comp measurable_fst
  have hμ : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.1 :=
    (measurable_fst.comp measurable_snd).comp measurable_fst
  have hσ : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.2 :=
    (measurable_snd.comp measurable_snd).comp measurable_fst
  have hx : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => p.2 := measurable_snd
  have hz : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => (p.2 - p.1.2.1) / p.1.2.2 :=
    (hx.sub hμ).div hσ
  have hu : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => 1 + p.1.1 * ((p.2 - p.1.2.1) / p.1.2.2) :=
    measurable_const.add (hξ.mul hz)
  refine hσ.inv.mul (Measurable.ite (measurableSet_eq_fun hξ measurable_const)
    ((hz.neg.exp).mul (hz.neg.exp.neg.exp))
    (Measurable.ite (measurableSet_lt measurable_const hu)
      ((hu.pow ((measurable_const.div hξ).sub_const 1)).mul
        ((hu.pow (measurable_const.div hξ)).neg.exp))
      measurable_const))

private lemma measurable_gevLogDensityE_joint :
    Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => gevLogDensityE p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  unfold gevLogDensityE
  exact ENNReal.measurable_log.comp (ENNReal.measurable_ofReal.comp measurable_gevLocScaleDensity_joint)

/-- Positive definiteness gives a strict lower bound `lam * (v₀² + v₁² + v₂²) ≤ vᵀ I₀ v`. -/
private lemma exists_pos_quad_le_gevFisherInfoZero {σ : ℝ} (hσ : 0 < σ) :
    ∃ lam > 0, ∀ v : Fin 3 → ℝ,
      lam * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) ≤ v ⬝ᵥ gevFisherInfoZero σ *ᵥ v := by
  set S : Set (EuclideanSpace ℝ (Fin 3)) := Metric.sphere 0 1
  have hSc : IsCompact S := isCompact_sphere 0 1
  have hSne : S.Nonempty := ⟨!₂[1, 0, 0], by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]⟩
  set q : EuclideanSpace ℝ (Fin 3) → ℝ := fun v => v.ofLp ⬝ᵥ gevFisherInfoZero σ *ᵥ v.ofLp
  have hqc : Continuous q := by
    simp only [q, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    have hcoord : ∀ i : Fin 3, Continuous fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp i :=
      fun i => (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
    fun_prop
  obtain ⟨v₀, hv₀S, hv₀min⟩ := hSc.exists_isMinOn hSne hqc.continuousOn
  have hv₀ne : v₀.ofLp ≠ 0 := by
    intro h0
    have hnorm : ‖v₀‖ = 1 := by simpa [S, Metric.mem_sphere] using hv₀S
    have hv₀0 : v₀ = 0 := by ext i; exact congrFun h0 i
    rw [hv₀0, norm_zero] at hnorm
    norm_num at hnorm
  have hlam : 0 < q v₀ :=
    (Matrix.posDef_iff_dotProduct_mulVec.1 (posDef_gevFisherInfoZero hσ)).2 hv₀ne
  refine ⟨q v₀, hlam, fun v => ?_⟩
  set w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 v
  have hsq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = ‖w‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [w, Fin.sum_univ_three, Real.norm_eq_abs]
  rw [hsq]
  rcases eq_or_ne ‖w‖ 0 with h0 | hne
  · have hw0 : w = 0 := norm_eq_zero.1 h0
    have hv0 : v = 0 := by ext i; exact congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x i) hw0
    simp [hv0, h0]
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hne)
    set u : EuclideanSpace ℝ (Fin 3) := ‖w‖⁻¹ • w
    have huS : u ∈ S := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hwpos.le),
        inv_mul_cancel₀ hwpos.ne']
    have hle : q v₀ ≤ q u := hv₀min huS
    have hscale : q u = (‖w‖ ^ 2)⁻¹ * (v ⬝ᵥ gevFisherInfoZero σ *ᵥ v) := by
      simp only [q, u, w, dotProduct, Matrix.mulVec, Fin.sum_univ_three, PiLp.smul_apply,
        smul_eq_mul]
      field_simp [hwpos.ne']
    rw [hscale] at hle
    have hmul := mul_le_mul_of_nonneg_right hle (sq_nonneg ‖w‖)
    have hrhs : (‖w‖ ^ 2)⁻¹ * (v ⬝ᵥ gevFisherInfoZero σ *ᵥ v) * ‖w‖ ^ 2 =
        v ⬝ᵥ gevFisherInfoZero σ *ᵥ v := by
      rw [mul_assoc, mul_comm _ (‖w‖ ^ 2), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hwpos.ne'),
        one_mul]
    rw [hrhs] at hmul
    exact hmul

set_option maxHeartbeats 400000 in
/-- **Existence and asymptotic normality of a data-driven measurable three-parameter GEV local MLE
at `ξ₀ = 0`** ([Smith 1985]; [Bücher–Segers 2017]). Given a compact `K₂ ⊂ ℝ × (0, ∞)` containing
`(μ₀, σ₀)` in its interior, maximizing the three-parameter GEV log-likelihood over a shrinking
cube of radius `≍ n^{-1/3}` around the two-parameter Gumbel MLE yields a measurable estimator
`gₙ : ℝⁿ → ℝ³` (independent of `(μ₀, σ₀)`) which with probability tending to `1` is a genuine
admissible local maximizer of `gevLogLikE` on `ℝ³` and satisfies
`√n (ξ̂ₙ, μ̂ₙ - μ₀, σ̂ₙ - σ₀) ⇒ N(0, gevMLECovZero σ₀)`. -/
theorem exists_gevLocalMLE_tendstoInDistribution_zero {μ₀ σ₀ : ℝ} {K₂ : Set (ℝ × ℝ)}
    (hK₂ : IsCompact K₂) (hKS₂ : ∀ p ∈ K₂, 0 < p.2) (hθ₀ : (μ₀, σ₀) ∈ interior K₂)
    (hσ₀ : 0 < σ₀) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {W : Ω' → EuclideanSpace ℝ (Fin 3)}
    (hW : HasLaw W (multivariateGaussian 0 (gevMLECovZero σ₀)) P') :
    ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
      Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
        (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω))
        (g n (fun i : Fin n => X i ω))}) atTop (𝓝 0) ∧
      TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) •
          !₂[(g n (fun i : Fin n => X i ω)).1, (g n (fun i : Fin n => X i ω)).2.1 - μ₀,
            (g n (fun i : Fin n => X i ω)).2.2 - σ₀])
        atTop W (fun _ => P) P' := by
  -- Step 1: measurable 2-parameter Gumbel MLE over `K₂`
  choose g₂ hg₂m hg₂ using exists_measurable_gumbelMLE hK₂ hKS₂ ⟨_, interior_subset hθ₀⟩
  obtain ⟨p_min, hp_min_mem, hp_min⟩ := hK₂.exists_isMinOn ⟨_, interior_subset hθ₀⟩ continuous_snd.continuousOn
  set c := p_min.2
  have hc : 0 < c := hKS₂ p_min hp_min_mem
  have hge_c : ∀ p ∈ K₂, c ≤ p.2 := fun p hp => hp_min hp
  -- Step 2: shrinking cube radius `r n = min (min (c / 2) (1 / 2)) ((n + 1)^{-1/3})`
  set r : ℕ → ℝ := fun n => min (min (c / 2) (1 / 2)) (((n : ℝ) + 1) ^ (-(1 / 3 : ℝ)))
  have hr_pos : ∀ n, 0 < r n := fun n =>
    lt_min (lt_min (by positivity) (by norm_num)) (rpow_pos_of_pos (by positivity) _)
  have hr_lim : Tendsto r atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    refine hpow.congr' ?_
    filter_upwards [hpow.eventually (gt_mem_nhds (lt_min (by positivity : 0 < c / 2) (by norm_num : (0 : ℝ) < 1 / 2)))]
      with n hn
    exact (min_eq_right hn.le).symm
  have hr_eq_ev : ∀ᶠ n : ℕ in atTop, r n = ((n : ℝ) + 1) ^ (-(1 / 3 : ℝ)) := by
    have hpow : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    filter_upwards [hpow.eventually (gt_mem_nhds (lt_min (by positivity : 0 < c / 2) (by norm_num : (0 : ℝ) < 1 / 2)))]
      with n hn
    exact min_eq_right hn.le
  have hsqr_atTop : Tendsto (fun n : ℕ => √(n : ℝ) * r n) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => √(n : ℝ) * ((n : ℝ) + 1) ^ (-(1 / 3 : ℝ))) atTop atTop := by
      have hrate : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ)) atTop atTop :=
        ((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num)).comp tendsto_natCast_atTop_atTop).const_mul_atTop
          (by norm_num)
      refine tendsto_atTop_mono' atTop ?_ hrate
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have h2n : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
      have hle : (2 * (n : ℝ)) ^ (-(1 / 3 : ℝ)) ≤ ((n : ℝ) + 1) ^ (-(1 / 3 : ℝ)) :=
        rpow_le_rpow_of_nonpos (by positivity) h2n (by norm_num)
      have h2le : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 3 : ℝ)) := by
        have h1 : (2 : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 3 : ℝ)) :=
          rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        simpa [rpow_neg_one] using h1
      have hpow_eq : √(n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) = (n : ℝ) ^ (1 / 6 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← rpow_add hn0]; congr 1; norm_num
      calc (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ)
          = (1 / 2 : ℝ) * (√(n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by rw [hpow_eq]
        _ ≤ (2 : ℝ) ^ (-(1 / 3 : ℝ)) * (√(n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by gcongr
        _ = √(n : ℝ) * (2 * (n : ℝ)) ^ (-(1 / 3 : ℝ)) := by
            rw [mul_rpow (by norm_num) hn0.le]; ring
        _ ≤ √(n : ℝ) * ((n : ℝ) + 1) ^ (-(1 / 3 : ℝ)) := by gcongr
    exact h1.congr' (hr_eq_ev.mono fun n hn => by dsimp only; rw [hn])
  -- Step 3: construct the measurable maximizer `δ n` over `cube n`
  set cube : ℕ → Set (ℝ × ℝ × ℝ) := fun n =>
    Icc (-r n) (r n) ×ˢ Icc (-r n) (r n) ×ˢ Icc (-r n) (r n)
  have hex : ∀ n : ℕ, ∃ δ : (Fin n → ℝ) → ℝ × ℝ × ℝ, Measurable δ ∧
      ∀ x, δ x ∈ cube n ∧ IsMaxOn (fun d : ℝ × ℝ × ℝ =>
        gevLogLikE d.2.2 ((g₂ n x).1 + d.1) ((g₂ n x).2 + d.2.1) x) (cube n) (δ x) := by
    intro n
    have hKc : IsCompact (cube n) := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hne : (cube n).Nonempty := ⟨(0, 0, 0),
      ⟨⟨by linarith [hr_pos n], (hr_pos n).le⟩, ⟨by linarith [hr_pos n], (hr_pos n).le⟩,
        by linarith [hr_pos n], (hr_pos n).le⟩⟩
    refine exists_measurable_isMaxOn₃ hKc
      (f := fun d x => gevLogLikE d.2.2 ((g₂ n x).1 + d.1) ((g₂ n x).2 + d.2.1) x)
      (fun x => ?_) (fun d => ?_) hne
    · have hσ_pos : ∀ d ∈ cube n, -1 < d.2.2 ∧ 0 < (g₂ n x).2 + d.2.1 := fun d hd => by
        have hg2c : c ≤ (g₂ n x).2 := hge_c _ (hg₂ n x).1
        have hrc : r n ≤ c / 2 := (min_le_left _ _).trans (min_le_left _ _)
        have hr2 : r n ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
        exact ⟨by linarith [hd.2.2.1], by linarith [hd.2.1.1]⟩
      refine (continuousOn_finsetSum_ereal Finset.univ (fun i _ => ?_) (fun i _ d hd => ?_)).1
      · have hmap : Continuous fun d : ℝ × ℝ × ℝ => (d.2.2, (g₂ n x).1 + d.1, (g₂ n x).2 + d.2.1) := by
          fun_prop
        exact (continuousOn_gevLogDensityE (x i)).comp hmap.continuousOn fun d hd => hσ_pos d hd
      · exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
          (gevLogDensityE_le (hσ_pos d hd).1 (hσ_pos d hd).2 (x i))
    · refine Finset.measurable_sum _ fun i _ => ?_
      have harg : Measurable fun x : Fin n → ℝ =>
          ((d.2.2, (g₂ n x).1 + d.1, (g₂ n x).2 + d.2.1), x i) := by
        have := hg₂m n
        have h1 : Measurable fun x : Fin n → ℝ => (g₂ n x).1 + d.1 :=
          (measurable_fst.comp this).add_const _
        have h2 : Measurable fun x : Fin n → ℝ => (g₂ n x).2 + d.2.1 :=
          (measurable_snd.comp this).add_const _
        exact (measurable_const.prodMk (h1.prodMk h2)).prodMk (measurable_pi_apply i)
      exact measurable_gevLogDensityE_joint.comp harg
  choose δ hδm hδ using hex
  set g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ := fun n x =>
    ((δ n x).2.2, (g₂ n x).1 + (δ n x).1, (g₂ n x).2 + (δ n x).2.1)
  have hgm : ∀ n, Measurable (g n) := fun n => by
    have h1 := hg₂m n; have h2 := hδm n
    exact ((measurable_snd.comp measurable_snd).comp h2).prodMk
      (((measurable_fst.comp h1).add (measurable_fst.comp h2)).prodMk
        ((measurable_snd.comp h1).add ((measurable_fst.comp measurable_snd).comp h2)))
  set θh : ℕ → Ω → ℝ × ℝ × ℝ := fun n ω => g n (fun i : Fin n => X i ω)
  have hθm : ∀ n, AEMeasurable (θh n) P := fun n =>
    (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable)
  -- Step 4: `√n (g₂ - (μ₀, σ₀))` is tight, so `|g₂ - (μ₀, σ₀)| / r n → 0` in probability
  have hZ2 : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (gumbelFisherInfoInv σ₀))
      (multivariateGaussian 0 (gumbelFisherInfoInv σ₀)) := HasLaw.id
  have hg2_clt := tendstoInDistribution_gumbelMLE hK₂ hKS₂ hθ₀ hσ₀ hX hind
    (θh := fun n ω => g₂ n (fun i : Fin n => X i ω))
    (fun n => (hg₂m n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable))
    (fun n ω => (hg₂ n _).1) (fun n ω => (hg₂ n _).2) hZ2
  have hg2_cons : TendstoInMeasure P
      (fun (n : ℕ) ω => (!₂[(g₂ n (fun i : Fin n => X i ω)).1 - μ₀,
        (g₂ n (fun i : Fin n => X i ω)).2 - σ₀] : EuclideanSpace ℝ (Fin 2)))
      atTop (fun _ => 0) :=
    TendstoInDistribution.tendstoInMeasure_of_smul (r := fun n : ℕ => √(n : ℝ)) hg2_clt
      tendsto_sqrt_natCast_atTop
  have hg2_div_r : Tendsto (fun n : ℕ => P {ω | r n / 4 ≤
      |(g₂ n (fun i : Fin n => X i ω)).1 - μ₀| + |(g₂ n (fun i : Fin n => X i ω)).2 - σ₀|})
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    obtain ⟨M, hM⟩ := hg2_clt.exists_measure_le_norm_le hη
    filter_upwards [hM, eventually_ge_atTop 1, hsqr_atTop.eventually_gt_atTop (8 * max M 1)] with
      n hMn hn1 hsr
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hsq0 : 0 < √(n : ℝ) := sqrt_pos.2 hn0
    refine (measure_mono fun ω hω => ?_).trans hMn
    simp only [mem_ofPred_eq] at hω ⊢
    set v : EuclideanSpace ℝ (Fin 2) := !₂[(g₂ n (fun i : Fin n => X i ω)).1 - μ₀,
      (g₂ n (fun i : Fin n => X i ω)).2 - σ₀]
    have hnorm_v : |(g₂ n (fun i : Fin n => X i ω)).1 - μ₀| +
        |(g₂ n (fun i : Fin n => X i ω)).2 - σ₀| ≤ 2 * ‖v‖ := by
      have h0 : |(g₂ n (fun i : Fin n => X i ω)).1 - μ₀| ≤ ‖v‖ := by
        simpa [v, Real.norm_eq_abs] using PiLp.norm_apply_le v 0
      have h1 : |(g₂ n (fun i : Fin n => X i ω)).2 - σ₀| ≤ ‖v‖ := by
        simpa [v, Real.norm_eq_abs] using PiLp.norm_apply_le v 1
      linarith
    rw [norm_smul, Real.norm_of_nonneg hsq0.le]
    have hMle : M ≤ max M 1 := le_max_left _ _
    nlinarith
  -- Step 5: prove `hcons`, `hξmax`, and `hloc`
  have hcons : TendstoInMeasure P θh atTop (fun _ => ((0 : ℝ), μ₀, σ₀)) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have h2 : Tendsto (fun n : ℕ => P {ω | ε / 2 ≤
        ‖(!₂[(g₂ n (fun i : Fin n => X i ω)).1 - μ₀,
          (g₂ n (fun i : Fin n => X i ω)).2 - σ₀] : EuclideanSpace ℝ (Fin 2)) - 0‖}) atTop (𝓝 0) :=
      (tendstoInMeasure_iff_norm.1 hg2_cons) (ε / 2) (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hr_lim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))] with n hrn
    refine measure_mono fun ω hω => ?_
    by_contra hnot
    simp only [mem_ofPred_eq, sub_zero, not_le] at hω hnot
    set v : EuclideanSpace ℝ (Fin 2) := !₂[(g₂ n (fun i : Fin n => X i ω)).1 - μ₀,
      (g₂ n (fun i : Fin n => X i ω)).2 - σ₀]
    have h0le : |(g₂ n (fun i : Fin n => X i ω)).1 - μ₀| ≤ ‖v‖ := by
      simpa [v, Real.norm_eq_abs] using PiLp.norm_apply_le v 0
    have h1le : |(g₂ n (fun i : Fin n => X i ω)).2 - σ₀| ≤ ‖v‖ := by
      simpa [v, Real.norm_eq_abs] using PiLp.norm_apply_le v 1
    have h0 : |(g₂ n (fun i : Fin n => X i ω)).1 - μ₀| < ε / 2 := h0le.trans_lt hnot
    have h1 : |(g₂ n (fun i : Fin n => X i ω)).2 - σ₀| < ε / 2 := h1le.trans_lt hnot
    have hd := (hδ n (fun i : Fin n => X i ω)).1
    have hd1 : |(δ n (fun i : Fin n => X i ω)).1| ≤ r n := abs_le.2 hd.1
    have hd2 : |(δ n (fun i : Fin n => X i ω)).2.1| ≤ r n := abs_le.2 hd.2.1
    have hd3 : |(δ n (fun i : Fin n => X i ω)).2.2| ≤ r n := abs_le.2 hd.2.2
    have hdist : dist (θh n ω) ((0 : ℝ), μ₀, σ₀) < ε := by
      simp only [θh, g, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
      refine ⟨lt_of_le_of_lt hd3 (by linarith), ?_, ?_⟩
      · have := abs_add_le ((g₂ n (fun i : Fin n => X i ω)).1 - μ₀) (δ n (fun i : Fin n => X i ω)).1
        rw [show (g₂ n (fun i : Fin n => X i ω)).1 + (δ n (fun i : Fin n => X i ω)).1 - μ₀ =
          ((g₂ n (fun i : Fin n => X i ω)).1 - μ₀) + (δ n (fun i : Fin n => X i ω)).1 by ring]
        linarith
      · have := abs_add_le ((g₂ n (fun i : Fin n => X i ω)).2 - σ₀) (δ n (fun i : Fin n => X i ω)).2.1
        rw [show (g₂ n (fun i : Fin n => X i ω)).2 + (δ n (fun i : Fin n => X i ω)).2.1 - σ₀ =
          ((g₂ n (fun i : Fin n => X i ω)).2 - σ₀) + (δ n (fun i : Fin n => X i ω)).2.1 by ring]
        linarith
    linarith
  have hrm_r : TendstoInMeasure P
      (fun (n : ℕ) ω => r n * runMax (fun i => |(X i ω - μ₀) / σ₀|) n) atTop (fun _ => 0) := by
    have hrm := tendstoInMeasure_runMax_abs_gumbel_div_rpow hσ₀ (show (0 : ℝ) < 1 / 3 by norm_num) hX
    rw [tendstoInMeasure_iff_norm] at hrm ⊢
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hrm ε hε)
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hr_le : r n ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) :=
      (min_le_right _ _).trans (rpow_le_rpow_of_nonpos hn0 (by linarith) (by norm_num))
    refine measure_mono fun ω hω => ?_
    have hnn1 : 0 ≤ r n * runMax (fun i => |(X i ω - μ₀) / σ₀|) n :=
      mul_nonneg (hr_pos n).le (runMax_nonneg _ _)
    have hnn2 : 0 ≤ runMax (fun i => |(X i ω - μ₀) / σ₀|) n / (n : ℝ) ^ (1 / 3 : ℝ) :=
      div_nonneg (runMax_nonneg _ _) (rpow_nonneg hn0.le _)
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn1,
      abs_of_nonneg hnn2] at hω ⊢
    have heq : (n : ℝ) ^ (-(1 / 3 : ℝ)) * runMax (fun i => |(X i ω - μ₀) / σ₀|) n =
        runMax (fun i => |(X i ω - μ₀) / σ₀|) n / (n : ℝ) ^ (1 / 3 : ℝ) := by
      rw [rpow_neg hn0.le, mul_comm, ← div_eq_mul_inv]
    calc ε ≤ r n * runMax (fun i => |(X i ω - μ₀) / σ₀|) n := hω
      _ ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) * runMax (fun i => |(X i ω - μ₀) / σ₀|) n :=
          mul_le_mul_of_nonneg_right hr_le (runMax_nonneg _ _)
      _ = runMax (fun i => |(X i ω - μ₀) / σ₀|) n / (n : ℝ) ^ (1 / 3 : ℝ) := heq
  have hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).1| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm] at hrm_r ⊢
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hrm_r ε hε)
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => measure_mono fun ω hω => ?_)
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg _) (runMax_nonneg _ _)),
      abs_of_nonneg (mul_nonneg (hr_pos n).le (runMax_nonneg _ _))] at hω ⊢
    have hd3 : |(θh n ω).1| ≤ r n := abs_le.2 (hδ n (fun i : Fin n => X i ω)).1.2.2
    exact hω.trans (mul_le_mul_of_nonneg_right hd3 (runMax_nonneg _ _))
  -- Step 6: prove `hloc`: `δ n X` lies in the open interior of `cube n` with probability `→ 1`
  have hloc : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω)})
      atTop (𝓝 0) := by
    obtain ⟨lam, hlam, hlam_le⟩ := exists_pos_quad_le_gevFisherInfoZero hσ₀
    set C₀ : ℝ := 7000 * (1 + σ₀⁻¹ ^ 2)
    have hC₀ : 0 < C₀ := by positivity
    -- Cutoff `M : ℕ` so `2 * C₀ * E[gevZeroEnvTail M] < lam / 72`
    obtain ⟨M, hM_int⟩ := ((tendsto_integral_gevZeroEnvTail (μ₀ := μ₀) hσ₀).eventually
      (gt_mem_nhds (show (0 : ℝ) < lam / (144 * C₀) by positivity))).exists
    -- Uniform continuity radius `δ₀ > 0` for all 9 Hessian entries on `|z₀| ≤ M`
    have hex_δ : ∀ i j : Fin 3, ∃ δ > 0, δ ≤ min (σ₀ / 8) (1 / (8 * ((M : ℝ) + 1))) ∧
        ∀ θ : ℝ × ℝ × ℝ, |θ.1 - μ₀| ≤ δ → |θ.2.1 - σ₀| ≤ δ → |θ.2.2| ≤ δ →
          ∀ x : ℝ, |(x - μ₀) / σ₀| ≤ (M : ℝ) →
            |gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) x -
              gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) x| ≤ lam / 72 :=
      fun i j => exists_delta_gevZeroH_sub_le hσ₀ (M : ℝ) (Nat.cast_nonneg M) (by positivity) i j
    choose δM hδM_pos hδM_le hδM_unif using hex_δ
    set δ₀ : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).inf' ⟨(0, 0), Finset.mem_univ _⟩
      (fun p => δM p.1 p.2)
    have hδ₀_pos : 0 < δ₀ := (Finset.lt_inf'_iff _).2 fun p _ => hδM_pos p.1 p.2
    have hδ₀_le : ∀ i j : Fin 3, δ₀ ≤ δM i j := fun i j =>
      Finset.inf'_le (f := fun p : Fin 3 × Fin 3 => δM p.1 p.2) (Finset.mem_univ (i, j))
    have hδ₀_σ : δ₀ ≤ σ₀ / 8 := (hδ₀_le 0 0).trans ((hδM_le 0 0).trans (min_le_left _ _))
    have hδ₀_8 : δ₀ ≤ 1 / 8 := (hδ₀_le 0 0).trans ((hδM_le 0 0).trans ((min_le_right _ _).trans
      (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [Nat.cast_nonneg (α := ℝ) M])))
    -- SLLN events for `gevZeroH (μ₀, σ₀, 0)` (all 9 entries) and `gevZeroEnvTail M`
    have hidX : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
      ⟨(hX k).aemeasurable, (hX 0).aemeasurable, by rw [(hX k).map_eq, (hX 0).map_eq]⟩
    have hslln : ∀ (g : ℝ → ℝ), Measurable g →
        Integrable g (gevLocScaleCDF 0 μ₀ hσ₀).measure →
        TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (X k ω))
          atTop (fun _ => ∫ x, g x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure) := fun g hgm hgi => by
      refine tendstoInMeasure_of_tendsto_ae (fun n =>
        ((Finset.aemeasurable_fun_sum _ fun k _ => hgm.comp_aemeasurable (hX k).aemeasurable).const_mul
          (n : ℝ)⁻¹).aestronglyMeasurable) ?_
      have hae := strong_law_ae (fun k ω => g (X k ω)) ((hX 0).integrable_comp hgi)
        (fun a b hab => (hind.indepFun hab).comp hgm hgm) (fun k => (hidX k).comp hgm)
      have hint_eq : ∫ ω, g (X 0 ω) ∂P = ∫ x, g x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure :=
        (hX 0).integral_comp hgm.aestronglyMeasurable
      filter_upwards [hae] with ω hω
      rw [hint_eq] at hω
      simpa [smul_eq_mul] using hω
    -- Score tightness event `‖Sₙ‖ ≥ (lam / 64) * √n * r n`
    set S_proc : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω =>
      (√(n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω)
    have hZ3 : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (gevFisherInfoZero σ₀))
        (multivariateGaussian 0 (gevFisherInfoZero σ₀)) := HasLaw.id
    have hS_clt : TendstoInDistribution S_proc atTop id (fun _ => P)
        (multivariateGaussian 0 (gevFisherInfoZero σ₀)) :=
      tendstoInDistribution_gumbelScoreVec3 hσ₀ hX hind hZ3
    have hS_small : Tendsto (fun n : ℕ => P {ω | (lam / 64) * (√(n : ℝ) * r n) ≤ ‖S_proc n ω‖})
        atTop (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro η hη
      obtain ⟨Ms, hMs⟩ := hS_clt.exists_measure_le_norm_le hη
      filter_upwards [hMs, hsqr_atTop.eventually_gt_atTop (64 * max Ms 1 / lam)] with n hMsn hsr
      refine (measure_mono fun ω hω => ?_).trans hMsn
      simp only [mem_ofPred_eq] at hω ⊢
      have h1 : max Ms 1 < (lam / 64) * (√(n : ℝ) * r n) := by
        rw [div_lt_iff₀ hlam] at hsr; linarith
      linarith [le_max_left Ms 1]
    set μT := ∫ x, gevZeroEnvTail μ₀ σ₀ (M : ℝ) x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure
    have hηT : 0 < lam / (144 * C₀) - μT := sub_pos.2 hM_int
    have hT_bad : Tendsto (fun n : ℕ => P {ω | lam / (144 * C₀) - μT ≤
        |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) - μT|})
        atTop (𝓝 0) := by
      have h := (tendstoInMeasure_iff_norm.1 (hslln _ (measurable_gevZeroEnvTail μ₀ σ₀ M)
        (integrable_gevZeroEnvTail hσ₀ M))) (lam / (144 * C₀) - μT) hηT
      simpa [Real.norm_eq_abs] using h
    have hH_bad : Tendsto (fun n : ℕ => ∑ i : Fin 3, ∑ j : Fin 3,
        P {ω | lam / 72 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
          (-gevFisherInfoZero σ₀ i j)|}) atTop (𝓝 0) := by
      have : (0 : ENNReal) = ∑ _i : Fin 3, ∑ _j : Fin 3, (0 : ENNReal) := by simp
      rw [this]
      refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
      have hs := hslln _ (measurable_gevZeroH_zero μ₀ σ₀ (gevZeroBasis i) (gevZeroBasis j))
        (integrable_gevZeroH_zero hσ₀ _ _)
      rw [integral_gevZeroH_eq_neg_gevFisherInfoZero hσ₀ i j] at hs
      simpa [Real.norm_eq_abs] using (tendstoInMeasure_iff_norm.1 hs) (lam / 72) (by positivity)
    have hrm_bad : Tendsto (fun n : ℕ => P {ω | (1 / 16 : ℝ) ≤
        r n * runMax (fun i => |(X i ω - μ₀) / σ₀|) n}) atTop (𝓝 0) := by
      have h := (tendstoInMeasure_iff_norm.1 hrm_r) (1 / 16) (by norm_num)
      refine h.congr fun n => ?_; congr 1; ext ω
      have hnn : 0 ≤ r n * runMax (fun i => |(X i ω - μ₀) / σ₀|) n :=
        mul_nonneg (hr_pos n).le (runMax_nonneg _ _)
      simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn]
    have htot_lim : Tendsto (fun n : ℕ =>
        P {ω | r n / 4 ≤ |(g₂ n (fun i : Fin n => X i ω)).1 - μ₀| +
            |(g₂ n (fun i : Fin n => X i ω)).2 - σ₀|} +
        P {ω | (1 / 16 : ℝ) ≤ r n * runMax (fun i => |(X i ω - μ₀) / σ₀|) n} +
        P {ω | (lam / 64) * (√(n : ℝ) * r n) ≤ ‖S_proc n ω‖} +
        P {ω | lam / (144 * C₀) - μT ≤
            |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) - μT|} +
        ∑ i : Fin 3, ∑ j : Fin 3,
          P {ω | lam / 72 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
            (-gevFisherInfoZero σ₀ i j)|}) atTop (𝓝 0) := by
      simpa using (((hg2_div_r.add hrm_bad).add hS_small).add hT_bad).add hH_bad
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htot_lim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1,
      hr_lim.eventually (gt_mem_nhds (show (0 : ℝ) < δ₀ / 2 by positivity))] with n hn1 hrδ
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hsub : {ω | ¬ IsLocalMax
        (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω)} ⊆
        (({ω | r n / 4 ≤ |(g₂ n (fun i : Fin n => X i ω)).1 - μ₀| +
            |(g₂ n (fun i : Fin n => X i ω)).2 - σ₀|} ∪
          {ω | (1 / 16 : ℝ) ≤ r n * runMax (fun i => |(X i ω - μ₀) / σ₀|) n}) ∪
         ({ω | (lam / 64) * (√(n : ℝ) * r n) ≤ ‖S_proc n ω‖} ∪
          {ω | lam / (144 * C₀) - μT ≤
            |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) - μT|})) ∪
        ⋃ i : Fin 3, ⋃ j : Fin 3,
          {ω | lam / 72 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
            (-gevFisherInfoZero σ₀ i j)|} := by
      intro ω hω
      by_contra hnot
      simp only [mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists, not_le] at hnot
      obtain ⟨⟨⟨hg2lt, hrmlt⟩, ⟨hSlt, hTlt⟩⟩, hHlt⟩ := hnot
      set x := fun i : Fin n => X i ω
      set p₂ := g₂ n x
      have hp2lt : |p₂.1 - μ₀| + |p₂.2 - σ₀| < r n / 4 := hg2lt
      have hr8 : r n ≤ 1 / 8 := by linarith [hrδ, hδ₀_8]
      -- Every `d ∈ cube n` gives a point `θ_d` in `(μ₀, σ₀, 0) ± δ₀` with `|ξ z_k| ≤ 1/2` along segment
      have hgood_d : ∀ d ∈ cube n,
          let θ : ℝ × ℝ × ℝ := (p₂.1 + d.1, p₂.2 + d.2.1, d.2.2)
          |θ.1 - μ₀| ≤ δ₀ ∧ |θ.2.1 - σ₀| ≤ δ₀ ∧ |θ.2.2| ≤ δ₀ ∧ θ ∈ gevZeroNbhd μ₀ σ₀ ∧
          ∀ k < n, ∀ s ∈ Icc (0 : ℝ) 1,
            |(gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s).2.2 *
              gevZeroZ (gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s) (X k ω)| ≤ 1 / 2 := by
        intro d hd
        set θ : ℝ × ℝ × ℝ := (p₂.1 + d.1, p₂.2 + d.2.1, d.2.2)
        have h1 : |θ.1 - μ₀| ≤ 2 * r n := by
          have htri := abs_add_le (p₂.1 - μ₀) d.1
          have heq : θ.1 - μ₀ = (p₂.1 - μ₀) + d.1 := by simp only [θ]; ring
          rw [heq]
          linarith only [htri, abs_le.2 hd.1, abs_nonneg (p₂.2 - σ₀), hp2lt, hr_pos n]
        have h2 : |θ.2.1 - σ₀| ≤ 2 * r n := by
          have htri := abs_add_le (p₂.2 - σ₀) d.2.1
          have heq : θ.2.1 - σ₀ = (p₂.2 - σ₀) + d.2.1 := by simp only [θ]; ring
          rw [heq]
          linarith only [htri, abs_le.2 hd.2.1, abs_nonneg (p₂.1 - μ₀), hp2lt, hr_pos n]
        have h3 : |θ.2.2| ≤ r n := abs_le.2 hd.2.2
        have h1δ : |θ.1 - μ₀| ≤ δ₀ := h1.trans (by linarith)
        have h2δ : |θ.2.1 - σ₀| ≤ δ₀ := h2.trans (by linarith)
        have h3δ : |θ.2.2| ≤ δ₀ := h3.trans (by linarith)
        have hnbhd : θ ∈ gevZeroNbhd μ₀ σ₀ :=
          ⟨⟨by linarith [(abs_le.1 h1δ).1], by linarith [(abs_le.1 h1δ).2]⟩,
           ⟨by linarith [(abs_le.1 h2δ).1], by linarith [(abs_le.1 h2δ).2]⟩,
           by linarith [(abs_le.1 h3δ).1], by linarith [(abs_le.1 h3δ).2]⟩
        refine ⟨h1δ, h2δ, h3δ, hnbhd, fun k hk s hs => ?_⟩
        have hm := gevStep_mem_gevZeroNbhd hnbhd hs.1 hs.2
        have hz := abs_gevZeroZ_le hσ₀ hm (x := X k ω)
        have hξs : |(gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s).2.2| ≤ r n := by
          simp only [gevStep, zero_add, abs_mul, abs_of_nonneg hs.1]
          nlinarith [hs.2, h3, abs_nonneg θ.2.2]
        have hrmk : |(X k ω - μ₀) / σ₀| ≤ runMax (fun m => |(X m ω - μ₀) / σ₀|) n :=
          le_runMax (fun m => |(X m ω - μ₀) / σ₀|) hk
        rw [abs_mul]
        calc _ ≤ r n * (2 * (1 + |(X k ω - μ₀) / σ₀|)) :=
              mul_le_mul hξs hz (abs_nonneg _) (hr_pos n).le
          _ ≤ r n * (2 * (1 + runMax (fun m => |(X m ω - μ₀) / σ₀|) n)) := by gcongr
          _ = 2 * r n + 2 * (r n * runMax (fun m => |(X m ω - μ₀) / σ₀|) n) := by ring
          _ ≤ 2 * (1 / 8) + 2 * (1 / 16) := by linarith [hr8, hrmlt]
          _ ≤ 1 / 2 := by norm_num
      -- Uniform negative-definiteness of the average Hessian at any point in `(μ₀, σ₀, 0) ± δ₀`
      have hH_neg : ∀ (θ : ℝ × ℝ × ℝ) (v : ℝ × ℝ × ℝ),
          |θ.1 - μ₀| ≤ δ₀ → |θ.2.1 - σ₀| ≤ δ₀ → |θ.2.2| ≤ δ₀ → θ ∈ gevZeroNbhd μ₀ σ₀ →
          (∀ k < n, |θ.2.2 * gevZeroZ θ (X k ω)| ≤ 1 / 2) →
          (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH θ v v (X k ω) ≤
            -(lam / 2) * (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
        intro θ v h1 h2 h3 hnbhd ht_all
        have hentry : ∀ i j : Fin 3,
            |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
              (-gevFisherInfoZero σ₀ i j)| ≤ lam / 24 := by
          intro i j
          have hpt : ∀ k ∈ Finset.range n,
              |gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
                gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)| ≤
              lam / 72 + 2 * C₀ * gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) := by
            intro k hk
            by_cases hM : |(X k ω - μ₀) / σ₀| ≤ (M : ℝ)
            · have hu := hδM_unif i j θ (h1.trans (hδ₀_le i j)) (h2.trans (hδ₀_le i j))
                (h3.trans (hδ₀_le i j)) (X k ω) hM
              linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * C₀)
                (gevZeroEnvTail_nonneg μ₀ σ₀ M (X k ω))]
            · push Not at hM
              rw [show gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) = gevZeroEnv μ₀ σ₀ (X k ω) from
                Set.indicator_of_mem (show X k ω ∈ {y | (M : ℝ) < |(y - μ₀) / σ₀|} from hM) _]
              have hb1 := abs_gevZeroH_basis_le hσ₀ hnbhd (ht_all k (Finset.mem_range.1 hk)) i j
              have h0_nbhd : (μ₀, σ₀, (0 : ℝ)) ∈ gevZeroNbhd μ₀ σ₀ :=
                ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by norm_num, by norm_num⟩
              have hb0 := abs_gevZeroH_basis_le hσ₀ h0_nbhd (by simp) i j (x := X k ω)
              linarith [abs_sub (gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) (X k ω))
                (gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))]
          have hdiff : |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
              (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
                gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)| ≤
              lam / 72 + 2 * C₀ * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) := by
            rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hn0)]
            calc _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
                    (lam / 72 + 2 * C₀ * gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) :=
                  mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpt))
                    (inv_nonneg.2 hn0.le)
              _ = _ := by
                  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                    ← Finset.mul_sum]; field_simp [hn0.ne']
          have hTbd : 2 * C₀ * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) <
              lam / 72 := by
            have h1 := (abs_lt.1 hTlt).2
            have h2 : (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) <
                lam / (144 * C₀) := by linarith
            have := mul_lt_mul_of_pos_left h2 (show (0 : ℝ) < 2 * C₀ by positivity)
            have heq : 2 * C₀ * (lam / (144 * C₀)) = lam / 72 := by field_simp [hC₀.ne']; ring
            linarith
          have htri := abs_sub_le
            ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) (X k ω))
            ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
              gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
            (-gevFisherInfoZero σ₀ i j)
          linarith [hHlt i j]
        set vv : Fin 3 → ℝ := ![v.1, v.2.1, v.2.2]
        have hexp : (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH θ v v (X k ω) =
            ∑ i : Fin 3, ∑ j : Fin 3, vv i * vv j *
              ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) (X k ω)) := by
          have hrew : ∀ k, gevZeroH θ v v (X k ω) =
              ∑ i : Fin 3, ∑ j : Fin 3, vv i * vv j * gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) (X k ω) :=
            fun k => gevZeroH_eq_sum θ v v (X k ω)
          simp_rw [hrew]
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_comm (s := Finset.range n)]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum]; ring
        have hI0_exp : -(vv ⬝ᵥ gevFisherInfoZero σ₀ *ᵥ vv) =
            ∑ i : Fin 3, ∑ j : Fin 3, vv i * vv j * (-gevFisherInfoZero σ₀ i j) := by
          simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring
        have herr : |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH θ v v (X k ω) -
            (-(vv ⬝ᵥ gevFisherInfoZero σ₀ *ᵥ vv))| ≤ (lam / 2) * (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
          rw [hexp, hI0_exp, ← Finset.sum_sub_distrib]
          have h1 : |∑ i : Fin 3, (∑ j : Fin 3, vv i * vv j *
                ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) (X k ω)) -
              ∑ j : Fin 3, vv i * vv j * (-gevFisherInfoZero σ₀ i j))| ≤
              ∑ i : Fin 3, ∑ j : Fin 3, |vv i| * |vv j| * (lam / 24) := by
            calc _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, vv i * vv j *
                  (((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH θ (gevZeroBasis i) (gevZeroBasis j) (X k ω)) -
                    (-gevFisherInfoZero σ₀ i j))| := by
                  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
                  rw [← Finset.sum_sub_distrib]
                  refine le_of_eq (congrArg abs (Finset.sum_congr rfl fun j _ => by ring))
              _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |vv i| * |vv j| * (lam / 24) :=
                  Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
                    (Finset.sum_le_sum fun j _ => by
                      rw [abs_mul, abs_mul]
                      exact mul_le_mul_of_nonneg_left (hentry i j) (by positivity))
          have hsum_vv : ∑ i : Fin 3, ∑ j : Fin 3, |vv i| * |vv j| ≤ 3 * (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
            simp only [Fin.sum_univ_three, vv, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
            nlinarith only [sq_nonneg (|v.1| - |v.2.1|), sq_nonneg (|v.1| - |v.2.2|),
              sq_nonneg (|v.2.1| - |v.2.2|), sq_abs v.1, sq_abs v.2.1, sq_abs v.2.2]
          calc _ ≤ (∑ i : Fin 3, ∑ j : Fin 3, |vv i| * |vv j|) * (lam / 24) := by
                simpa [Finset.sum_mul] using h1
            _ ≤ (3 * (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)) * (lam / 24) :=
                mul_le_mul_of_nonneg_right hsum_vv (by positivity)
            _ ≤ (lam / 2) * (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
                nlinarith only [hlam, sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
        have hq := hlam_le vv
        simp only [vv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons] at hq
        linarith only [hq, (abs_le.1 herr).2]
      -- Show `δ n x` lies in the strict open interior of `cube n`!
      set d_opt := δ n x
      have hd_opt_mem : d_opt ∈ cube n := (hδ n x).1
      have hd_int : d_opt ∈ Ioo (-r n) (r n) ×ˢ Ioo (-r n) (r n) ×ˢ Ioo (-r n) (r n) := by
        -- Suppose for contradiction that one coordinate hits `±r n`
        by_contra hbdry
        have hmax_eq : |d_opt.1| = r n ∨ |d_opt.2.1| = r n ∨ |d_opt.2.2| = r n := by
          have ha : |d_opt.1| ≤ r n := abs_le.2 hd_opt_mem.1
          have hb : |d_opt.2.1| ≤ r n := abs_le.2 hd_opt_mem.2.1
          have hc' : |d_opt.2.2| ≤ r n := abs_le.2 hd_opt_mem.2.2
          by_contra hlt3
          push Not at hlt3
          apply hbdry
          exact ⟨abs_lt.1 (lt_of_le_of_ne ha hlt3.1), abs_lt.1 (lt_of_le_of_ne hb hlt3.2.1),
            abs_lt.1 (lt_of_le_of_ne hc' hlt3.2.2)⟩
        set θ_opt : ℝ × ℝ × ℝ := (p₂.1 + d_opt.1, p₂.2 + d_opt.2.1, d_opt.2.2)
        set Δ : ℝ × ℝ × ℝ := (θ_opt.1 - μ₀, θ_opt.2.1 - σ₀, θ_opt.2.2)
        have hΔ_lb : (9 / 16 : ℝ) * (r n) ^ 2 ≤ Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2 := by
          rcases hmax_eq with h | h | h
          · have h1 : 3 / 4 * r n ≤ |Δ.1| := by
              have htri := abs_sub_abs_le_abs_sub d_opt.1 (μ₀ - p₂.1)
              have heq : d_opt.1 - (μ₀ - p₂.1) = Δ.1 := by simp only [Δ, θ_opt]; ring
              rw [heq, abs_sub_comm μ₀ p₂.1] at htri
              linarith only [htri, h, hp2lt, abs_nonneg (p₂.2 - σ₀)]
            have hsq := pow_le_pow_left₀ (by linarith only [hr_pos n]) h1 2
            rw [sq_abs] at hsq
            nlinarith only [hsq, sq_nonneg Δ.2.1, sq_nonneg Δ.2.2]
          · have h1 : 3 / 4 * r n ≤ |Δ.2.1| := by
              have htri := abs_sub_abs_le_abs_sub d_opt.2.1 (σ₀ - p₂.2)
              have heq : d_opt.2.1 - (σ₀ - p₂.2) = Δ.2.1 := by simp only [Δ, θ_opt]; ring
              rw [heq, abs_sub_comm σ₀ p₂.2] at htri
              linarith only [htri, h, hp2lt, abs_nonneg (p₂.1 - μ₀)]
            have hsq := pow_le_pow_left₀ (by linarith only [hr_pos n]) h1 2
            rw [sq_abs] at hsq
            nlinarith only [hsq, sq_nonneg Δ.1, sq_nonneg Δ.2.2]
          · have hsq : (r n) ^ 2 = Δ.2.2 ^ 2 := by rw [← sq_abs Δ.2.2]; simp only [Δ, θ_opt, h]
            nlinarith only [hsq, sq_nonneg Δ.1, sq_nonneg Δ.2.1, sq_nonneg (r n)]
        have hΔ_ub : √(Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2) ≤ 4 * r n := by
          have h1 : |Δ.1| ≤ 2 * r n := by
            have htri := abs_add_le (p₂.1 - μ₀) d_opt.1
            have heq : Δ.1 = (p₂.1 - μ₀) + d_opt.1 := by simp only [Δ, θ_opt]; ring
            rw [heq]; linarith only [htri, abs_le.2 hd_opt_mem.1, abs_nonneg (p₂.2 - σ₀), hp2lt, hr_pos n]
          have h2 : |Δ.2.1| ≤ 2 * r n := by
            have htri := abs_add_le (p₂.2 - σ₀) d_opt.2.1
            have heq : Δ.2.1 = (p₂.2 - σ₀) + d_opt.2.1 := by simp only [Δ, θ_opt]; ring
            rw [heq]; linarith only [htri, abs_le.2 hd_opt_mem.2.1, abs_nonneg (p₂.1 - μ₀), hp2lt, hr_pos n]
          have h3 : |Δ.2.2| ≤ r n := abs_le.2 hd_opt_mem.2.2
          have hsq1 : Δ.1 ^ 2 ≤ 4 * (r n) ^ 2 := by
            have := pow_le_pow_left₀ (abs_nonneg _) h1 2; rw [sq_abs] at this; linarith only [this]
          have hsq2 : Δ.2.1 ^ 2 ≤ 4 * (r n) ^ 2 := by
            have := pow_le_pow_left₀ (abs_nonneg _) h2 2; rw [sq_abs] at this; linarith only [this]
          have hsq3 : Δ.2.2 ^ 2 ≤ (r n) ^ 2 := by
            have := pow_le_pow_left₀ (abs_nonneg _) h3 2; rw [sq_abs] at this; linarith only [this]
          calc √(Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2) ≤ √((4 * r n) ^ 2) :=
                Real.sqrt_le_sqrt (by nlinarith only [hsq1, hsq2, hsq3, sq_nonneg (r n)])
            _ = 4 * r n := Real.sqrt_sq (by linarith only [hr_pos n])
        -- Taylor expansion of `∑_{k<n} (gevZeroLog θ_opt - gevZeroLog θ₀)`
        obtain ⟨hθ1δ, hθ2δ, hθ3δ, hθnbhd, hθseg⟩ := hgood_d d_opt hd_opt_mem
        have hint_k : ∀ k ∈ Finset.range n,
            IntervalIntegrable (fun s => (1 - s) * gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω))
              volume 0 1 := fun k hk => by
          have hcont : ContinuousOn (fun s => (1 - s) * gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω))
              (uIcc 0 1) := by
            have hH : ContinuousOn (fun s => gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω)) (uIcc 0 1) := by
              have hrew : (fun s => gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω)) = fun s =>
                  ∑ i : Fin 3, ∑ j : Fin 3, (![Δ.1, Δ.2.1, Δ.2.2] i) * (![Δ.1, Δ.2.1, Δ.2.2] j) *
                    gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) (gevZeroBasis i) (gevZeroBasis j) (X k ω) :=
                funext fun s => gevZeroH_eq_sum _ _ _ _
              rw [hrew]
              refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
                continuousOn_const.mul fun s hs => ?_
              rw [uIcc_of_le zero_le_one] at hs
              have hm := gevStep_mem_gevZeroNbhd hθnbhd hs.1 hs.2
              have hσs : 0 < (gevStep (μ₀, σ₀, 0) Δ s).2.1 := by linarith only [(mem_gevZeroNbhd_bounds hm).2.1, hσ₀]
              have hus : 0 < 1 + (gevStep (μ₀, σ₀, 0) Δ s).2.2 *
                  gevZeroZ (gevStep (μ₀, σ₀, 0) Δ s) (X k ω) := by
                linarith only [neg_abs_le ((gevStep (μ₀, σ₀, 0) Δ s).2.2 *
                  gevZeroZ (gevStep (μ₀, σ₀, 0) Δ s) (X k ω)), hθseg k (Finset.mem_range.1 hk) s hs]
              exact (ContinuousAt.comp (f := fun r => (gevStep (μ₀, σ₀, 0) Δ r, X k ω))
                (g := fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroH p.1 (gevZeroBasis i) (gevZeroBasis j) p.2)
                (continuousAt_gevZeroH_basis hσs hus i j)
                (by unfold gevStep; fun_prop)).continuousWithinAt
            exact (continuous_const.sub continuous_id).continuousOn.mul hH
          exact hcont.intervalIntegrable
        have htaylor_sum : ∑ k ∈ Finset.range n, (gevZeroLog θ_opt (X k ω) - gevZeroLog (μ₀, σ₀, 0) (X k ω)) =
            √(n : ℝ) * ⟪S_proc n ω, !₂[Δ.1, Δ.2.1, Δ.2.2]⟫ +
            ∫ s in (0 : ℝ)..1, (1 - s) * ∑ k ∈ Finset.range n,
              gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω) := by
          have h1 := Finset.sum_congr rfl fun k hk =>
            gevZeroLog_sub_eq_taylor hσ₀ hθnbhd (hθseg k (Finset.mem_range.1 hk))
          rw [h1, Finset.sum_add_distrib]
          congr 1
          · have hD : ∑ k ∈ Finset.range n, gevZeroD (μ₀, σ₀, 0) Δ (X k ω) =
                √(n : ℝ) * ⟪S_proc n ω, !₂[Δ.1, Δ.2.1, Δ.2.2]⟫ := by
              rw [inner_smul_left, sum_inner]
              simp only [map_inv₀, conj_trivial]
              rw [← mul_assoc, mul_inv_cancel₀ (sqrt_pos.2 hn0).ne', one_mul]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [gevZeroD_zero_eq_gumbelScore]
              simp [gumbelScoreVec3, PiLp.inner_apply, Fin.sum_univ_three]
            exact hD
          · rw [← intervalIntegral.integral_finsetSum hint_k]
            refine intervalIntegral.integral_congr fun s _ => ?_
            rw [Finset.mul_sum]
        -- Bound the integral term above by `-(lam / 4) * n * (Δ₀² + Δ₁² + Δ₂²)`
        have hint_le : ∫ s in (0 : ℝ)..1, (1 - s) * ∑ k ∈ Finset.range n,
              gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω) ≤
            -(lam / 4) * (n : ℝ) * (Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2) := by
          have hpt_s : ∀ s ∈ Icc (0 : ℝ) 1,
              (1 - s) * ∑ k ∈ Finset.range n, gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω) ≤
              (1 - s) * (-(lam / 2) * (n : ℝ) * (Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2)) := by
            intro s hs
            have hm := gevStep_mem_gevZeroNbhd hθnbhd hs.1 hs.2
            have hs1 : |(gevStep (μ₀, σ₀, 0) Δ s).1 - μ₀| ≤ δ₀ := by
              simp only [gevStep, add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
              nlinarith only [hs.2, hθ1δ, abs_nonneg Δ.1]
            have hs2 : |(gevStep (μ₀, σ₀, 0) Δ s).2.1 - σ₀| ≤ δ₀ := by
              simp only [gevStep, add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
              nlinarith only [hs.2, hθ2δ, abs_nonneg Δ.2.1]
            have hs3 : |(gevStep (μ₀, σ₀, 0) Δ s).2.2| ≤ δ₀ := by
              simp only [gevStep, zero_add, abs_mul, abs_of_nonneg hs.1]
              nlinarith only [hs.2, hθ3δ, abs_nonneg Δ.2.2]
            have havg := hH_neg (gevStep (μ₀, σ₀, 0) Δ s) Δ hs1 hs2 hs3 hm (fun k hk => hθseg k hk s hs)
            have hmul := mul_le_mul_of_nonneg_left havg hn0.le
            rw [← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul] at hmul
            exact mul_le_mul_of_nonneg_left (by linarith only [hmul]) (by linarith only [hs.2])
          have hint_lhs : IntervalIntegrable (fun s => (1 - s) * ∑ k ∈ Finset.range n,
              gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω)) volume 0 1 := by
            have : (fun s => (1 - s) * ∑ k ∈ Finset.range n, gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω)) =
                ∑ k ∈ Finset.range n, fun s => (1 - s) * gevZeroH (gevStep (μ₀, σ₀, 0) Δ s) Δ Δ (X k ω) := by
              funext s; simp [Finset.mul_sum]
            rw [this]
            exact IntervalIntegrable.sum _ hint_k
          have hint_rhs : IntervalIntegrable
              (fun s : ℝ => (1 - s) * (-(lam / 2) * (n : ℝ) * (Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2)))
              volume 0 1 := ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable _ _
          have hle := intervalIntegral.integral_mono_on zero_le_one hint_lhs hint_rhs hpt_s
          have heval : ∫ s in (0 : ℝ)..1,
              (1 - s) * (-(lam / 2) * (n : ℝ) * (Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2)) =
              -(lam / 4) * (n : ℝ) * (Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2) := by
            have h1s : ∫ s in (0 : ℝ)..1, (1 - s) = 1 / 2 := by
              have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => r - r ^ 2 / 2) (1 - s) s :=
                fun s _ => by
                  have h := (hasDerivAt_id s).sub (((hasDerivAt_id s).pow 2).div_const 2)
                  refine h.congr_deriv ?_; simp only [id_eq]; ring
              rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
                ((continuous_const.sub continuous_id).intervalIntegrable 0 1)]
              norm_num
            rw [intervalIntegral.integral_mul_const, h1s]
            ring
          linarith only [hle, heval]
        -- Bound the linear term via Cauchy-Schwarz
        have hlin_le : √(n : ℝ) * ⟪S_proc n ω, !₂[Δ.1, Δ.2.1, Δ.2.2]⟫ <
            (lam / 16) * (n : ℝ) * (r n) ^ 2 := by
          have hcs := abs_real_inner_le_norm (S_proc n ω) !₂[Δ.1, Δ.2.1, Δ.2.2]
          have hnorm_Δ : ‖(!₂[Δ.1, Δ.2.1, Δ.2.2] : EuclideanSpace ℝ (Fin 3))‖ =
              √(Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2) := by
            rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_three, Real.norm_eq_abs]
          have h1 : ⟪S_proc n ω, !₂[Δ.1, Δ.2.1, Δ.2.2]⟫ ≤ ‖S_proc n ω‖ * (4 * r n) :=
            (le_abs_self _).trans (hcs.trans (by rw [hnorm_Δ]; exact mul_le_mul_of_nonneg_left hΔ_ub (norm_nonneg _)))
          have h2 : √(n : ℝ) * (‖S_proc n ω‖ * (4 * r n)) <
              √(n : ℝ) * (((lam / 64) * (√(n : ℝ) * r n)) * (4 * r n)) := by
            have hsq0 : 0 < √(n : ℝ) := sqrt_pos.2 hn0
            have h4r : 0 < 4 * r n := by linarith only [hr_pos n]
            exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hSlt h4r) hsq0
          have hsqn : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
          have h3 : √(n : ℝ) * (((lam / 64) * (√(n : ℝ) * r n)) * (4 * r n)) =
              (lam / 16) * (n : ℝ) * (r n) ^ 2 := by
            calc _ = (lam / 16) * (√(n : ℝ) * √(n : ℝ)) * (r n) ^ 2 := by ring
              _ = (lam / 16) * (n : ℝ) * (r n) ^ 2 := by rw [hsqn]
          linarith only [mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (n : ℝ)), h2, h3]
        have hstrict : ∑ k ∈ Finset.range n, gevZeroLog θ_opt (X k ω) <
            ∑ k ∈ Finset.range n, gevZeroLog (μ₀, σ₀, 0) (X k ω) := by
          have hsub_neg : ∑ k ∈ Finset.range n, (gevZeroLog θ_opt (X k ω) - gevZeroLog (μ₀, σ₀, 0) (X k ω)) < 0 := by
            rw [htaylor_sum]
            have hneg2 : -(lam / 4) * (n : ℝ) * (Δ.1 ^ 2 + Δ.2.1 ^ 2 + Δ.2.2 ^ 2) ≤
                -(9 * lam / 64) * (n : ℝ) * (r n) ^ 2 := by
              have := mul_le_mul_of_nonneg_left hΔ_lb (show (0 : ℝ) ≤ (lam / 4) * (n : ℝ) by positivity)
              linarith only [this]
            have hpos_nr : 0 < (5 * lam / 64) * (n : ℝ) * (r n) ^ 2 := by positivity
            linarith only [hlin_le, hint_le, hneg2, hpos_nr]
          rw [Finset.sum_sub_distrib] at hsub_neg
          linarith only [hsub_neg]
        -- Compare with `d₀ := (μ₀ - p₂.1, σ₀ - p₂.2, 0) ∈ cube n`, contradicting maximality of `d_opt`!
        set d₀ : ℝ × ℝ × ℝ := (μ₀ - p₂.1, σ₀ - p₂.2, 0)
        have hd₀_mem : d₀ ∈ cube n := by
          have h1 : |μ₀ - p₂.1| ≤ r n := by rw [abs_sub_comm]; linarith only [hp2lt, abs_nonneg (p₂.2 - σ₀), hr_pos n]
          have h2 : |σ₀ - p₂.2| ≤ r n := by rw [abs_sub_comm]; linarith only [hp2lt, abs_nonneg (p₂.1 - μ₀), hr_pos n]
          exact ⟨abs_le.1 h1, abs_le.1 h2, by linarith only [hr_pos n], (hr_pos n).le⟩
        have hmax_le := (hδ n x).2 hd₀_mem
        simp only [mem_ofPred_eq] at hmax_le
        have hσ_opt : 0 < θ_opt.2.1 := by linarith [(mem_gevZeroNbhd_bounds hθnbhd).2.1]
        have hadm_opt : ∀ i : Fin n, 0 < 1 + θ_opt.2.2 * gevZeroZ θ_opt (x i) := fun i => by
          have hs1 := hθseg i.1 i.2 1 ⟨zero_le_one, le_rfl⟩
          have hst : gevStep (μ₀, σ₀, 0) Δ 1 = θ_opt := by simp [gevStep, Δ]
          rw [hst] at hs1
          linarith [neg_abs_le (θ_opt.2.2 * gevZeroZ θ_opt (x i))]
        have hlik_opt : gevLogLikE d_opt.2.2 (p₂.1 + d_opt.1) (p₂.2 + d_opt.2.1) x =
            ((∑ k ∈ Finset.range n, gevZeroLog θ_opt (X k ω) : ℝ) : EReal) := by
          rw [gevLogLikE, ← Fin.sum_univ_eq_sum_range (fun k => gevZeroLog θ_opt (X k ω)) n,
            ereal_coe_finsetSum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hpos : 0 < gevLocScaleDensity θ_opt.2.2 θ_opt.1 θ_opt.2.1 (x i) := by
            rcases eq_or_ne θ_opt.2.2 0 with h0 | h0
            · simp only [gevLocScaleDensity, gevDensity, h0, ↓reduceIte]; positivity
            · exact gevLocScaleDensity_pos hσ_opt h0 (hadm_opt i)
          rw [gevLogDensityE_of_pos hpos, ← gevZeroLog_eq_log_density hσ_opt (hadm_opt i)]
        have hlik_0 : gevLogLikE d₀.2.2 (p₂.1 + d₀.1) (p₂.2 + d₀.2.1) x =
            ((∑ k ∈ Finset.range n, gevZeroLog (μ₀, σ₀, 0) (X k ω) : ℝ) : EReal) := by
          have hp1 : p₂.1 + d₀.1 = μ₀ := by simp [d₀]
          have hp2 : p₂.2 + d₀.2.1 = σ₀ := by simp [d₀]
          rw [hp1, hp2, gevLogLikE, ← Fin.sum_univ_eq_sum_range (fun k => gevZeroLog (μ₀, σ₀, 0) (X k ω)) n,
            ereal_coe_finsetSum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hpos : 0 < gevLocScaleDensity 0 μ₀ σ₀ (x i) := by
            simp only [gevLocScaleDensity, gevDensity, ↓reduceIte]; positivity
          have hl := gevZeroLog_eq_log_density (θ := (μ₀, σ₀, 0)) (x := x i) hσ₀ (by simp)
          change gevLogDensityE 0 μ₀ σ₀ (x i) = (gevZeroLog (μ₀, σ₀, 0) (x i) : EReal)
          rw [gevLogDensityE_of_pos hpos, ← hl]
        rw [hlik_opt, hlik_0, EReal.coe_le_coe_iff] at hmax_le
        linarith
      -- Since `d_opt` lies in the open interior of `cube n`, `θh n ω` is a genuine `IsLocalMax`!
      apply hω
      set U : Set (ℝ × ℝ × ℝ) :=
        Ioo (-r n) (r n) ×ˢ Ioo (p₂.1 - r n) (p₂.1 + r n) ×ˢ Ioo (p₂.2 - r n) (p₂.2 + r n)
      have hU_open : IsOpen U := isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)
      have hU_mem : θh n ω ∈ U := by
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := hd_int
        exact ⟨⟨h5, h6⟩, ⟨by simp [θh, g, p₂]; linarith, by simp [θh, g, p₂]; linarith⟩,
          ⟨by simp [θh, g, p₂]; linarith, by simp [θh, g, p₂]; linarith⟩⟩
      filter_upwards [hU_open.mem_nhds hU_mem] with q hq
      set d_q : ℝ × ℝ × ℝ := (q.2.1 - p₂.1, q.2.2 - p₂.2, q.1)
      have hdq_mem : d_q ∈ cube n :=
        ⟨⟨by linarith [hq.2.1.1], by linarith [hq.2.1.2]⟩,
         ⟨by linarith [hq.2.2.1], by linarith [hq.2.2.2]⟩,
         ⟨hq.1.1.le, hq.1.2.le⟩⟩
      have hmax_q := (hδ n x).2 hdq_mem
      simp only [mem_ofPred_eq, d_q] at hmax_q
      simpa [θh, g, x, p₂] using hmax_q
    refine (measure_mono hsub).trans ?_
    have h5 : P (⋃ i : Fin 3, ⋃ j : Fin 3,
        {ω | lam / 72 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
          (-gevFisherInfoZero σ₀ i j)|}) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, P {ω | lam / 72 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
          (-gevFisherInfoZero σ₀ i j)|} :=
      (measure_iUnion_fintype_le P _).trans (Finset.sum_le_sum fun _ _ => measure_iUnion_fintype_le P _)
    calc P _ ≤ P ({ω | r n / 4 ≤ |(g₂ n (fun i : Fin n => X i ω)).1 - μ₀| +
            |(g₂ n (fun i : Fin n => X i ω)).2 - σ₀|} ∪
          {ω | (1 / 16 : ℝ) ≤ r n * runMax (fun i => |(X i ω - μ₀) / σ₀|) n} ∪
         ({ω | (lam / 64) * (√(n : ℝ) * r n) ≤ ‖S_proc n ω‖} ∪
          {ω | lam / (144 * C₀) - μT ≤
            |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) - μT|})) +
          P (⋃ i : Fin 3, ⋃ j : Fin 3,
            {ω | lam / 72 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
              gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
              (-gevFisherInfoZero σ₀ i j)|}) := measure_union_le _ _
      _ ≤ (P _ + P _) + (P _ + P _) +
          ∑ i : Fin 3, ∑ j : Fin 3, P {ω | lam / 72 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
            (-gevFisherInfoZero σ₀ i j)|} := by
        refine add_le_add ?_ h5
        exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
      _ = _ := by ring
  exact ⟨g, hgm, hloc, tendstoInDistribution_gevLocalMLE_zero hσ₀ hX hind hθm hcons hξmax hloc hW⟩

end ExistenceZero

/-! ### Three-parameter GEV return-level normality and plug-in CI at `ξ₀ = 0` -/

section ReturnLevelZero

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- The asymptotic variance `∇z_mᵀ gevMLECovZero(σ) ∇z_m` of the three-parameter GEV return level
estimator at `ξ₀ = 0` ([Coles, §3.3.3]). -/
noncomputable def gevReturnLevelVarZero (σ m : ℝ) : ℝ :=
  gevReturnLevelGrad 0 σ m ⬝ᵥ gevMLECovZero σ *ᵥ gevReturnLevelGrad 0 σ m

/-- `gevReturnLevelVarZero σ m > 0` for every `σ > 0` and every `m`. -/
theorem gevReturnLevelVarZero_pos {σ : ℝ} (hσ : 0 < σ) (m : ℝ) :
    0 < gevReturnLevelVarZero σ m := by
  have hne : (fun i => gevReturnLevelGrad 0 σ m i) ≠ 0 := fun h => by
    have := congrFun h 1
    simp [gevReturnLevelGrad] at this
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 (posDef_gevMLECovZero hσ)).2 hne
  simpa [gevReturnLevelVarZero] using this

/-- Scaling identity: `gevFisherInfoZero σ = D(σ) I₀(1) D(σ)` with `D(σ) = diag(σ⁻¹, σ⁻¹, 1)`,
so `gevReturnLevelVarZero σ m = σ² · gevReturnLevelVarZero 1 m`. -/
theorem gevReturnLevelVarZero_eq_sq_mul {σ : ℝ} (hσ : 0 < σ) (m : ℝ) :
    gevReturnLevelVarZero σ m = σ ^ 2 * gevReturnLevelVarZero 1 m := by
  set D : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![σ⁻¹, σ⁻¹, 1]
  set Dinv : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![σ, σ, 1]
  have hDD : D * Dinv = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [D, Dinv, Matrix.mul_apply, Fin.sum_univ_three, hσ.ne']
  have hDinvD : Dinv * D = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [D, Dinv, Matrix.mul_apply, Fin.sum_univ_three, hσ.ne']
  have hI_scale : gevFisherInfoZero σ = D * gevFisherInfoZero 1 * D := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, gevFisherInfoZero, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have hIinv_scale : (gevFisherInfoZero σ)⁻¹ = Dinv * (gevFisherInfoZero 1)⁻¹ * Dinv := by
    have hdet1 : IsUnit (gevFisherInfoZero 1).det :=
      isUnit_iff_ne_zero.2 (posDef_gevFisherInfoZero one_pos).det_pos.ne'
    have hdetσ : IsUnit (gevFisherInfoZero σ).det :=
      isUnit_iff_ne_zero.2 (posDef_gevFisherInfoZero hσ).det_pos.ne'
    have hmul : (Dinv * (gevFisherInfoZero 1)⁻¹ * Dinv) * gevFisherInfoZero σ = 1 := by
      rw [hI_scale]
      calc Dinv * (gevFisherInfoZero 1)⁻¹ * Dinv * (D * gevFisherInfoZero 1 * D)
          = Dinv * (gevFisherInfoZero 1)⁻¹ * (Dinv * D) * gevFisherInfoZero 1 * D := by
            simp only [Matrix.mul_assoc]
        _ = Dinv * ((gevFisherInfoZero 1)⁻¹ * gevFisherInfoZero 1) * D := by
            rw [hDinvD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = Dinv * D := by rw [Matrix.nonsing_inv_mul _ hdet1, Matrix.mul_one]
        _ = 1 := hDinvD
    calc (gevFisherInfoZero σ)⁻¹ = 1 * (gevFisherInfoZero σ)⁻¹ := (Matrix.one_mul _).symm
      _ = ((Dinv * (gevFisherInfoZero 1)⁻¹ * Dinv) * gevFisherInfoZero σ) * (gevFisherInfoZero σ)⁻¹ := by
          rw [hmul]
      _ = (Dinv * (gevFisherInfoZero 1)⁻¹ * Dinv) * (gevFisherInfoZero σ * (gevFisherInfoZero σ)⁻¹) :=
          Matrix.mul_assoc _ _ _
      _ = Dinv * (gevFisherInfoZero 1)⁻¹ * Dinv := by
          rw [Matrix.mul_nonsing_inv _ hdetσ, Matrix.mul_one]
  -- Evaluate `gevReturnLevelVarZero σ m` explicitly using `hIinv_scale`
  have hcov_entry : ∀ i j : Fin 3,
      gevMLECovZero σ i j = (![1, σ, σ] i) * (![1, σ, σ] j) * gevMLECovZero 1 i j := by
    intro i j
    simp only [gevMLECovZero, Matrix.submatrix_apply, hIinv_scale]
    fin_cases i <;> fin_cases j <;>
      simp [Dinv, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  simp only [gevReturnLevelVarZero, dotProduct, Matrix.mulVec, Fin.sum_univ_three, hcov_entry,
    gevReturnLevelGrad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

lemma continuousAt_gevReturnLevelVarZero {σ : ℝ} (hσ : 0 < σ) (m : ℝ) :
    ContinuousAt (fun s => gevReturnLevelVarZero s m) σ := by
  have hev : (fun s => gevReturnLevelVarZero s m) =ᶠ[𝓝 σ]
      fun s => s ^ 2 * gevReturnLevelVarZero 1 m := by
    filter_upwards [lt_mem_nhds hσ] with s hs
    exact gevReturnLevelVarZero_eq_sq_mul hs m
  refine ContinuousAt.congr ?_ hev.symm
  fun_prop

lemma measurable_gevReturnLevelVarZero (m : ℝ) : Measurable fun σ : ℝ => gevReturnLevelVarZero σ m := by
  have h1 : ∀ σ : ℝ, gevReturnLevelVarZero σ m =
      (if 0 < σ then σ ^ 2 * gevReturnLevelVarZero 1 m else gevReturnLevelVarZero σ m) := fun σ => by
    split_ifs with h
    · exact gevReturnLevelVarZero_eq_sq_mul h m
    · rfl
  -- Direct measurability on `(0, ∞)` is not needed if we use `ContinuousOn` or direct formula on `s ↦ s^2 * c`!
  -- Actually `gevReturnLevelVarZero σ m` is defined via `(gevFisherInfoZero σ)⁻¹`, which is a polynomial
  -- of `σ⁻¹` divided by `det`, hence directly measurable!
  have hI : ∀ i j : Fin 3, Measurable fun σ : ℝ => gevFisherInfoZero σ i j := fun i j => by
    fin_cases i <;> fin_cases j <;> simp only [gevFisherInfoZero, Matrix.of_apply] <;> fun_prop
  have hdet : Measurable fun σ : ℝ => (gevFisherInfoZero σ).det := by
    simp only [Matrix.det_fin_three]
    have := hI 0 0; have := hI 0 1; have := hI 0 2
    have := hI 1 0; have := hI 1 1; have := hI 1 2
    have := hI 2 0; have := hI 2 1; have := hI 2 2
    fun_prop
  have hadj : ∀ i j : Fin 3, Measurable fun σ : ℝ => (gevFisherInfoZero σ).adjugate i j := fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one] <;>
      have := hI 0 0 <;> have := hI 0 1 <;> have := hI 0 2 <;>
      have := hI 1 0 <;> have := hI 1 1 <;> have := hI 1 2 <;>
      have := hI 2 0 <;> have := hI 2 1 <;> have := hI 2 2 <;>
      fun_prop
  have hinv : ∀ i j : Fin 3, Measurable fun σ : ℝ => (gevFisherInfoZero σ)⁻¹ i j := fun i j => by
    have heq : (fun σ : ℝ => (gevFisherInfoZero σ)⁻¹ i j) =
        fun σ => (gevFisherInfoZero σ).det⁻¹ * (gevFisherInfoZero σ).adjugate i j := by
      funext σ
      rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    rw [heq]
    exact hdet.inv.mul (hadj i j)
  have hcov : ∀ i j : Fin 3, Measurable fun σ : ℝ => gevMLECovZero σ i j := fun i j =>
    hinv (![2, 0, 1] i) (![2, 0, 1] j)
  simp only [gevReturnLevelVarZero, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    gevReturnLevelGrad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  have := hcov 0 0; have := hcov 0 1; have := hcov 0 2
  have := hcov 1 0; have := hcov 1 1; have := hcov 1 2
  have := hcov 2 0; have := hcov 2 1; have := hcov 2 2
  fun_prop

/-- **Three-parameter GEV return-level asymptotic normality at `ξ₀ = 0`** ([Coles, §3.3.3]):
for any three-parameter local MLE satisfying the hypotheses of `tendstoInDistribution_gevLocalMLE_zero`,
`√n (ẑ_m - z_m) ⇒ N(0, gevReturnLevelVarZero σ₀ m)`. -/
theorem tendstoInDistribution_gevLocalMLEReturnLevel_zero {μ₀ σ₀ m : ℝ} (hσ₀ : 0 < σ₀) (hm : 1 < m)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P)
    (hind : iIndepFun X P) {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : TendstoInMeasure P θh atTop (fun _ => ((0 : ℝ), μ₀, σ₀)))
    (hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).1| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0))
    (hloc : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω)})
      atTop (𝓝 0))
    {W : Ω' → ℝ} (hW : HasLaw W (gaussianReal 0 (gevReturnLevelVarZero σ₀ m).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m - gevReturnLevel 0 μ₀ σ₀ m))
      atTop W (fun _ => P) P' := by
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (gevMLECovZero σ₀))
      (multivariateGaussian 0 (gevMLECovZero σ₀)) := HasLaw.id
  have hθN : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - 0, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀])
      atTop id (fun _ => P) (multivariateGaussian 0 (gevMLECovZero σ₀)) := by
    simpa only [sub_zero] using
      tendstoInDistribution_gevLocalMLE_zero hσ₀ hX hind hθm hcons hξmax hloc hZ
  exact tendstoInDistribution_gevReturnLevel_all (ξ₀ := 0) (μ₀ := μ₀) (σ₀ := σ₀) hm hθm
    (posSemidef_gevMLECovZero hσ₀) hθN hZ hW

/-- **Computable plug-in confidence interval for the three-parameter GEV return level at `ξ₀ = 0`**:
with plug-in standard error `ŝₙ = √(gevReturnLevelVarZero σ̂ₙ m)`, the Wald interval
`[ẑ_m - z ŝₙ/√n, ẑ_m + z ŝₙ/√n]` has asymptotic coverage `N(0, 1)([-z, z])`. -/
theorem tendsto_measure_mem_gevLocalMLEReturnLevelPlugInInterval_zero {μ₀ σ₀ m : ℝ}
    (hσ₀ : 0 < σ₀) (hm : 1 < m) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : TendstoInMeasure P θh atTop (fun _ => ((0 : ℝ), μ₀, σ₀)))
    (hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).1| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0))
    (hloc : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω)})
      atTop (𝓝 0)) (z : ℝ) :
    Tendsto (fun n : ℕ => P {ω | gevReturnLevel 0 μ₀ σ₀ m ∈ Icc
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m -
        z * √(gevReturnLevelVarZero (θh n ω).2.2 m) / √(n : ℝ))
      (gevReturnLevel (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 m +
        z * √(gevReturnLevelVarZero (θh n ω).2.2 m) / √(n : ℝ))})
      atTop (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hvpos : 0 < gevReturnLevelVarZero σ₀ m := gevReturnLevelVarZero_pos hσ₀ m
  have hZ : HasLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 3)) (gevMLECovZero σ₀))
      (multivariateGaussian 0 (gevMLECovZero σ₀)) := HasLaw.id
  have hθN : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - 0, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀])
      atTop id (fun _ => P) (multivariateGaussian 0 (gevMLECovZero σ₀)) := by
    simpa only [sub_zero] using
      tendstoInDistribution_gevLocalMLE_zero hσ₀ hX hind hθm hcons hξmax hloc hZ
  have hS : TendstoInMeasure P (fun (n : ℕ) ω => √(gevReturnLevelVarZero (θh n ω).2.2 m))
      atTop (fun _ => √(gevReturnLevelVarZero σ₀ m)) := by
    have hcont : ContinuousAt (fun p : ℝ × ℝ × ℝ => √(gevReturnLevelVarZero p.2.2 m)) (0, μ₀, σ₀) :=
      (ContinuousAt.comp (g := fun s => gevReturnLevelVarZero s m)
        (f := fun p : ℝ × ℝ × ℝ => p.2.2) (x := (0, μ₀, σ₀))
        (continuousAt_gevReturnLevelVarZero hσ₀ m) (by fun_prop)).sqrt
    exact hcons.comp_continuousAt hcont
  have hSm : ∀ n, AEMeasurable (fun ω => √(gevReturnLevelVarZero (θh n ω).2.2 m)) P := fun n =>
    (((measurable_gevReturnLevelVarZero m).comp (measurable_snd.comp measurable_snd)).comp_aemeasurable
      (hθm n)).sqrt
  exact tendsto_measure_mem_gevReturnLevelInterval_all (ξ₀ := 0) (μ₀ := μ₀) (σ₀ := σ₀) hm hθm
    (posSemidef_gevMLECovZero hσ₀) hθN hZ (sqrt_pos.2 hvpos) (sq_sqrt hvpos.le) hS hSm z

end ReturnLevelZero

end ExtremeValueTheory




