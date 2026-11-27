/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDWilks.Regular
import ExtremeValueTheory.Statistics.GEVMLENormality
import ExtremeValueTheory.Statistics.GEVMLENormalityZero

/-!
# Wilks' theorem and deviance confidence regions for the three-parameter GEV family

Let `X₀, X₁, …` be iid with the location-scale GEV law `GEV(ξ₀, μ₀, σ₀)` in the regular range
`ξ₀ > -1/2`, `σ₀ > 0` (both `ξ₀ ≠ 0` and the Gumbel boundary `ξ₀ = 0`). We prove the
three-parameter GEV Wilks' theorem and deviance confidence region coverage ([Coles, §2.6.5];
[Smith 1985]; [Bücher–Segers 2017]):

* **General `χ²` tools:**
  * `nullSingletonClass_chiSquared_succ`: `χ²_{k+1}` has no atoms for every `k : ℕ` (in particular
    `χ²₃` has no atoms).
  * `hasLaw_dotProduct_inv_mulVec_chiSquared`: if `I : Matrix (Fin d) (Fin d) ℝ` is positive
    definite and `W ~ N(0, I)`, then `Wᵀ I⁻¹ W ~ χ²_d` (via the real spectral theorem).
* **Non-Gumbel regular case (`ξ₀ > -1/2`, `ξ₀ ≠ 0`):**
  * `tendstoInMeasure_gevLocalDeviance_sub`:
    `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - Zₙᵀ I(θ₀)⁻¹ Zₙ → 0` in probability for consistent local maximizers.
  * `tendstoInDistribution_gevLocalDeviance`, `tendstoInDistribution_gevDeviance`:
    `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ⇒ χ²₃`.
  * `tendsto_measure_mem_gevDevianceRegion`:
    `P((ξ₀, μ₀, σ₀) ∈ gevDevianceRegion K c X) → χ²₃((-∞, c])`.
* **Gumbel boundary (`ξ₀ = 0`):**
  * `tendstoInMeasure_gevLocalDeviance_zero_sub`:
    `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - Sₙᵀ I₀(σ₀)⁻¹ Sₙ → 0` in probability.
  * `tendstoInDistribution_gevLocalDeviance_zero`: `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ⇒ χ²₃`.
  * `tendsto_measure_mem_gevLocalDeviance_zero`:
    `P(2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ≤ c) → χ²₃((-∞, c])`.
  * `exists_gevLocalMLE_deviance_tendstoInDistribution_zero`: unconditional existence of a
    data-driven measurable local MLE `gₙ : ℝⁿ → ℝ³` whose deviance converges to `χ²₃`.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §2.6.5.
* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* A. Bücher and J. Segers, *On the maximum likelihood estimator for the Generalized Extreme-Value
  distribution*, Extremes 20 (2017).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §16.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

namespace ExtremeValueTheory

/-! ### General `χ²_d` lemmas: atomlessness and positive-definite quadratic forms -/

section ChiSquaredGeneral

/-- For every `k : ℕ`, `χ²_{k + 1}` has no atoms. -/
instance nullSingletonClass_chiSquared_succ (k : ℕ) : NullSingletonClass (chiSquared (k + 1)) where
  measure_singleton c := by
    have hns := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    let μk : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1
    let μ1 : Measure ℝ := gaussianReal 0 1
    have hmp1 := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) 0).symm
    have hmp2 := (Measure.measurePreserving_swap (μ := μk) (ν := μ1))
    have hmp := hmp1.comp hmp2
    have hpi : (Measure.pi fun _ : Fin (k + 1) => gaussianReal 0 1) =
        (μk.prod μ1).map (fun p : (Fin k → ℝ) × ℝ => Fin.cons p.2 p.1) := by
      rw [← hmp.map_eq]
      congr 1
      funext ⟨y, x⟩
      ext i
      refine Fin.cases ?_ ?_ i <;>
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    have hchi : chiSquared (k + 1) =
        (μk.prod μ1).map (fun p : (Fin k → ℝ) × ℝ => p.2 ^ 2 + ∑ i : Fin k, (p.1 i) ^ 2) := by
      rw [chiSquared, ← map_pi_eq_stdGaussian, hpi,
        Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext p
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    have hf : Measurable fun p : (Fin k → ℝ) × ℝ => p.2 ^ 2 + ∑ i : Fin k, (p.1 i) ^ 2 := by
      refine (measurable_snd.pow_const 2).add (Finset.measurable_sum _ fun i _ => ?_)
      exact ((measurable_pi_apply i).comp measurable_fst).pow_const 2
    rw [hchi, Measure.map_apply hf (measurableSet_singleton c)]
    have hms : MeasurableSet ((fun p : (Fin k → ℝ) × ℝ => p.2 ^ 2 + ∑ i : Fin k, (p.1 i) ^ 2) ⁻¹' {c}) :=
      hf (measurableSet_singleton c)
    rw [Measure.measure_prod_null hms]
    refine Eventually.of_forall fun y => ?_
    set r : ℝ := c - ∑ i : Fin k, (y i) ^ 2
    refine measure_mono_null (t := {√r, -√r}) (fun x hx => ?_) ?_
    · simp only [mem_preimage, mem_singleton_iff] at hx
      have hrx : r = x ^ 2 := by linarith
      simp only [mem_insert_iff, mem_singleton_iff, hrx]
      rcases le_total 0 x with h | h
      · exact Or.inl (Real.sqrt_sq h).symm
      · exact Or.inr (by rw [Real.sqrt_sq_eq_abs, abs_of_nonpos h, neg_neg])
    · exact (Set.toFinite _).measure_zero _

/-- **Chi-squared quadratic form for any positive-definite covariance matrix `I`.**
If `W ~ N(0, I)` in `ℝᵈ` with `I` positive definite, then `Wᵀ I⁻¹ W ~ χ²_d`. -/
theorem hasLaw_dotProduct_inv_mulVec_chiSquared {d : ℕ} {I : Matrix (Fin d) (Fin d) ℝ}
    (hI : I.PosDef) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {W : Ω' → EuclideanSpace ℝ (Fin d)}
    (hW : HasLaw W (multivariateGaussian 0 I) P') :
    HasLaw (fun ω => (W ω).ofLp ⬝ᵥ I⁻¹ *ᵥ (W ω).ofLp) (chiSquared d) P' := by
  have hH : I.IsHermitian := hI.isHermitian
  let U : Matrix (Fin d) (Fin d) ℝ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  let ev : Fin d → ℝ := hH.eigenvalues
  have hev : ∀ i, 0 < ev i := hI.eigenvalues_pos
  have hUU : U * Uᵀ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2)
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hUtU : Uᵀ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2)
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hspec : I = U * Matrix.diagonal ev * Uᵀ := by
    have h := hH.spectral_theorem
    simpa [U, ev, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Function.comp_def, Matrix.mul_assoc] using h
  let D : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (fun i => (√(ev i))⁻¹)
  let B : Matrix (Fin d) (Fin d) ℝ := D * Uᵀ
  have hDt : Dᵀ = D := Matrix.diagonal_transpose _
  have hBt : Bᵀ = U * D := by rw [Matrix.transpose_mul, Matrix.transpose_transpose, hDt]
  have hBIB : B * I * Bᵀ = 1 := by
    calc B * I * Bᵀ
        = (D * Uᵀ) * (U * Matrix.diagonal ev * Uᵀ) * (U * D) := by rw [hspec, hBt]
      _ = D * (Uᵀ * U) * Matrix.diagonal ev * (Uᵀ * U) * D := by simp only [Matrix.mul_assoc]
      _ = D * Matrix.diagonal ev * D := by rw [hUtU, Matrix.mul_one, Matrix.mul_one]
      _ = Matrix.diagonal (fun i => (√(ev i))⁻¹ * ev i * (√(ev i))⁻¹) := by
            simp only [D, Matrix.diagonal_mul_diagonal]
      _ = 1 := by
            rw [← Matrix.diagonal_one]
            congr 1; funext i
            have hsq : √(ev i) * √(ev i) = ev i := Real.mul_self_sqrt (hev i).le
            have hne : √(ev i) ≠ 0 := (Real.sqrt_pos.2 (hev i)).ne'
            calc (√(ev i))⁻¹ * ev i * (√(ev i))⁻¹
                = (√(ev i))⁻¹ * (√(ev i) * √(ev i)) * (√(ev i))⁻¹ := by rw [hsq]
              _ = 1 := by field_simp [hne]
  have hBtBI : (Bᵀ * B) * I = 1 := by
    calc (Bᵀ * B) * I
        = (U * D) * (D * Uᵀ) * (U * Matrix.diagonal ev * Uᵀ) := by rw [hBt, hspec]
      _ = U * (D * D) * (Uᵀ * U) * Matrix.diagonal ev * Uᵀ := by simp only [Matrix.mul_assoc]
      _ = U * (D * D * Matrix.diagonal ev) * Uᵀ := by
            rw [hUtU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = U * 1 * Uᵀ := by
            congr 2
            simp only [D, Matrix.diagonal_mul_diagonal]
            rw [← Matrix.diagonal_one]
            congr 1; funext i
            have hsq : √(ev i) * √(ev i) = ev i := Real.mul_self_sqrt (hev i).le
            have hne : √(ev i) ≠ 0 := (Real.sqrt_pos.2 (hev i)).ne'
            calc (√(ev i))⁻¹ * (√(ev i))⁻¹ * ev i
                = (√(ev i))⁻¹ * (√(ev i))⁻¹ * (√(ev i) * √(ev i)) := by rw [hsq]
              _ = 1 := by field_simp [hne]
      _ = 1 := by rw [Matrix.mul_one, hUU]
  have hIinv : I * I⁻¹ = 1 :=
    Matrix.mul_nonsing_inv I (Matrix.isUnit_iff_isUnit_det I |>.1 hI.isUnit)
  have hBtB : Bᵀ * B = I⁻¹ := by
    calc Bᵀ * B = (Bᵀ * B) * 1 := (Matrix.mul_one _).symm
      _ = (Bᵀ * B) * (I * I⁻¹) := by rw [hIinv]
      _ = ((Bᵀ * B) * I) * I⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 * I⁻¹ := by rw [hBtBI]
      _ = I⁻¹ := Matrix.one_mul _
  -- Linear map `L v = toLp 2 (B *ᵥ v.ofLp)` sends `N(0, I)` to `stdGaussian`
  let L : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun v => WithLp.toLp 2 (B *ᵥ v.ofLp)
  have hL_cont : Continuous L := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp (continuous_pi fun i => ?_)
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _))
  have hLW : HasLaw (fun ω => L (W ω)) (stdGaussian (EuclideanSpace ℝ (Fin d))) P' := by
    refine ⟨hL_cont.measurable.comp_aemeasurable hW.aemeasurable, ?_⟩
    rw [← multivariateGaussian_zero_one]
    have hmap : P'.map (fun ω => L (W ω)) = (multivariateGaussian 0 I).map L := by
      rw [← hW.map_eq, AEMeasurable.map_map_of_aemeasurable hL_cont.measurable.aemeasurable hW.aemeasurable]
      rfl
    rw [hmap]
    refine Measure.ext_of_charFun ?_
    ext t
    rw [charFun_multivariateGaussian Matrix.PosSemidef.one,
      charFun_apply, integral_map hL_cont.measurable.aemeasurable
        (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) =>
          Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)).aestronglyMeasurable]
    let tB : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Bᵀ *ᵥ t.ofLp)
    have hinner : ∀ x : EuclideanSpace ℝ (Fin d), ⟪L x, t⟫ = ⟪x, tB⟫ := fun x => by
      have h1 : ⟪L x, t⟫ = t.ofLp ⬝ᵥ B *ᵥ x.ofLp := by
        simp [L, PiLp.inner_apply, dotProduct]
      have h2 : ⟪x, tB⟫ = (Bᵀ *ᵥ t.ofLp) ⬝ᵥ x.ofLp := by
        simp [tB, PiLp.inner_apply, dotProduct, mul_comm]
      rw [h1, h2, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    simp_rw [hinner]
    have hcf : ∫ x, Complex.exp ((⟪x, tB⟫ : ℝ) * Complex.I) ∂(multivariateGaussian 0 I) =
        charFun (multivariateGaussian 0 I) tB := by rw [charFun_apply]
    rw [hcf, charFun_multivariateGaussian hI.posSemidef]
    congr 1
    have hq : tB.ofLp ⬝ᵥ I *ᵥ tB.ofLp = t.ofLp ⬝ᵥ (1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ t.ofLp := by
      have h1 : tB.ofLp = Bᵀ *ᵥ t.ofLp := rfl
      rw [h1, ← hBIB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec t.ofLp B, ← Matrix.mulVec_transpose]
    simp [hq]
  have hsq := hLW.norm_sq_chiSquared
  refine hsq.congr (ae_of_all _ fun ω => ?_)
  dsimp only
  have hnorm : ‖L (W ω)‖ ^ 2 = (B *ᵥ (W ω).ofLp) ⬝ᵥ (B *ᵥ (W ω).ofLp) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [L, dotProduct, sq]
  calc (W ω).ofLp ⬝ᵥ I⁻¹ *ᵥ (W ω).ofLp
      = (W ω).ofLp ⬝ᵥ (Bᵀ * B) *ᵥ (W ω).ofLp := by rw [hBtB]
    _ = (W ω).ofLp ⬝ᵥ Bᵀ *ᵥ (B *ᵥ (W ω).ofLp) := by rw [Matrix.mulVec_mulVec]
    _ = (B *ᵥ (W ω).ofLp) ⬝ᵥ (B *ᵥ (W ω).ofLp) := by
          rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = ‖L (W ω)‖ ^ 2 := hnorm.symm

/-- Algebraic completion-of-the-square identity for any symmetric invertible matrix `I`:
`2 (U · Z) - Uᵀ I U = Zᵀ I⁻¹ Z - (U - I⁻¹ Z)ᵀ I (U - I⁻¹ Z)`. -/
lemma two_mul_dotProduct_sub_quad_eq {d : ℕ} {I : Matrix (Fin d) (Fin d) ℝ}
    (hIsym : Iᵀ = I) (hIinv : I * I⁻¹ = 1) (U Z : Fin d → ℝ) :
    2 * (U ⬝ᵥ Z) - U ⬝ᵥ I *ᵥ U =
      Z ⬝ᵥ I⁻¹ *ᵥ Z - (U - I⁻¹ *ᵥ Z) ⬝ᵥ I *ᵥ (U - I⁻¹ *ᵥ Z) := by
  have h1 : I *ᵥ (I⁻¹ *ᵥ Z) = Z := by rw [Matrix.mulVec_mulVec, hIinv, Matrix.one_mulVec]
  have h2 : (I⁻¹ *ᵥ Z) ⬝ᵥ I *ᵥ U = U ⬝ᵥ Z := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hIsym, h1, dotProduct_comm]
  rw [Matrix.mulVec_sub, h1, sub_dotProduct, dotProduct_sub, dotProduct_sub, h2]
  have h4 : (I⁻¹ *ᵥ Z) ⬝ᵥ Z = Z ⬝ᵥ I⁻¹ *ᵥ Z := dotProduct_comm _ _
  rw [h4]
  ring

end ChiSquaredGeneral

/-! ### GEV log-likelihood definitions and measurability -/

section Defs

/-- The real GEV log-likelihood of the first `n` observations `x 0, …, x (n - 1)`. -/
noncomputable def gevLogLikN (ξ μ σ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, log (gevLocScaleDensity ξ μ σ (x i))

/-- The maximized extended-real GEV log-likelihood `sup_{θ ∈ K} ℓₙ(θ)`. -/
noncomputable def gevMaxLogLik (K : Set (ℝ × ℝ × ℝ)) {n : ℕ} (x : Fin n → ℝ) : EReal :=
  ⨆ p ∈ K, gevLogLikE p.1 p.2.1 p.2.2 x

/-- The **deviance confidence region** for the three-parameter GEV parameter `θ = (ξ, μ, σ)`
([Coles, §2.6.5]): `{θ ∈ K : 2 (sup_K ℓₙ - ℓₙ(θ)) ≤ c}`, with `c` the `(1 - α)` quantile of
`χ²₃`. -/
def gevDevianceRegion (K : Set (ℝ × ℝ × ℝ)) (c : ℝ) {n : ℕ} (x : Fin n → ℝ) : Set (ℝ × ℝ × ℝ) :=
  {θ | θ ∈ K ∧ gevMaxLogLik K x ≠ ⊥ ∧ gevMaxLogLik K x ≠ ⊤ ∧
    2 * (gevMaxLogLik K x - gevLogLikE θ.1 θ.2.1 θ.2.2 x) ≤ (c : EReal)}

lemma gevMaxLogLik_eq_of_isMaxOn {K : Set (ℝ × ℝ × ℝ)} {n : ℕ} {x : Fin n → ℝ} {θ : ℝ × ℝ × ℝ}
    (hθ : θ ∈ K) (hmax : IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) K θ) :
    gevMaxLogLik K x = gevLogLikE θ.1 θ.2.1 θ.2.2 x :=
  le_antisymm (iSup₂_le fun _ hp => hmax hp)
    (le_iSup₂ (f := fun (p : ℝ × ℝ × ℝ) (_ : p ∈ K) => gevLogLikE p.1 p.2.1 p.2.2 x) θ hθ)

/-- Where the extended-real GEV log-likelihood is not `-∞`, it equals the real log-likelihood. -/
lemma gevLogLikE_eq_coe_of_ne_bot {ξ μ σ : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (h : gevLogLikE ξ μ σ x ≠ ⊥) :
    gevLogLikE ξ μ σ x = ((∑ i, log (gevLocScaleDensity ξ μ σ (x i)) : ℝ) : EReal) := by
  have hall : ∀ i, gevLogDensityE ξ μ σ (x i) ≠ ⊥ := fun i hi => h <| by
    rw [gevLogLikE, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi, EReal.bot_add]
  have hpos : ∀ i, 0 < gevLocScaleDensity ξ μ σ (x i) := fun i =>
    gevLogDensityE_ne_bot_iff.1 (hall i)
  exact gevLogLikE_eq_coe hpos

/-- Joint measurability of `gevLocScaleDensity` in `((ξ, μ, σ), x)`. -/
lemma measurable_gevLocScaleDensity_joint' :
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
  have hcond1 : MeasurableSet {p : (ℝ × ℝ × ℝ) × ℝ | p.1.1 = 0} :=
    measurableSet_eq_fun hξ measurable_const
  have hcond2 : MeasurableSet {p : (ℝ × ℝ × ℝ) × ℝ | 0 < 1 + p.1.1 * ((p.2 - p.1.2.1) / p.1.2.2)} :=
    measurableSet_lt measurable_const (measurable_const.add (hξ.mul hz))
  have hbr0 : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ =>
      exp (-((p.2 - p.1.2.1) / p.1.2.2)) * exp (-exp (-((p.2 - p.1.2.1) / p.1.2.2))) := by fun_prop
  have hbr1 : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ =>
      (1 + p.1.1 * ((p.2 - p.1.2.1) / p.1.2.2)) ^ (-1 / p.1.1 - 1) *
        exp (-((1 + p.1.1 * ((p.2 - p.1.2.1) / p.1.2.2)) ^ (-1 / p.1.1))) := by fun_prop
  exact hσ.inv.mul (Measurable.ite hcond1 hbr0 (Measurable.ite hcond2 hbr1 measurable_const))

lemma aemeasurable_gevLogLikN {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (hX : ∀ i, AEMeasurable (X i) P) {θ : Ω → ℝ × ℝ × ℝ}
    (hθ : AEMeasurable θ P) (n : ℕ) :
    AEMeasurable (fun ω => gevLogLikN (θ ω).1 (θ ω).2.1 (θ ω).2.2 (fun i => X i ω) n) P := by
  unfold gevLogLikN
  refine Finset.aemeasurable_fun_sum _ fun i _ => ?_
  exact (Real.measurable_log.comp measurable_gevLocScaleDensity_joint').comp_aemeasurable
    (hθ.prodMk (hX i))

end Defs

/-! ### Wilks' theorem for the regular non-Gumbel GEV (`ξ₀ > -1/2`, `ξ₀ ≠ 0`) -/

section NonGumbel

variable {ξ₀ μ₀ σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

private lemma hasDerivAt_gevLine (a τ s : ℝ) : HasDerivAt (fun r => a + r * τ) τ s := by
  simpa using ((hasDerivAt_id s).mul_const τ).const_add a

/-- Continuity of `s ↦ gevEtaM (gevEtaLine ξ₀ Δ s) v Δ Δ` on `[0, 1]` when the segment stays in
the domain. -/
private lemma continuousOn_gevEtaM_line {Δ : ℝ × ℝ × ℝ} {v : ℝ}
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, (gevEtaLine ξ₀ Δ s).1 ≠ 0 ∧ (gevEtaLine ξ₀ Δ s).2.2 ≠ 0 ∧
      gevEtaU (gevEtaLine ξ₀ Δ s) v ≠ 0) :
    ContinuousOn (fun s => gevEtaM (gevEtaLine ξ₀ Δ s) v Δ Δ) (Icc 0 1) := by
  have hc1 : Continuous fun s => (gevEtaLine ξ₀ Δ s).1 := by unfold gevEtaLine; fun_prop
  have hc2 : Continuous fun s => (gevEtaLine ξ₀ Δ s).2.2 := by unfold gevEtaLine; fun_prop
  have hcU : Continuous fun s => gevEtaU (gevEtaLine ξ₀ Δ s) v := by
    unfold gevEtaU gevEtaLine; fun_prop
  have hcLogU : ContinuousOn (fun s => log (gevEtaU (gevEtaLine ξ₀ Δ s) v)) (Icc 0 1) :=
    fun s hs => ((hcU.continuousAt).log (hdom s hs).2.2).continuousWithinAt
  have hcY : ContinuousOn (fun s => gevEtaY (gevEtaLine ξ₀ Δ s) v) (Icc 0 1) := by
    unfold gevEtaY
    exact hcLogU.neg.div hc1.continuousOn fun s hs => (hdom s hs).1
  have hcDY : ContinuousOn (fun s => gevEtaDY (gevEtaLine ξ₀ Δ s) v Δ) (Icc 0 1) := by
    unfold gevEtaDY
    refine ((continuousOn_const.mul hcLogU).div (hc1.pow 2).continuousOn
      fun s hs => pow_ne_zero 2 (hdom s hs).1).sub ?_
    exact continuousOn_const.div (hc1.continuousOn.mul hcU.continuousOn)
      fun s hs => mul_ne_zero (hdom s hs).1 (hdom s hs).2.2
  have hcDDY : ContinuousOn (fun s => gevEtaDDY (gevEtaLine ξ₀ Δ s) v Δ Δ) (Icc 0 1) := by
    unfold gevEtaDDY
    refine (((hc1.continuousOn.mul hcDY).mul hcDY).add
      (((continuousOn_const.mul hcDY).add (continuousOn_const.mul hcDY)).mul
        (hcY.sub (continuousOn_const.div hc1.continuousOn fun s hs => (hdom s hs).1)))).add ?_
    exact (((continuousOn_const.div hc1.continuousOn fun s hs => (hdom s hs).1).mul
      continuousOn_const).mul continuousOn_const).mul (hcY.pow 2)
  have hcExpY : ContinuousOn (fun s => exp (gevEtaY (gevEtaLine ξ₀ Δ s) v)) (Icc 0 1) :=
    continuous_exp.comp_continuousOn hcY
  unfold gevEtaM
  refine (((((continuousOn_const.div (hc2.pow 2).continuousOn fun s hs => pow_ne_zero 2 (hdom s hs).2.1).add
    (continuousOn_const.div (hc1.pow 2).continuousOn fun s hs => pow_ne_zero 2 (hdom s hs).1)).add
    (continuousOn_const.mul hcDY)).add (continuousOn_const.mul hcDY)).sub
    ((hcExpY.mul hcDY).mul hcDY)).add ?_
  exact ((continuousOn_const.add hc1.continuousOn).sub hcExpY).mul hcDDY

/-- Deterministic second-order deviance expansion along a path in the coordinates `η`. -/
private lemma gevPath_deviance_bound (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) {ε K : ℝ}
    (hdev : GevEtaDev ξ₀ ε K) {x : ℕ → ℝ} (hx : ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (x i))
    {θh : ℕ → ℝ × ℝ × ℝ} (hc : Tendsto θh atTop (𝓝 (ξ₀, μ₀, σ₀)))
    (hM : ∀ j k, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        gevEtaM (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ (x i)) (gevEtaBasis j) (gevEtaBasis k)) atTop
      (𝓝 (-gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k))))
    {t : ℕ → ℝ} (hT : ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (gevU ξ₀ μ₀ σ₀ (x i))) atTop (𝓝 (t k)))
    (ht : Tendsto t atTop (𝓝 0)) {e' : ℝ} (he' : 0 < e') :
    ∀ᶠ n : ℕ in atTop,
      gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) *
        (1 + runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (x i)) n) < 1 / 2 →
      |2 * (gevLogLikN (θh n).1 (θh n).2.1 (θh n).2.2 x n - gevLogLikN ξ₀ μ₀ σ₀ x n) -
        (2 * ((fun j => √(n : ℝ) * gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) j) ⬝ᵥ
            gevPathZ ξ₀ μ₀ σ₀ x n) -
          (fun j => √(n : ℝ) * gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) j) ⬝ᵥ
            gevFisherInfo ξ₀ σ₀ *ᵥ
              (fun j => √(n : ℝ) * gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n)) j))| ≤
        e' * (√(n : ℝ) * gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n))) ^ 2 := by
  set η₀ : ℝ × ℝ × ℝ := (ξ₀, 0, 1)
  set Δ : ℕ → ℝ × ℝ × ℝ := fun n => gevEtaIncr ξ₀ μ₀ σ₀ (θh n)
  have hadd : ∀ n, η₀ + Δ n = gevEtaOf ξ₀ μ₀ σ₀ (θh n) := fun n => add_sub_cancel _ _
  have hcη : ContinuousAt (gevEtaOf ξ₀ μ₀ σ₀) (ξ₀, μ₀, σ₀) := by
    have hσ : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) (ξ₀, μ₀, σ₀) := by fun_prop
    have hμ : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.1) (ξ₀, μ₀, σ₀) := by fun_prop
    have hξ : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1) (ξ₀, μ₀, σ₀) := by fun_prop
    have h1 : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1 * σ₀ / (ξ₀ * p.2.2)) (ξ₀, μ₀, σ₀) :=
      (hξ.mul continuousAt_const).div (continuousAt_const.mul hσ) (mul_ne_zero hξ₀0 hσ₀.ne')
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
    rwa [h3] at h2
  have hbox : ∀ᶠ n in atTop, η₀ + Δ n ∈ gevEtaBox ξ₀ := by
    filter_upwards [hη.eventually (gevEtaBox_mem_nhds hξ₀0)] with n hn; rwa [hadd]
  have hσ₁ : ∀ᶠ n in atTop, 0 < (θh n).2.2 :=
    (((continuous_snd.comp continuous_snd).tendsto (ξ₀, μ₀, σ₀)).comp hc).eventually (lt_mem_nhds hσ₀)
  obtain ⟨δ, hδ, hdev_ev⟩ := gevPath_dev (σ₀ := σ₀) hdev hx hM hT ht he'
  filter_upwards [hdev_ev, (hN0.eventually (gt_mem_nhds hδ)), hbox, hσ₁,
    eventually_gt_atTop 0] with n hdevn hNδ hboxn hσn hn0 hr
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn0
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
  have hsq2 : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn'.le
  -- Every observation `i < n` is good all along `[0, 1]`
  have hgood : ∀ i < n, ∀ s ∈ Icc (0 : ℝ) 1,
      gevU ξ₀ μ₀ σ₀ (x i) / 2 ≤ gevEtaU (gevEtaLine ξ₀ (Δ n) s) (gevU ξ₀ μ₀ σ₀ (x i)) ∧
      gevEtaU (gevEtaLine ξ₀ (Δ n) s) (gevU ξ₀ μ₀ σ₀ (x i)) ≤ 2 * gevU ξ₀ μ₀ σ₀ (x i) := fun i hi s hs => by
    refine gevEtaU_gevEtaLine_good (Δ n) hs (hx i) ?_
    have hrm : 1 / gevU ξ₀ μ₀ σ₀ (x i) ≤ runMax (fun j => 1 / gevU ξ₀ μ₀ σ₀ (x j)) n :=
      le_runMax (fun j => 1 / gevU ξ₀ μ₀ σ₀ (x j)) hi
    have hle : gevEtaNorm (Δ n) * (1 + 1 / gevU ξ₀ μ₀ σ₀ (x i)) ≤
        gevEtaNorm (Δ n) * (1 + runMax (fun j => 1 / gevU ξ₀ μ₀ σ₀ (x j)) n) :=
      mul_le_mul_of_nonneg_left (by linarith) (gevEtaNorm_nonneg _)
    linarith
  have hdom : ∀ s ∈ Icc (0 : ℝ) 1, gevEtaLine ξ₀ (Δ n) s ∈ gevEtaBox ξ₀ ∧
      (gevEtaLine ξ₀ (Δ n) s).1 ≠ 0 ∧ (gevEtaLine ξ₀ (Δ n) s).2.2 ≠ 0 ∧
      ∀ i < n, 0 < gevEtaU (gevEtaLine ξ₀ (Δ n) s) (gevU ξ₀ μ₀ σ₀ (x i)) := fun s hs => by
    have hmem := gevEtaLine_mem_gevEtaBox hboxn hs
    obtain ⟨-, -, -, h1, -, -, h2, -⟩ := bounds_of_mem_gevEtaBox hξ₀0 hmem
    refine ⟨hmem, h1, by linarith, fun i hi => by linarith [(hgood i hi s hs).1, hx i]⟩
  -- Rewrite log-likelihoods at `s = 0` and `s = 1` in `η` coordinates
  obtain ⟨-, -, -, hξn, hdivn, -, hκn, -⟩ := bounds_of_mem_gevEtaBox hξ₀0 hboxn
  have hθ_eq : gevThetaOf ξ₀ μ₀ σ₀ (η₀ + Δ n) = θh n := by
    rw [hadd]
    exact gevThetaOf_gevEtaOf hξ₀0 hσ₀.ne' (by rwa [hadd] at hξn) hσn.ne'
  set f : ℝ → ℝ := fun s => ∑ i ∈ Finset.range n,
    gevEtaLog ξ₀ σ₀ (gevEtaLine ξ₀ (Δ n) s) (gevU ξ₀ μ₀ σ₀ (x i))
  set f' : ℝ → ℝ := fun s => ∑ i ∈ Finset.range n,
    gevEtaD (gevEtaLine ξ₀ (Δ n) s) (gevU ξ₀ μ₀ σ₀ (x i)) (Δ n)
  set f'' : ℝ → ℝ := fun s => ∑ i ∈ Finset.range n,
    gevEtaM (gevEtaLine ξ₀ (Δ n) s) (gevU ξ₀ μ₀ σ₀ (x i)) (Δ n) (Δ n)
  have hf0 : f 0 = gevLogLikN ξ₀ μ₀ σ₀ x n := by
    simp only [f, gevEtaLine_zero, gevLogLikN]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 := log_gevLocScaleDensity_gevThetaOf (μ₀ := μ₀) hξ₀0 hσ₀ (η := (ξ₀, 0, 1)) (x := x i)
      (by rw [div_self hξ₀0]; norm_num) one_pos (by simpa using hx i)
    have hθ0 : gevThetaOf ξ₀ μ₀ σ₀ (ξ₀, 0, 1) = (ξ₀, μ₀, σ₀) := by
      rw [← gevEtaOf_self (μ₀ := μ₀) hξ₀0 hσ₀.ne']
      exact gevThetaOf_gevEtaOf hξ₀0 hσ₀.ne' hξ₀0 hσ₀.ne'
    rw [hθ0] at h0
    exact h0.symm
  have hf1 : f 1 = gevLogLikN (θh n).1 (θh n).2.1 (θh n).2.2 x n := by
    simp only [f, gevEtaLine_one, gevLogLikN]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hui : 0 < gevEtaU (η₀ + Δ n) (gevU ξ₀ μ₀ σ₀ (x i)) := by
      simpa [gevEtaLine_one] using (hdom 1 ⟨zero_le_one, le_rfl⟩).2.2.2 i (Finset.mem_range.1 hi)
    have h1 := log_gevLocScaleDensity_gevThetaOf (μ₀ := μ₀) hξ₀0 hσ₀ hdivn (by linarith) hui
    rw [hθ_eq] at h1
    exact h1.symm
  have hdf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' s) s := fun s hs => by
    refine HasDerivAt.fun_sum fun i hi => ?_
    exact hasDerivAt_gevEtaLog hξ₀0 (hasDerivAt_gevLine _ _ s) (hasDerivAt_gevLine _ _ s)
      (hasDerivAt_gevLine _ _ s) (hdom s hs).2.1 (hdom s hs).2.2.1
      ((hdom s hs).2.2.2 i (Finset.mem_range.1 hi)).ne'
  have hdf' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' s) s := fun s hs => by
    refine HasDerivAt.fun_sum fun i hi => ?_
    exact hasDerivAt_gevEtaD (Δ n) (hasDerivAt_gevLine _ _ s) (hasDerivAt_gevLine _ _ s)
      (hasDerivAt_gevLine _ _ s) (hdom s hs).2.1 (hdom s hs).2.2.1
      ((hdom s hs).2.2.2 i (Finset.mem_range.1 hi)).ne'
  have hcont : ContinuousOn f'' (Icc 0 1) :=
    continuousOn_finsetSum _ fun i hi => continuousOn_gevEtaM_line fun s hs =>
      ⟨(hdom s hs).2.1, (hdom s hs).2.2.1, ((hdom s hs).2.2.2 i (Finset.mem_range.1 hi)).ne'⟩
  have htaylor := two_mul_sub_eq_taylor_segW
    (fun s hs => hdf s (uIcc_of_le (zero_le_one (α := ℝ)) ▸ hs))
    (fun s hs => hdf' s (uIcc_of_le (zero_le_one (α := ℝ)) ▸ hs))
    (uIcc_of_le (zero_le_one (α := ℝ)) ▸ hcont)
  rw [hf1, hf0] at htaylor
  -- Evaluate `f' 0` as `Uₙ · Zₙ`
  set U : Fin 3 → ℝ := fun j => √(n : ℝ) * gevEtaJ ξ₀ σ₀ (Δ n) j
  have hf'0 : f' 0 = U ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n := by
    simp only [f', gevEtaLine_zero]
    have hsum : ∑ i ∈ Finset.range n, gevEtaD (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ (x i)) (Δ n) =
        ∑ i ∈ Finset.range n, gevEtaJ ξ₀ σ₀ (Δ n) ⬝ᵥ gevScore ξ₀ μ₀ σ₀ (x i) :=
      Finset.sum_congr rfl fun i _ => gevEtaD_self_eq hξ₀0 hσ₀.ne' (hx i) (Δ n)
    rw [hsum, show U = √(n : ℝ) • gevEtaJ ξ₀ σ₀ (Δ n) from rfl, smul_dotProduct,
      dotProduct_gevPathZ, smul_eq_mul, mul_inv_cancel_left₀ hsq.ne']
  -- Evaluate `-Uᵀ I U` as `∫₀¹ 2 (1 - s) (-n · gevEtaInfo (Δ n) (Δ n)) ds`
  have hquad : U ⬝ᵥ gevFisherInfo ξ₀ σ₀ *ᵥ U = (n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n) := by
    have hU : U = √(n : ℝ) • gevEtaJ ξ₀ σ₀ (Δ n) := rfl
    rw [hU, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hsq2, gevEtaInfo]
  have hconst_int : -(U ⬝ᵥ gevFisherInfo ξ₀ σ₀ *ᵥ U) =
      ∫ s in (0 : ℝ)..1, 2 * (1 - s) * (-(n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n)) := by
    rw [intervalIntegral.integral_mul_const, integral_two_mul_one_sub, one_mul, hquad]; ring
  have hint1 : IntervalIntegrable (fun s => 2 * (1 - s) * f'' s) volume 0 1 := by
    have hc : ContinuousOn (fun s => 2 * (1 - s) * f'' s) (Icc 0 1) :=
      (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).mul hcont
    exact hc.intervalIntegrable_of_Icc zero_le_one
  have hint2 : IntervalIntegrable
      (fun s => 2 * (1 - s) * (-(n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n))) volume 0 1 :=
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  have hsub_eq : 2 * (gevLogLikN (θh n).1 (θh n).2.1 (θh n).2.2 x n - gevLogLikN ξ₀ μ₀ σ₀ x n) -
      (2 * (U ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n) - U ⬝ᵥ gevFisherInfo ξ₀ σ₀ *ᵥ U) =
      ∫ s in (0 : ℝ)..1, 2 * (1 - s) * (f'' s + (n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n)) := by
    rw [htaylor, hf'0]
    have h1 : 2 * (U ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n) + (∫ s in (0 : ℝ)..1, 2 * (1 - s) * f'' s) -
        (2 * (U ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ x n) - U ⬝ᵥ gevFisherInfo ξ₀ σ₀ *ᵥ U) =
        (∫ s in (0 : ℝ)..1, 2 * (1 - s) * f'' s) -
        (∫ s in (0 : ℝ)..1, 2 * (1 - s) * (-(n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n))) := by
      rw [← hconst_int]; ring
    rw [h1, ← intervalIntegral.integral_sub hint1 hint2]
    refine intervalIntegral.integral_congr fun s _ => by ring
  rw [hsub_eq]
  -- Pointwise bound along `s ∈ [0, 1]` from `gevPath_dev`
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1,
      |f'' s + (n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n)| ≤
        e' * (√(n : ℝ) * gevEtaNorm (Δ n)) ^ 2 := fun s hs => by
    have hbd := (hdevn _ (hdom s hs).1 ((gevEtaNorm_gevEtaLine_sub_le (Δ n) hs).trans hNδ.le)).2
      (fun i hi => hgood i hi s hs) (Δ n) (Δ n)
    have hmul := mul_le_mul_of_nonneg_left hbd hn'.le
    have hlhs : (n : ℝ) * |(n : ℝ)⁻¹ * f'' s + gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n)| =
        |f'' s + (n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n)| := by
      rw [show (n : ℝ) * |(n : ℝ)⁻¹ * f'' s + gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n)| =
          |(n : ℝ) * ((n : ℝ)⁻¹ * f'' s + gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n))| by
          rw [abs_mul, abs_of_pos hn'], mul_add, mul_inv_cancel_left₀ hn'.ne']
    rw [hlhs] at hmul
    refine hmul.trans (le_of_eq ?_)
    rw [mul_pow, Real.sq_sqrt hn'.le]; ring
  have hle_abs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) zero_le_one
    (f := fun s => 2 * (1 - s) * (f'' s + (n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n)))
  refine hle_abs.trans ?_
  have hint_abs : IntervalIntegrable
      (fun s => |2 * (1 - s) * (f'' s + (n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n))|) volume 0 1 := by
    have hc : ContinuousOn (fun s => |2 * (1 - s) * (f'' s + (n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n))|)
        (Icc 0 1) :=
      continuous_abs.comp_continuousOn
        ((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).mul
          (hcont.add continuousOn_const))
    exact hc.intervalIntegrable_of_Icc zero_le_one
  have hint_rhs : IntervalIntegrable
      (fun s => 2 * (1 - s) * (e' * (√(n : ℝ) * gevEtaNorm (Δ n)) ^ 2)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) 0 1
  have hmono : (∫ s in (0 : ℝ)..1,
        |2 * (1 - s) * (f'' s + (n : ℝ) * gevEtaInfo ξ₀ σ₀ (Δ n) (Δ n))|) ≤
      ∫ s in (0 : ℝ)..1, 2 * (1 - s) * (e' * (√(n : ℝ) * gevEtaNorm (Δ n)) ^ 2) := by
    refine intervalIntegral.integral_mono_on zero_le_one hint_abs hint_rhs fun s hs => ?_
    rw [abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 2 * (1 - s))]
    exact mul_le_mul_of_nonneg_left (hpt s hs) (by linarith [hs.2])
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const, integral_two_mul_one_sub, one_mul]

/-- **Stochastic expansion of the GEV deviance** (`ξ₀ > -1/2`, `ξ₀ ≠ 0`):
for consistent local maximizers `θ̂ₙ`, `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - Zₙᵀ I(θ₀)⁻¹ Zₙ → 0` in probability. -/
theorem tendstoInMeasure_gevLocalDeviance_sub (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, μ₀, σ₀)))
    (hloc : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      0 < gevU (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (X i ω)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω =>
        2 * (gevLogLikN (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (fun i => X i ω) n -
          gevLogLikN ξ₀ μ₀ σ₀ (fun i => X i ω) n) -
        gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n ⬝ᵥ
          (gevFisherInfo ξ₀ σ₀)⁻¹ *ᵥ gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n)
      atTop (fun _ => 0) := by
  set I := gevFisherInfo ξ₀ σ₀
  set A := I⁻¹
  have hIinv : I * A = 1 := mul_inv_gevFisherInfo hσ₀ hξ₀0 hξ₀
  have hIsym : Iᵀ = I := gevFisherInfo_isSymm.eq
  have hAsym : Aᵀ = A := transpose_inv_gevFisherInfo ξ₀ σ₀
  obtain ⟨ε, hε, ha, hb⟩ := exists_gevEnvM_integrable hξ₀ hξ₀0
  obtain ⟨K, hK0, hdev⟩ := exists_gevEtaM_dev_le hξ₀ hξ₀0 hε
  obtain ⟨lam, hlam0, hlam⟩ := exists_gevEtaInfo_ge hσ₀ hξ₀0 hξ₀
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (X i ω) := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gevU_pos hξ₀0 hσ₀)
  have hM : ∀ᵐ ω ∂P, ∀ j k, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gevEtaM (ξ₀, 0, 1) (gevU ξ₀ μ₀ σ₀ (X i ω)) (gevEtaBasis j) (gevEtaBasis k)) atTop
      (𝓝 (-gevEtaInfo ξ₀ σ₀ (gevEtaBasis j) (gevEtaBasis k))) := by
    refine ae_all_iff.2 fun j => ae_all_iff.2 fun k => ?_
    have h := ae_tendsto_avg_comp hX hind (measurable_gevEtaM_self ξ₀ μ₀ σ₀ _ _)
      (integrable_gevEtaM_self hσ₀ hξ₀0 hξ₀ (gevEtaBasis j) (gevEtaBasis k))
    rwa [integral_gevEtaM_self hσ₀ hξ₀0 hξ₀] at h
  have hT : ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (gevU ξ₀ μ₀ σ₀ (X i ω))) atTop
      (𝓝 (∫ x, gevEtaTail ξ₀ ε K (1 / ((k : ℝ) + 1)) (gevU ξ₀ μ₀ σ₀ x)
        ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure)) :=
    ae_all_iff.2 fun k => ae_tendsto_avg_comp hX hind (measurable_gevEtaTail_gevU ξ₀ ε K _ μ₀ σ₀)
      (integrable_gevEtaTail hξ₀0 hσ₀ hε hK0 ha hb _)
  have ht := tendsto_integral_gevEtaTail (μ₀ := μ₀) hξ₀0 hσ₀ hε hK0 ha hb
  -- Rate `√n * |Δₙ| ≤ C₂ * Z1` and `rₙ = |Δₙ| * (1 + Mₙ) → 0` in probability
  set C₂ := 2 * gevJBound ξ₀ σ₀ / lam
  have hC₂0 : 0 ≤ C₂ := by unfold C₂ gevJBound; positivity
  set Z1 : ℕ → Ω → ℝ := fun n ω => gevPathZNorm ξ₀ μ₀ σ₀ (fun i => X i ω) n
  have hZm := fun n => aemeasurable_gevPathZNorm (ξ₀ := ξ₀) (μ₀ := μ₀) (σ₀ := σ₀) hXm n
  have hZb := isBoundedInProbability_gevPathZNorm hξ₀ hξ₀0 hσ₀ hX hind
  have hZ0 : ∀ n ω, 0 ≤ Z1 n ω := fun n ω => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set N : ℕ → Ω → ℝ := fun n ω => gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω))
  have hNm : ∀ n, AEMeasurable (N n) P := fun n => by
    have h : Measurable fun θ : ℝ × ℝ × ℝ => gevEtaNorm (gevEtaIncr ξ₀ μ₀ σ₀ θ) := by
      simp only [gevEtaNorm, gevEtaIncr, gevEtaOf, Prod.fst_sub, Prod.snd_sub]; fun_prop
    exact h.comp_aemeasurable (hθm n)
  set M : ℕ → Ω → ℝ := fun n ω => runMax (fun i => 1 / gevU ξ₀ μ₀ σ₀ (X i ω)) n
  have hMm : ∀ n, AEMeasurable (M n) P := fun n =>
    aemeasurable_runMax (fun i => (measurable_const.div (measurable_gevU ξ₀ μ₀ σ₀)).comp_aemeasurable
      (hXm i)) n
  set r : ℕ → Ω → ℝ := fun n ω => N n ω * (1 + M n ω)
  have hrm : ∀ n, AEMeasurable (r n) P := fun n => (hNm n).mul (aemeasurable_const.add (hMm n))
  have hrate : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, √(n : ℝ) * N n ω ≤ C₂ * Z1 n ω := by
    filter_upwards [hsupp, hcons, hloc, hadm, hM, hT] with ω h1 h2 h3 h4 h5 h6
    exact (gevPath_estimates (μ₀ := μ₀) hξ₀0 hσ₀ hdev hlam0 hlam hIinv
      (x := fun i => X i ω) (θh := fun n => θh n ω) h1 h2 h3 h4 h5 h6 ht).1
  have hr : TendstoInMeasure P r atTop (fun _ => 0) := by
    have hY := tendstoInMeasure_one_add_runMax_gevU_div_sqrt (μ₀ := μ₀) hξ₀ hξ₀0 hσ₀ hX
    have hprod := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hZb hY
    have hg : TendstoInMeasure P (fun n ω => C₂ * ((1 + M n ω) / √(n : ℝ) * Z1 n ω)) atTop
        (fun _ => 0) := by
      simpa only [mul_zero] using tendstoInMeasure_comp hprod (φ := fun z => C₂ * z) (by fun_prop)
    refine tendstoInMeasure_zero_of_ae_eventually_abs_le
      (fun n => (hrm n).aestronglyMeasurable) (fun n => ?_) ?_ hg
    · exact (aemeasurable_const.mul ((aemeasurable_const.add (hMm n)).div_const _ |>.mul
        (hZm n))).aestronglyMeasurable
    · filter_upwards [hrate] with ω hω
      filter_upwards [hω, eventually_gt_atTop 0] with n hn hn0
      have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn0)
      have hM0 : 0 ≤ M n ω := runMax_nonneg _ _
      have hN0 : 0 ≤ N n ω := gevEtaNorm_nonneg _
      rw [abs_of_nonneg (by positivity)]
      have e : r n ω = √(n : ℝ) * N n ω * ((1 + M n ω) / √(n : ℝ)) := by simp only [r]; field_simp
      rw [e]
      calc √(n : ℝ) * N n ω * ((1 + M n ω) / √(n : ℝ))
          ≤ C₂ * Z1 n ω * ((1 + M n ω) / √(n : ℝ)) := mul_le_mul_of_nonneg_right hn (by positivity)
        _ = _ := by ring
  -- Part 1: `R₁(n, ω) = 2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - (2 (Uₙ · Zₙ) - Uₙᵀ I Uₙ) → 0` in probability
  set U : ℕ → Ω → Fin 3 → ℝ := fun n ω j =>
    √(n : ℝ) * gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) j
  set Z : ℕ → Ω → Fin 3 → ℝ := fun n ω => gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n
  set R₁ : ℕ → Ω → ℝ := fun n ω =>
    2 * (gevLogLikN (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (fun i => X i ω) n -
      gevLogLikN ξ₀ μ₀ σ₀ (fun i => X i ω) n) -
    (2 * (U n ω ⬝ᵥ Z n ω) - U n ω ⬝ᵥ I *ᵥ U n ω)
  have hUm : ∀ n j, AEMeasurable (fun ω => U n ω j) P := fun n j => by
    have hm : Measurable fun θ : ℝ × ℝ × ℝ => gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ θ) j := by
      fin_cases j
      · simp only [gevEtaJ, gevEtaIncr, gevEtaOf, Prod.fst_sub, Prod.snd_sub]; fun_prop
      · simp only [gevEtaJ, gevEtaIncr, gevEtaOf, Prod.fst_sub, Prod.snd_sub]; fun_prop
      · simp only [gevEtaJ, gevEtaIncr, gevEtaOf, Prod.fst_sub, Prod.snd_sub]; fun_prop
    exact (hm.comp_aemeasurable (hθm n)).const_mul _
  have hR₁m : ∀ n, AEMeasurable (R₁ n) P := fun n => by
    have hL1 := aemeasurable_gevLogLikN hXm (hθm n) n
    have hL0 := aemeasurable_gevLogLikN hXm (θ := fun _ => (ξ₀, μ₀, σ₀)) aemeasurable_const n
    have hUZ : AEMeasurable (fun ω => U n ω ⬝ᵥ Z n ω) P :=
      Finset.aemeasurable_fun_sum _ fun j _ => (hUm n j).mul (aemeasurable_gevPathZ hXm n j)
    have hUIU : AEMeasurable (fun ω => U n ω ⬝ᵥ I *ᵥ U n ω) P := by
      simp only [dotProduct, Matrix.mulVec]
      exact Finset.aemeasurable_fun_sum _ fun i _ => (hUm n i).mul
        (Finset.aemeasurable_fun_sum _ fun j _ => (hUm n j).const_mul _)
    exact ((hL1.sub hL0).const_mul 2).sub ((hUZ.const_mul 2).sub hUIU)
  have hZ1sq_bd : IsBoundedInProbability P (fun n ω => (1 + Z1 n ω) ^ 2) := by
    intro δ hδ
    obtain ⟨B, hB⟩ := hZb δ hδ
    refine ⟨(1 + max B 0) ^ 2, hB.mono fun n hn => (measure_mono fun ω hω => ?_).trans hn⟩
    simp only [mem_ofPred_eq] at hω ⊢
    rw [abs_of_nonneg (sq_nonneg _)] at hω
    by_contra hle; push Not at hle
    have h1 : 1 + Z1 n ω ≤ 1 + max B 0 := by
      have : Z1 n ω ≤ B := by simpa [Z1, abs_of_nonneg (hZ0 n ω)] using hle
      linarith [le_max_left B 0]
    have h2 : (1 + Z1 n ω) ^ 2 ≤ (1 + max B 0) ^ 2 := pow_le_pow_left₀ (by linarith [hZ0 n ω]) h1 2
    linarith
  have hR₁_lim : TendstoInMeasure P R₁ atTop (fun _ => 0) := by
    set Q₁ : ℕ → Ω → ℝ := fun n ω => |R₁ n ω| / (1 + Z1 n ω) ^ 2
    have hQ₁m : ∀ n, AEMeasurable (Q₁ n) P := fun n =>
      (hR₁m n).abs.div ((aemeasurable_const.add (hZm n)).pow_const 2)
    have hQ₁_cut : TendstoInMeasure P (fun n ω => Q₁ n ω * cutoff (r n ω)) atTop (fun _ => 0) :=
      tendstoInMeasure_mul_cutoff Q₁ hr
    have hQ₁_good : TendstoInMeasure P (fun n ω => Q₁ n ω * (1 - cutoff (r n ω))) atTop (fun _ => 0) := by
      refine tendstoInMeasure_of_tendsto_ae (fun n => ((hQ₁m n).mul (aemeasurable_const.sub
        (continuous_cutoff.measurable.comp_aemeasurable (hrm n)))).aestronglyMeasurable) ?_
      have hdev_rat : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
          r n ω < 1 / 2 → |R₁ n ω| ≤ (1 / ((k : ℝ) + 1)) * (√(n : ℝ) * N n ω) ^ 2 := by
        refine ae_all_iff.2 fun k => ?_
        filter_upwards [hsupp, hcons, hM, hT] with ω h1 h2 h5 h6
        exact gevPath_deviance_bound hξ₀0 hσ₀ hdev h1 h2 h5 h6 ht (by positivity)
      filter_upwards [hrate, hdev_rat] with ω hrateω hdevω
      refine Metric.tendsto_nhds.2 fun η hη => ?_
      obtain ⟨k, hk⟩ : ∃ k : ℕ, C₂ ^ 2 / ((k : ℝ) + 1) < η := by
        obtain ⟨k, hk⟩ := exists_nat_gt (C₂ ^ 2 / η)
        refine ⟨k, ?_⟩
        rw [div_lt_iff₀ (by positivity)]
        have : C₂ ^ 2 < η * (k : ℝ) := by rwa [div_lt_iff₀ hη, mul_comm] at hk
        nlinarith
      filter_upwards [hrateω, hdevω k] with n hrt hd
      rw [Real.dist_eq, sub_zero]
      have h1Z : 0 < 1 + Z1 n ω := by linarith [hZ0 n ω]
      have hden : 0 < (1 + Z1 n ω) ^ 2 := sq_pos_of_pos h1Z
      have hQ0 : 0 ≤ Q₁ n ω := div_nonneg (abs_nonneg _) hden.le
      by_cases hcut : cutoff (r n ω) = 1
      · rw [hcut, sub_self, mul_zero, abs_zero]; exact hη
      · have hr' : r n ω < 1 / 2 := by
          by_contra h; exact hcut (cutoff_of_ge (not_lt.1 h))
        have h1 := hd hr'
        have h2 : (√(n : ℝ) * N n ω) ^ 2 ≤ (C₂ * Z1 n ω) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (gevEtaNorm_nonneg _)) hrt 2
        have h3 : (Z1 n ω) ^ 2 ≤ (1 + Z1 n ω) ^ 2 :=
          pow_le_pow_left₀ (hZ0 n ω) (by linarith) 2
        have hQle : Q₁ n ω ≤ C₂ ^ 2 / ((k : ℝ) + 1) := by
          rw [show Q₁ n ω = |R₁ n ω| / (1 + Z1 n ω) ^ 2 from rfl, div_le_iff₀ hden]
          calc |R₁ n ω|
              ≤ (1 / ((k : ℝ) + 1)) * (√(n : ℝ) * N n ω) ^ 2 := h1
            _ ≤ (1 / ((k : ℝ) + 1)) * (C₂ * Z1 n ω) ^ 2 :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = (C₂ ^ 2 / ((k : ℝ) + 1)) * (Z1 n ω) ^ 2 := by ring
            _ ≤ (C₂ ^ 2 / ((k : ℝ) + 1)) * (1 + Z1 n ω) ^ 2 :=
                  mul_le_mul_of_nonneg_left h3 (by positivity)
        have hc0 : 0 ≤ cutoff (r n ω) := cutoff_nonneg _
        have hc1 : cutoff (r n ω) ≤ 1 := min_le_left _ _
        rw [abs_mul, abs_of_nonneg hQ0, abs_of_nonneg (by linarith)]
        calc Q₁ n ω * (1 - cutoff (r n ω)) ≤ (C₂ ^ 2 / ((k : ℝ) + 1)) * 1 :=
              mul_le_mul hQle (by linarith) (by linarith) (by positivity)
          _ < η := by linarith
    have hQ₁_lim : TendstoInMeasure P Q₁ atTop (fun _ => 0) := by
      have := tendstoInMeasure_add_zero hQ₁_cut hQ₁_good
      refine this.congr_left fun n => ae_of_all _ fun ω => by ring
    have hR₁_abs := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hZ1sq_bd hQ₁_lim
    refine tendstoInMeasure_zero_of_abs_le (fun n ω => ?_) hR₁_abs
    have hden : (1 + Z1 n ω) ^ 2 ≠ 0 := (sq_pos_of_pos (by linarith [hZ0 n ω])).ne'
    have heq : Q₁ n ω * (1 + Z1 n ω) ^ 2 = |R₁ n ω| := by simp only [Q₁]; exact div_mul_cancel₀ _ hden
    rw [heq]
  -- Part 2: `Uₙ - A *ᵥ Zₙ → 0` entrywise in probability, hence `(Uₙ - A Zₙ)ᵀ I (Uₙ - A Zₙ) → 0`
  have hlin := tendstoInMeasure_gevLinErr hξ₀ hξ₀0 hσ₀ hX hind hθm hcons hloc hadm
  have hN_ae : ∀ᵐ ω ∂P, Tendsto (fun n => N n ω) atTop (𝓝 0) := by
    have hcη : ContinuousAt (gevEtaOf ξ₀ μ₀ σ₀) (ξ₀, μ₀, σ₀) := by
      have hσ : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) (ξ₀, μ₀, σ₀) := by fun_prop
      have hμ : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.1) (ξ₀, μ₀, σ₀) := by fun_prop
      have hξ : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1) (ξ₀, μ₀, σ₀) := by fun_prop
      have h1 : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1 * σ₀ / (ξ₀ * p.2.2)) (ξ₀, μ₀, σ₀) :=
        (hξ.mul continuousAt_const).div (continuousAt_const.mul hσ) (mul_ne_zero hξ₀0 hσ₀.ne')
      unfold gevEtaOf
      exact hξ.prodMk (((continuousAt_const.sub h1).add
        ((hξ.div hσ hσ₀.ne').mul (continuousAt_const.sub hμ))).prodMk h1)
    have hcN : Continuous gevEtaNorm := by unfold gevEtaNorm; fun_prop
    filter_upwards [hcons] with ω hω
    have hη : Tendsto (fun n => gevEtaOf ξ₀ μ₀ σ₀ (θh n ω)) atTop (𝓝 (ξ₀, 0, 1)) := by
      have h := hcη.tendsto.comp hω
      rwa [gevEtaOf_self hξ₀0 hσ₀.ne'] at h
    have h1 : Tendsto (fun n => gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) atTop (𝓝 0) := by
      simpa [gevEtaIncr] using hη.sub_const (ξ₀, 0, 1)
    have h2 := (hcN.tendsto 0).comp h1
    have h3 : gevEtaNorm 0 = 0 := by simp [gevEtaNorm]
    rw [h3] at h2
    exact h2
  have hN_meas : TendstoInMeasure P N atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hNm n).aestronglyMeasurable) hN_ae
  have hsqN_bd : TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) * N n ω ^ 2) atTop (fun _ => 0) := by
    have hprod := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hZb hN_meas
    have hg : TendstoInMeasure P (fun (n : ℕ) ω => C₂ * (Z1 n ω * N n ω)) atTop (fun _ => 0) := by
      have := tendstoInMeasure_comp hprod (φ := fun z => C₂ * z) (by fun_prop)
      simp only [mul_zero] at this
      refine this.congr_left fun n => ae_of_all _ fun ω => by simp only [Z1]; ring
    refine tendstoInMeasure_zero_of_ae_eventually_abs_le
      (fun n => ((hNm n).pow_const 2 |>.const_mul _).aestronglyMeasurable)
      (fun n => (((hZm n).mul (hNm n)).const_mul _).aestronglyMeasurable) ?_ hg
    filter_upwards [hrate] with ω hω
    filter_upwards [hω] with n hn
    rw [abs_of_nonneg (by positivity)]
    calc √(n : ℝ) * N n ω ^ 2 = (√(n : ℝ) * N n ω) * N n ω := by ring
      _ ≤ (C₂ * Z1 n ω) * N n ω := mul_le_mul_of_nonneg_right hn (gevEtaNorm_nonneg _)
      _ = C₂ * (Z1 n ω * N n ω) := by ring
  obtain ⟨Cθ, hCθ0, hCθ⟩ := exists_abs_gevThetaOf_sub_sub_le (μ₀ := μ₀) (σ₀ := σ₀) hξ₀0
  have hUdiff : ∀ j : Fin 3,
      TendstoInMeasure P (fun (n : ℕ) ω => U n ω j - (A *ᵥ Z n ω) j) atTop (fun _ => 0) := fun j => by
    have h1 : TendstoInMeasure P (fun (n : ℕ) ω =>
        Cθ * (√(n : ℝ) * N n ω ^ 2) + gevLinErr ξ₀ μ₀ σ₀ A (fun i => X i ω) (θh n ω) n)
        atTop (fun _ => 0) := by
      have hc : TendstoInMeasure P (fun (n : ℕ) ω => Cθ * (√(n : ℝ) * N n ω ^ 2)) atTop (fun _ => 0) := by
        simpa only [mul_zero] using tendstoInMeasure_comp hsqN_bd (φ := fun z => Cθ * z) (by fun_prop)
      exact tendstoInMeasure_add_zero hc hlin
    have hdiff_m : ∀ n : ℕ, AEMeasurable (fun ω => U n ω j - (A *ᵥ Z n ω) j) P := fun n => by
      simp only [Matrix.mulVec, dotProduct]
      exact (hUm n j).sub (Finset.aemeasurable_fun_sum _ fun k _ => (aemeasurable_gevPathZ hXm n k).const_mul _)
    have hbd_m : ∀ n : ℕ, AEMeasurable (fun ω =>
        Cθ * (√(n : ℝ) * N n ω ^ 2) + gevLinErr ξ₀ μ₀ σ₀ A (fun i => X i ω) (θh n ω) n) P := fun n => by
      have hG : AEMeasurable (fun ω => gevLinErr ξ₀ μ₀ σ₀ A (fun i => X i ω) (θh n ω) n) P := by
        have hd : ∀ k, AEMeasurable (fun ω => gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) k) P := fun k => by
          fin_cases k
          · exact (measurable_snd.fst.comp_aemeasurable (hθm n)).sub_const _
          · exact (measurable_snd.snd.comp_aemeasurable (hθm n)).sub_const _
          · exact (measurable_fst.comp_aemeasurable (hθm n)).sub_const _
        exact Finset.aemeasurable_fun_sum _ fun k _ =>
          (((hd k).const_mul _).sub (Finset.aemeasurable_fun_sum _ fun l _ =>
            (aemeasurable_gevPathZ hXm n l).const_mul _)).abs
      exact (((hNm n).pow_const 2 |>.const_mul _).const_mul _).add hG
    refine tendstoInMeasure_zero_of_ae_eventually_abs_le (fun n => (hdiff_m n).aestronglyMeasurable)
      (fun n => (hbd_m n).aestronglyMeasurable) ?_ h1
    filter_upwards [hcons, hN_ae] with ω hcω hNω
    have hξne : ∀ᶠ n in atTop, (θh n ω).1 ≠ 0 :=
      ((continuous_fst.tendsto (ξ₀, μ₀, σ₀)).comp hcω).eventually (isOpen_ne.mem_nhds hξ₀0)
    have hσpos : ∀ᶠ n in atTop, 0 < (θh n ω).2.2 :=
      (((continuous_snd.comp continuous_snd).tendsto (ξ₀, μ₀, σ₀)).comp hcω).eventually (lt_mem_nhds hσ₀)
    filter_upwards [hξne, hσpos, hNω.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))]
      with n hξn hσn hN4
    have hθeq : gevThetaOf ξ₀ μ₀ σ₀ ((ξ₀, 0, 1) + gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) = θh n ω := by
      rw [gevEtaIncr, add_sub_cancel]
      exact gevThetaOf_gevEtaOf hξ₀0 hσ₀.ne' hξn hσn.ne'
    have hC := hCθ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) hN4.le
    rw [hθeq] at hC
    have hpart1 : |U n ω j - √(n : ℝ) * gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j| ≤
        Cθ * (√(n : ℝ) * N n ω ^ 2) := by
      rw [show U n ω j - √(n : ℝ) * gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j =
          -(√(n : ℝ) * (gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j -
            gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) j)) by ring,
        abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hcoord : |gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j -
          gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) j| ≤ Cθ * N n ω ^ 2 := by
        fin_cases j
        · simpa [gevThetaDiff, N] using hC.1
        · simpa [gevThetaDiff, N] using hC.2.1
        · have hzero : gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) 2 -
              gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) 2 = 0 := by
            simpa [gevThetaDiff] using hC.2.2
          change |gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) 2 -
            gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) 2| ≤ Cθ * N n ω ^ 2
          rw [hzero, abs_zero]
          exact mul_nonneg hCθ0 (sq_nonneg _)
      calc √(n : ℝ) * |gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j -
              gevEtaJ ξ₀ σ₀ (gevEtaIncr ξ₀ μ₀ σ₀ (θh n ω)) j|
          ≤ √(n : ℝ) * (Cθ * N n ω ^ 2) := mul_le_mul_of_nonneg_left hcoord (Real.sqrt_nonneg _)
        _ = Cθ * (√(n : ℝ) * N n ω ^ 2) := by ring
    have hAZ : (A *ᵥ Z n ω) j = (fun k => A k j) ⬝ᵥ Z n ω := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hAjk : A j k = A k j := by simpa [Matrix.transpose_apply] using congrFun (congrFun hAsym k) j
      rw [hAjk]
    have hpart2 : |√(n : ℝ) * gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j - (A *ᵥ Z n ω) j| ≤
        gevLinErr ξ₀ μ₀ σ₀ A (fun i => X i ω) (θh n ω) n := by
      rw [hAZ]
      exact Finset.single_le_sum (f := fun l => |√(n : ℝ) * gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) l -
          (fun k => A k l) ⬝ᵥ gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have htri := abs_sub_le (U n ω j) (√(n : ℝ) * gevThetaDiff ξ₀ μ₀ σ₀ (θh n ω) j) ((A *ᵥ Z n ω) j)
    linarith
  have hR₂_lim : TendstoInMeasure P
      (fun n ω => (U n ω - A *ᵥ Z n ω) ⬝ᵥ I *ᵥ (U n ω - A *ᵥ Z n ω)) atTop (fun _ => 0) := by
    have hterm : ∀ i j : Fin 3, TendstoInMeasure P
        (fun n ω => I i j * ((U n ω i - (A *ᵥ Z n ω) i) * (U n ω j - (A *ᵥ Z n ω) j)))
        atTop (fun _ => 0) := fun i j => by
      have hp := tendstoInMeasure_comp₂ (hUdiff i) (hUdiff j) (φ := fun p : ℝ × ℝ => p.1 * p.2)
        continuous_mul.continuousAt
      simp only [mul_zero] at hp
      simpa only [mul_zero] using tendstoInMeasure_comp hp (φ := fun z => I i j * z) (by fun_prop)
    have hsum : TendstoInMeasure P
        (fun n ω => ∑ i : Fin 3, ∑ j : Fin 3,
          I i j * ((U n ω i - (A *ᵥ Z n ω) i) * (U n ω j - (A *ᵥ Z n ω) j)))
        atTop (fun _ => 0) := by
      have h0 : ∀ i : Fin 3, TendstoInMeasure P
          (fun n ω => ∑ j : Fin 3, I i j * ((U n ω i - (A *ᵥ Z n ω) i) * (U n ω j - (A *ᵥ Z n ω) j)))
          atTop (fun _ => 0) := fun i => by
        have h01 := tendstoInMeasure_add_zero (hterm i 0) (hterm i 1)
        have h012 := tendstoInMeasure_add_zero h01 (hterm i 2)
        refine h012.congr_left fun n => ae_of_all _ fun ω => by simp [Fin.sum_univ_three]
      have h01 := tendstoInMeasure_add_zero (h0 0) (h0 1)
      have h012 := tendstoInMeasure_add_zero h01 (h0 2)
      refine h012.congr_left fun n => ae_of_all _ fun ω => by simp [Fin.sum_univ_three]
    refine hsum.congr_left fun n => ae_of_all _ fun ω => ?_
    simp only [dotProduct, Matrix.mulVec, Pi.sub_apply, Fin.sum_univ_three]
    ring
  -- Combine `R₁` and `-R₂` via the completion-of-the-square identity
  have hcomb := tendstoInMeasure_comp₂ hR₁_lim hR₂_lim (φ := fun p : ℝ × ℝ => p.1 - p.2)
    continuous_sub.continuousAt
  simp only [sub_zero] at hcomb
  refine hcomb.congr_left fun n => ae_of_all _ fun ω => ?_
  have hid := two_mul_dotProduct_sub_quad_eq hIsym hIinv (U n ω) (Z n ω)
  simp only [R₁]
  linarith

set_option maxHeartbeats 400000 in
/-- **Wilks' theorem for consistent local maximizers of the three-parameter GEV likelihood**
(`ξ₀ > -1/2`, `ξ₀ ≠ 0`): `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ⇒ χ²₃`. -/
theorem tendstoInDistribution_gevLocalDeviance (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, μ₀, σ₀)))
    (hloc : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω))
    (hadm : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      0 < gevU (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (X i ω))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 3) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        2 * (gevLogLikN (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (fun i => X i ω) n -
          gevLogLikN ξ₀ μ₀ σ₀ (fun i => X i ω) n))
      atTop Z (fun _ => P) P' := by
  set I := gevFisherInfo ξ₀ σ₀
  have hIpos : I.PosDef := posDef_gevFisherInfo hσ₀ hξ₀0 hξ₀
  have hW : HasLaw (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (multivariateGaussian 0 I) (multivariateGaussian 0 I) := HasLaw.id
  have hscore := tendstoInDistribution_gevScoreVec3 hξ₀ hξ₀0 hσ₀ hX hind hW
  let q : EuclideanSpace ℝ (Fin 3) → ℝ := fun v => v.ofLp ⬝ᵥ I⁻¹ *ᵥ v.ofLp
  have hq_cont : Continuous q := by
    unfold q; simp only [dotProduct, Matrix.mulVec]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul
        (continuous_finsetSum _ fun j _ =>
          continuous_const.mul ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _)))
  have hqLaw : HasLaw (q ∘ id) (chiSquared 3) (multivariateGaussian 0 I) :=
    hasLaw_dotProduct_inv_mulVec_chiSquared hIpos hW
  have hquad_clt : TendstoInDistribution
      (fun (n : ℕ) ω => gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n ⬝ᵥ
        I⁻¹ *ᵥ gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n)
      atTop Z (fun _ => P) P' := by
    have h1 := tendstoInDistribution_congr_limit (hscore.continuous_comp hq_cont) hqLaw hZ
    refine h1.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun _ => rfl)
    simp only [Function.comp_apply, q]
    have heq : ((√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gevScoreVec3 ξ₀ μ₀ σ₀ (X i ω)).ofLp =
        gevPathZ ξ₀ μ₀ σ₀ (fun i => X i ω) n := by
      ext k; exact (gevPathZ_eq_smul_sum (fun i => X i ω) n k).symm
    rw [heq]
  have hsub := tendstoInMeasure_gevLocalDeviance_sub hξ₀ hξ₀0 hσ₀ hX hind hθm hcons hloc hadm
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hDm : ∀ n, AEMeasurable (fun ω =>
      2 * (gevLogLikN (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (fun i => X i ω) n -
        gevLogLikN ξ₀ μ₀ σ₀ (fun i => X i ω) n)) P := fun n =>
    ((aemeasurable_gevLogLikN hXm (hθm n) n).sub
      (aemeasurable_gevLogLikN hXm (θ := fun _ => (ξ₀, μ₀, σ₀)) aemeasurable_const n)).const_mul 2
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ Z hquad_clt hsub hDm

/-- **Wilks' theorem for the three-parameter GEV maximum likelihood estimator** ([Coles, §2.6.5]),
regular non-Gumbel case `ξ₀ > -1/2`, `ξ₀ ≠ 0`:
for measurable maximizers `θ̂ₙ` over a compact `K ⊂ {ξ > -1, σ > 0}` with `θ₀ ∈ interior K`,
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) ⇒ χ²₃`. -/
theorem tendstoInDistribution_gevDeviance {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P) (hθK : ∀ n ω, θh n ω ∈ K)
    (hmax : ∀ n ω, IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2
      (fun i : Fin n => X i ω)) K (θh n ω))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 3) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        2 * (gevLogLikN (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (fun i => X i ω) n -
          gevLogLikN ξ₀ μ₀ σ₀ (fun i => X i ω) n))
      atTop Z (fun _ => P) P' := by
  have hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, μ₀, σ₀)) := by
    filter_upwards [ae_tendsto_gevMLE (θ₀ := (ξ₀, μ₀, σ₀)) hK hKS (interior_subset hθ₀) hσ₀ hX
      hind] with ω hω
    refine hω (fun n => θh n ω) (fun _ => 0) (fun n => hθK n ω) tendsto_const_nhds
      (Eventually.of_forall fun n => ?_)
    have := hmax n ω (interior_subset hθ₀)
    simp only [mem_ofPred_eq] at this; simpa using this
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (X i ω) := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gevU_pos hξ₀0 hσ₀)
  have hloc : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, IsLocalMax (fun p : ℝ × ℝ × ℝ =>
      gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω) := by
    filter_upwards [hcons] with ω hc
    filter_upwards [hc.eventually (isOpen_interior.mem_nhds hθ₀)] with n hn
    exact (hmax n ω).isLocalMax (mem_of_superset (isOpen_interior.mem_nhds hn) interior_subset)
  have hadm : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      0 < gevU (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (X i ω) := by
    filter_upwards [hcons, hsupp] with ω hc hx
    have hne : ∀ᶠ n in atTop, (θh n ω).1 ≠ 0 :=
      ((continuous_fst.tendsto (ξ₀, μ₀, σ₀)).comp hc).eventually (isOpen_ne.mem_nhds hξ₀0)
    filter_upwards [hne] with n hn i hi
    exact gevU_pos_of_isMaxOn (x := fun i : Fin n => X i ω) (interior_subset hθ₀) hξ₀0 hσ₀
      (fun i => hx i) hn (hmax n ω) ⟨i, hi⟩
  exact tendstoInDistribution_gevLocalDeviance hξ₀ hξ₀0 hσ₀ hX hind hθm hcons hloc hadm hZ

/-- **Asymptotic coverage of the three-parameter GEV deviance confidence region** ([Coles, §2.6.5]),
regular non-Gumbel case `ξ₀ > -1/2`, `ξ₀ ≠ 0`:
`P((ξ₀, μ₀, σ₀) ∈ gevDevianceRegion K c X) → χ²₃((-∞, c])`. -/
theorem tendsto_measure_mem_gevDevianceRegion {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2) (hθ₀ : (ξ₀, μ₀, σ₀) ∈ interior K)
    (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure P) (hind : iIndepFun X P) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω | (ξ₀, μ₀, σ₀) ∈ gevDevianceRegion K c (fun i : Fin n => X i ω)})
      atTop (𝓝 (chiSquared 3 (Iic c))) := by
  choose G hGm hG using exists_measurable_gevMLE hK hKS ⟨_, interior_subset hθ₀⟩
  have hsam : ∀ n : ℕ, AEMeasurable (fun ω => (fun i : Fin n => X i ω)) P := fun n =>
    AEMeasurable.of_eval fun i => (hX i).aemeasurable
  have hD := tendstoInDistribution_gevDeviance hK hKS hθ₀ hξ₀ hξ₀0 hσ₀ hX hind
    (θh := fun n ω => G n fun i : Fin n => X i ω)
    (fun n => (hGm n).comp_aemeasurable (hsam n)) (fun n ω => (hG n _).1) (fun n ω => (hG n _).2)
    (Z := id) (P' := chiSquared 3) HasLaw.id
  refine (hD.tendsto_measure_le_of_noAtoms HasLaw.id c).congr fun n => ?_
  refine measure_congr ?_
  have hsupp : ∀ᵐ ω ∂P, ∀ i, 0 < gevU ξ₀ μ₀ σ₀ (X i ω) := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ ae_gevU_pos hξ₀0 hσ₀)
  filter_upwards [hsupp] with ω hω
  apply propext
  set x := fun i : Fin n => X i ω
  have h0_coe : gevLogLikE ξ₀ μ₀ σ₀ x = ((gevLogLikN ξ₀ μ₀ σ₀ (fun i => X i ω) n : ℝ) : EReal) := by
    rw [gevLogLikE_eq_coe fun i => gevLocScaleDensity_pos hσ₀ hξ₀0 (hω i), gevLogLik, gevLogLikN,
      Fin.sum_univ_eq_sum_range (fun i => log (gevLocScaleDensity ξ₀ μ₀ σ₀ (X i ω))) n]
  have h0_ne_bot : gevLogLikE ξ₀ μ₀ σ₀ x ≠ ⊥ := by rw [h0_coe]; exact EReal.coe_ne_bot _
  have hle : gevLogLikE ξ₀ μ₀ σ₀ x ≤ gevLogLikE (G n x).1 (G n x).2.1 (G n x).2.2 x :=
    (hG n x).2 (interior_subset hθ₀)
  have hG_coe : gevLogLikE (G n x).1 (G n x).2.1 (G n x).2.2 x =
      ((gevLogLikN (G n x).1 (G n x).2.1 (G n x).2.2 (fun i => X i ω) n : ℝ) : EReal) := by
    rw [gevLogLikE_eq_coe_of_ne_bot (ne_bot_of_le_ne_bot h0_ne_bot hle), gevLogLikN,
      Fin.sum_univ_eq_sum_range (fun i => log (gevLocScaleDensity (G n x).1 (G n x).2.1 (G n x).2.2 (X i ω))) n]
  have hmax_eq : gevMaxLogLik K x =
      ((gevLogLikN (G n x).1 (G n x).2.1 (G n x).2.2 (fun i => X i ω) n : ℝ) : EReal) := by
    rw [gevMaxLogLik_eq_of_isMaxOn (hG n x).1 (hG n x).2, hG_coe]
  change 2 * (gevLogLikN (G n x).1 (G n x).2.1 (G n x).2.2 (fun i => X i ω) n -
      gevLogLikN ξ₀ μ₀ σ₀ (fun i => X i ω) n) ≤ c ↔
    (ξ₀, μ₀, σ₀) ∈ K ∧ gevMaxLogLik K x ≠ ⊥ ∧ gevMaxLogLik K x ≠ ⊤ ∧
    2 * (gevMaxLogLik K x - gevLogLikE ξ₀ μ₀ σ₀ x) ≤ (c : EReal)
  rw [and_iff_right (interior_subset hθ₀), hmax_eq, h0_coe,
    and_iff_right (EReal.coe_ne_bot _), and_iff_right (EReal.coe_ne_top _),
    ← EReal.coe_sub, show (2 : EReal) = ((2 : ℝ) : EReal) from rfl, ← EReal.coe_mul,
    EReal.coe_le_coe_iff]

end NonGumbel

/-! ### Wilks' theorem for the three-parameter GEV at the Gumbel boundary `ξ₀ = 0` -/

section GumbelBoundary

variable {μ₀ σ₀ : ℝ} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}

/-- Weighted segment Hessian entry `∫₀¹ 2 (1 - s) H(θ₀ + s (θ - θ₀))[eᵢ, eⱼ] ds` at `ξ₀ = 0`. -/
noncomputable def gevZeroSegHW (μ₀ σ₀ : ℝ) (θ : ℝ × ℝ × ℝ) (i j : Fin 3) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, 2 * (1 - s) *
    gevZeroH (gevStep (μ₀, σ₀, 0) (θ.1 - μ₀, θ.2.1 - σ₀, θ.2.2) s)
      (gevZeroBasis i) (gevZeroBasis j) x

/-- Convergence in probability of the averaged weighted segment Hessian `B_W(i, j) → -I₀(i, j)`. -/
theorem tendstoInMeasure_avg_gevZeroSegHW (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ}
    (hθcons : TendstoInMeasure P θh atTop (fun _ => (μ₀, σ₀, (0 : ℝ))))
    (hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0)) (i j : Fin 3) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω))
      atTop (fun _ => -gevFisherInfoZero σ₀ i j) := by
  set C₀ : ℝ := 7000 * (1 + σ₀⁻¹ ^ 2)
  have hC₀ : 0 < C₀ := by positivity
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  obtain ⟨M, hM_int⟩ := ((tendsto_integral_gevZeroEnvTail (μ₀ := μ₀) hσ₀).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / (8 * C₀) by positivity))).exists
  obtain ⟨δ, hδ, hδ_le, hδ_unif⟩ := exists_delta_gevZeroH_sub_le (μ₀ := μ₀) hσ₀ (M : ℝ)
    (Nat.cast_nonneg M) (show (0 : ℝ) < ε / 4 by positivity) i j
  have hδ_σ : δ ≤ σ₀ / 8 := hδ_le.trans (min_le_left _ _)
  have hδ_8 : δ ≤ 1 / 8 := hδ_le.trans ((min_le_right _ _).trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [Nat.cast_nonneg (α := ℝ) M]))
  have hidX : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
    ⟨(hX k).aemeasurable, (hX 0).aemeasurable, by rw [(hX k).map_eq, (hX 0).map_eq]⟩
  have hslln : ∀ (g : ℝ → ℝ), Measurable g → Integrable g (gevLocScaleCDF 0 μ₀ hσ₀).measure →
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
    rw [hint_eq] at hω; simpa [smul_eq_mul] using hω
  have hH_meas := hslln _ (measurable_gevZeroH_zero μ₀ σ₀ (gevZeroBasis i) (gevZeroBasis j))
    (integrable_gevZeroH_zero hσ₀ _ _)
  rw [integral_gevZeroH_eq_neg_gevFisherInfoZero hσ₀ i j] at hH_meas
  have hT_meas := hslln _ (measurable_gevZeroEnvTail μ₀ σ₀ M) (integrable_gevZeroEnvTail hσ₀ M)
  have h1 : Tendsto (fun n : ℕ => P {ω | δ ≤ dist (θh n ω) (μ₀, σ₀, (0 : ℝ))}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.1 hθcons) δ hδ
  have h2 : Tendsto (fun n : ℕ => P {ω | (1 / 8 : ℝ) ≤
      |(θh n ω).2.2| * runMax (fun k => |(X k ω - μ₀) / σ₀|) n}) atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_norm.1 hξmax) (1 / 8) (by norm_num)
    refine h.congr fun n => ?_; congr 1; ext ω
    have hnn : 0 ≤ |(θh n ω).2.2| * runMax (fun k => |(X k ω - μ₀) / σ₀|) n :=
      mul_nonneg (abs_nonneg _) (runMax_nonneg _ _)
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn]
  have h3 : Tendsto (fun n : ℕ => P {ω | ε / 4 ≤
      |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
        (-gevFisherInfoZero σ₀ i j)|}) atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using (tendstoInMeasure_iff_norm.1 hH_meas) (ε / 4) (by positivity)
  set μT := ∫ x, gevZeroEnvTail μ₀ σ₀ (M : ℝ) x ∂(gevLocScaleCDF 0 μ₀ hσ₀).measure
  have hη : 0 < ε / (8 * C₀) - μT := sub_pos.2 hM_int
  have h4 : Tendsto (fun n : ℕ => P {ω | ε / (8 * C₀) - μT ≤
      |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) - μT|})
      atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using (tendstoInMeasure_iff_norm.1 hT_meas) (ε / (8 * C₀) - μT) hη
  have hsum_lim : Tendsto (fun n : ℕ =>
      P {ω | δ ≤ dist (θh n ω) (μ₀, σ₀, (0 : ℝ))} +
      P {ω | (1 / 8 : ℝ) ≤ |(θh n ω).2.2| * runMax (fun k => |(X k ω - μ₀) / σ₀|) n} +
      P {ω | ε / 4 ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
        (-gevFisherInfoZero σ₀ i j)|} +
      P {ω | ε / (8 * C₀) - μT ≤
        |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) - μT|})
      atTop (𝓝 0) := by simpa using ((h1.add h2).add h3).add h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum_lim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsub : {ω | ε ≤ ‖(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω) -
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
    have hpt : ∀ k ∈ Finset.range n,
        |gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω) -
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
          _ ≤ |(θh n ω).2.2| * (2 * (1 + runMax (fun m => |(X m ω - μ₀) / σ₀|) n)) := by gcongr
          _ = 2 * |(θh n ω).2.2| + 2 * (|(θh n ω).2.2| * runMax (fun m => |(X m ω - μ₀) / σ₀|) n) := by ring
          _ ≤ 2 * (1 / 8) + 2 * (1 / 8) := by linarith [hθ3.trans hδ_8]
          _ = 1 / 2 := by norm_num
      have hconst_int : gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) =
          ∫ s in (0 : ℝ)..1, 2 * (1 - s) *
            gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω) := by
        rw [intervalIntegral.integral_mul_const, integral_two_mul_one_sub, one_mul]
      have hcont_s : ContinuousOn (fun s => 2 * (1 - s) *
          gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) (X k ω)) (uIcc 0 1) := by
        refine (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn.mul ?_
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
      have hint_c : IntervalIntegrable (fun s => 2 * (1 - s) *
          gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)) volume 0 1 :=
        Continuous.intervalIntegrable (by fun_prop) 0 1
      rw [gevZeroSegHW, hconst_int, ← intervalIntegral.integral_sub hcont_s.intervalIntegrable hint_c]
      have hle_s : ∀ s ∈ Icc (0 : ℝ) 1,
          |gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) (X k ω) -
            gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)| ≤
          ε / 4 + 2 * C₀ * gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) := by
        intro s hs
        by_cases hM : |(X k ω - μ₀) / σ₀| ≤ (M : ℝ)
        · have h1s : |(γ s).1 - μ₀| ≤ δ := by
            simp only [γ, d, gevStep, add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
            nlinarith [hs.2, abs_nonneg ((θh n ω).1 - μ₀)]
          have h2s : |(γ s).2.1 - σ₀| ≤ δ := by
            simp only [γ, d, gevStep, add_sub_cancel_left, abs_mul, abs_of_nonneg hs.1]
            nlinarith [hs.2, abs_nonneg ((θh n ω).2.1 - σ₀)]
          have h3s : |(γ s).2.2| ≤ δ := by
            simp only [γ, d, gevStep, zero_add, abs_mul, abs_of_nonneg hs.1]
            nlinarith [hs.2, abs_nonneg (θh n ω).2.2]
          have hu := hδ_unif (γ s) h1s h2s h3s (X k ω) hM
          linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * C₀)
            (gevZeroEnvTail_nonneg μ₀ σ₀ M (X k ω))]
        · push Not at hM
          have htail_eq : gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) = gevZeroEnv μ₀ σ₀ (X k ω) :=
            Set.indicator_of_mem (show X k ω ∈ {x | (M : ℝ) < |(x - μ₀) / σ₀|} from hM) _
          rw [htail_eq]
          have hb1 := abs_gevZeroH_basis_le hσ₀ (gevStep_mem_gevZeroNbhd hθ_nbhd hs.1 hs.2)
            (hseg_t s hs) i j
          have h0_nbhd : (μ₀, σ₀, (0 : ℝ)) ∈ gevZeroNbhd μ₀ σ₀ :=
            ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by norm_num, by norm_num⟩
          have hb0 := abs_gevZeroH_basis_le hσ₀ h0_nbhd (by simp) i j (x := X k ω)
          have htri := abs_sub (gevZeroH (γ s) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
            (gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
          linarith
      refine (intervalIntegral.abs_integral_le_integral_abs (μ := volume) zero_le_one).trans ?_
      have hint_abs := (hcont_s.intervalIntegrable.sub hint_c).abs
      have hint_rhs : IntervalIntegrable
          (fun s => 2 * (1 - s) * (ε / 4 + 2 * C₀ * gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω))) volume 0 1 :=
        Continuous.intervalIntegrable (by fun_prop) 0 1
      have hmono := intervalIntegral.integral_mono_on zero_le_one hint_abs hint_rhs fun s hs => by
        rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 2 * (1 - s))]
        exact mul_le_mul_of_nonneg_left (hle_s s hs) (by linarith [hs.2])
      refine hmono.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_mul_const, integral_two_mul_one_sub, one_mul]
    have hdiff_avg : |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω) -
        (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)| ≤
        ε / 4 + 2 * C₀ * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.2 hn0)]
      calc (n : ℝ)⁻¹ * |∑ k ∈ Finset.range n, (gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω) -
              gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))|
          ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, |gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω) -
              gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hn0.le)
        _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (ε / 4 + 2 * C₀ * gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (inv_nonneg.2 hn0.le)
        _ = ε / 4 + 2 * C₀ * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.mul_sum]; field_simp [hn0.ne']
    have hT_bd : (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω) < ε / (8 * C₀) := by
      linarith [(abs_lt.1 hTlt).2]
    have h2CT : 2 * C₀ * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroEnvTail μ₀ σ₀ (M : ℝ) (X k ω)) <
        ε / 4 := by
      have h1 := mul_lt_mul_of_pos_left hT_bd (show (0 : ℝ) < 2 * C₀ by positivity)
      have heq : 2 * C₀ * (ε / (8 * C₀)) = ε / 4 := by field_simp [hC₀.ne']; ring
      linarith
    simp only [mem_ofPred_eq, Real.norm_eq_abs] at hω
    have htri := abs_sub_le
      ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω))
      ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroH (μ₀, σ₀, 0) (gevZeroBasis i) (gevZeroBasis j) (X k ω))
      (-gevFisherInfoZero σ₀ i j)
    linarith
  refine (measure_mono hsub).trans ?_
  calc P _ ≤ (P _ + P _) + (P _ + P _) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ = _ := by ring

/-- **Stochastic expansion of the three-parameter GEV deviance at the Gumbel boundary `ξ₀ = 0`**:
for `(μ, σ, ξ)`-ordered local maximizers `θ̂ₙ`,
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - Sₙᵀ I₀(σ₀)⁻¹ Sₙ → 0` in probability. -/
theorem tendstoInMeasure_gevLocalDeviance_zero_sub_muSigmaXi (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : TendstoInMeasure P θh atTop (fun _ => (μ₀, σ₀, (0 : ℝ))))
    (hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0))
    (hloc : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.2.2 p.1 p.2.1 (fun i : Fin n => X i ω)) (θh n ω)})
      atTop (𝓝 0)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω =>
        2 * (gevLogLikN (θh n ω).2.2 (θh n ω).1 (θh n ω).2.1 (fun i => X i ω) n -
          gevLogLikN 0 μ₀ σ₀ (fun i => X i ω) n) -
        ((√(n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω)).ofLp ⬝ᵥ
          (gevFisherInfoZero σ₀)⁻¹ *ᵥ
            ((√(n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω)).ofLp)
      atTop (fun _ => 0) := by
  set I₀ := gevFisherInfoZero σ₀
  set I₀inv := I₀⁻¹
  have hI₀pos : I₀.PosDef := posDef_gevFisherInfoZero hσ₀
  have hI₀_sym : I₀ᵀ = I₀ := by
    have := hI₀pos.isHermitian
    ext i j; simpa [Matrix.conjTranspose_apply] using congrFun (congrFun this i) j
  have hI₀inv_sym : I₀invᵀ = I₀inv := by rw [Matrix.transpose_nonsing_inv, hI₀_sym]
  have hdet : IsUnit I₀.det := isUnit_iff_ne_zero.2 hI₀pos.det_pos.ne'
  have hI₀mul : I₀ * I₀inv = 1 := Matrix.mul_nonsing_inv I₀ hdet
  have hI₀invmul : I₀inv * I₀ = 1 := Matrix.nonsing_inv_mul I₀ hdet
  -- Score, normalized MLE `T`, and segment Hessians `B` and `BW`
  set S : ℕ → Ω → Fin 3 → ℝ := fun n ω =>
    ((√(n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω)).ofLp
  set T : ℕ → Ω → Fin 3 → ℝ := fun n ω =>
    fun i => √(n : ℝ) * ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] i
  set B : ℕ → Ω → Matrix (Fin 3) (Fin 3) ℝ := fun n ω =>
    Matrix.of fun i j => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω)
  set BW : ℕ → Ω → Matrix (Fin 3) (Fin 3) ℝ := fun n ω =>
    Matrix.of fun i j => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω)
  have hB_lim : ∀ i j : Fin 3, TendstoInMeasure P (fun n ω => B n ω i j) atTop (fun _ => -I₀ i j) :=
    fun i j => tendstoInMeasure_avg_gevZeroSegH hσ₀ hX hind hcons hξmax i j
  have hBW_lim : ∀ i j : Fin 3, TendstoInMeasure P (fun n ω => BW n ω i j) atTop (fun _ => -I₀ i j) :=
    fun i j => tendstoInMeasure_avg_gevZeroSegHW hσ₀ hX hind hcons hξmax i j
  -- Tightness of `T` from `tendstoInDistribution_gevLocalMLE_zero_muSigmaXi`
  have hT_clt : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • !₂[(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2])
      atTop (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (fun _ => P)
      (multivariateGaussian 0 I₀inv) :=
    tendstoInDistribution_gevLocalMLE_zero_muSigmaXi hσ₀ hX hind hθm hcons hξmax hloc HasLaw.id
  -- Exact event-based `ε-η` proof: on the good event where `θ̂ ∈ gevZeroNbhd`, `|ξ̂| M < 1/8`,
  -- `IsLocalMax`, `‖T‖ < M`, `|B + I₀| < δ`, `|BW + I₀| < δ`, the deviance difference is `< ε`!
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  set C_I : ℝ := 1 + ∑ i : Fin 3, ∑ j : Fin 3, |I₀ i j|
  set C_inv : ℝ := 1 + ∑ i : Fin 3, ∑ j : Fin 3, |I₀inv i j|
  have hCI : 0 < C_I := by
    have : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, |I₀ i j| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hCinv : 0 < C_inv := by
    have : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, |I₀inv i j| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  -- Split `η` into 22 pieces (4 main events + 9 for `B` + 9 for `BW`)
  have hη22 : 0 < η / 22 := ENNReal.div_pos hη.ne' (by norm_num)
  obtain ⟨MT, hMT⟩ := hT_clt.exists_measure_le_norm_le hη22
  set M' := max MT 1
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set δB : ℝ := min (1 / 2) (min (√(ε / (4 * C_I * (3 * C_inv * M') ^ 2)))
    (ε / (2 * 9 * M' ^ 2)))
  have hδB : 0 < δB := lt_min (by norm_num) (lt_min (Real.sqrt_pos.2 (by positivity)) (by positivity))
  set δθ : ℝ := min (σ₀ / 8) (1 / 8)
  have hδθ : 0 < δθ := lt_min (by positivity) (by norm_num)
  have hp1 : ∀ᶠ n in atTop, P {ω | δθ ≤ dist (θh n ω) (μ₀, σ₀, (0 : ℝ))} ≤ η / 22 :=
    (((tendstoInMeasure_iff_dist.1 hcons) δθ hδθ).eventually (gt_mem_nhds hη22)).mono fun _ h => h.le
  have hp2 : ∀ᶠ n in atTop, P {ω | (1 / 8 : ℝ) ≤
      |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n} ≤ η / 22 := by
    have h := (tendstoInMeasure_iff_norm.1 hξmax) (1 / 8) (by norm_num)
    refine (h.eventually (gt_mem_nhds hη22)).mono fun n hn => ?_
    have heq : {ω | (1 / 8 : ℝ) ≤ |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n} =
        {ω | (1 / 8 : ℝ) ≤ ‖|(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n - 0‖} := by
      ext ω
      have hnn : 0 ≤ |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n :=
        mul_nonneg (abs_nonneg _) (runMax_nonneg _ _)
      simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn]
    rw [heq]; exact hn.le
  have hp3 : ∀ᶠ n in atTop, P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.2.2 p.1 p.2.1 (fun i : Fin n => X i ω)) (θh n ω)} ≤ η / 22 :=
    (hloc.eventually (gt_mem_nhds hη22)).mono fun _ h => h.le
  have hpB : ∀ᶠ n in atTop, ∀ i j : Fin 3,
      P {ω | δB ≤ |B n ω i j - (-I₀ i j)|} ≤ η / 22 := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have h := (tendstoInMeasure_iff_norm.1 (hB_lim i j)) δB hδB
    refine (h.eventually (gt_mem_nhds hη22)).mono fun n hn => ?_
    simpa [Real.norm_eq_abs] using hn.le
  have hpBW : ∀ᶠ n in atTop, ∀ i j : Fin 3,
      P {ω | δB ≤ |BW n ω i j - (-I₀ i j)|} ≤ η / 22 := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have h := (tendstoInMeasure_iff_norm.1 (hBW_lim i j)) δB hδB
    refine (h.eventually (gt_mem_nhds hη22)).mono fun n hn => ?_
    simpa [Real.norm_eq_abs] using hn.le
  filter_upwards [eventually_ge_atTop 1, hMT, hp1, hp2, hp3, hpB, hpBW]
    with n hn hMTn h1 h2 h3 hBn hBWn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hsq2 : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
  have hsub : {ω | ε ≤ ‖2 * (gevLogLikN (θh n ω).2.2 (θh n ω).1 (θh n ω).2.1 (fun i => X i ω) n -
        gevLogLikN 0 μ₀ σ₀ (fun i => X i ω) n) - S n ω ⬝ᵥ I₀inv *ᵥ S n ω - 0‖} ⊆
      ({ω | MT ≤ ‖√(n : ℝ) • !₂[(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2]‖} ∪
       {ω | δθ ≤ dist (θh n ω) (μ₀, σ₀, (0 : ℝ))}) ∪
      (({ω | (1 / 8 : ℝ) ≤ |(θh n ω).2.2| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n} ∪
        {ω | ¬ IsLocalMax (fun p : ℝ × ℝ × ℝ => gevLogLikE p.2.2 p.1 p.2.1 (fun i : Fin n => X i ω))
          (θh n ω)}) ∪
       ((⋃ i : Fin 3, ⋃ j : Fin 3, {ω | δB ≤ |B n ω i j - (-I₀ i j)|}) ∪
        (⋃ i : Fin 3, ⋃ j : Fin 3, {ω | δB ≤ |BW n ω i j - (-I₀ i j)|}))) := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists, not_le, not_not] at hnot
    obtain ⟨⟨hTlt, hθlt⟩, ⟨⟨hξlt, hlocω⟩, ⟨hBlt, hBWlt⟩⟩⟩ := hnot
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
    set d : ℝ × ℝ × ℝ := ((θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2)
    have hseg : ∀ k < n, ∀ s ∈ Icc (0 : ℝ) 1,
        |(gevStep (μ₀, σ₀, 0) d s).2.2 * gevZeroZ (gevStep (μ₀, σ₀, 0) d s) (X k ω)| ≤ 1 / 2 := by
      intro k hk s hs
      have hm := gevStep_mem_gevZeroNbhd hθ_nbhd hs.1 hs.2
      have hz := abs_gevZeroZ_le hσ₀ hm (x := X k ω)
      have hξs : |(gevStep (μ₀, σ₀, 0) d s).2.2| ≤ |(θh n ω).2.2| := by
        simp only [d, gevStep, zero_add, abs_mul, abs_of_nonneg hs.1]
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
    have hadm : ∀ k : Fin n, 0 < 1 + (θh n ω).2.2 * gevZeroZ (θh n ω) (X k ω) := fun k => by
      have hs1 := hseg k.1 k.2 1 ⟨zero_le_one, le_rfl⟩
      have hst : gevStep (μ₀, σ₀, 0) d 1 = θh n ω := by simp [d, gevStep]
      rw [hst] at hs1; linarith [neg_abs_le ((θh n ω).2.2 * gevZeroZ (θh n ω) (X k ω))]
    -- 1. First-order optimality: `B n ω *ᵥ T n ω = -S n ω`
    have hscore0 : ∀ i : Fin 3, ∑ k ∈ Finset.range n, gevZeroD (θh n ω) (gevZeroBasis i) (X k ω) = 0 := by
      intro i
      have hfin := sum_gevZeroD_eq_zero_of_isLocalMax hσθ hadm hlocω (gevZeroBasis i)
      rwa [Fin.sum_univ_eq_sum_range (fun k => gevZeroD (θh n ω) (gevZeroBasis i) (X k ω)) n] at hfin
    have hBT : (B n ω) *ᵥ T n ω = -S n ω := by
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
      have hS_i : S n ω i = (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω) i := by
        simp [S, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
      simp only [B, T, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.neg_apply, hS_i]
      have hinv : (n : ℝ)⁻¹ * √(n : ℝ) = (√(n : ℝ))⁻¹ :=
        calc (n : ℝ)⁻¹ * √(n : ℝ) = (√(n : ℝ) * √(n : ℝ))⁻¹ * √(n : ℝ) := by rw [hsq2]
          _ = (√(n : ℝ))⁻¹ := by rw [mul_inv, mul_assoc, inv_mul_cancel₀ hsq0.ne', mul_one]
      have hlhs : ∑ j : Fin 3, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω)) *
          (√(n : ℝ) * ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j) =
          (√(n : ℝ))⁻¹ * ∑ j : Fin 3, ∑ k ∈ Finset.range n,
            ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j *
              gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum]
        calc ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω)) *
              (√(n : ℝ) * ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j)
            = ((n : ℝ)⁻¹ * √(n : ℝ)) * (![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j *
                ∑ k ∈ Finset.range n, gevZeroSegH μ₀ σ₀ (θh n ω) i j (X k ω)) := by ring
          _ = _ := by rw [hinv]
      rw [hlhs, ← hsum_ftc]; ring
    -- 2. Exact identity `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) = 2 (T · S) + Tᵀ BW T`
    have hdev_eq : 2 * (gevLogLikN (θh n ω).2.2 (θh n ω).1 (θh n ω).2.1 (fun i => X i ω) n -
        gevLogLikN 0 μ₀ σ₀ (fun i => X i ω) n) =
        2 * (T n ω ⬝ᵥ S n ω) + T n ω ⬝ᵥ (BW n ω) *ᵥ T n ω := by
      have hdiff_k : ∀ k ∈ Finset.range n,
          2 * (log (gevLocScaleDensity (θh n ω).2.2 (θh n ω).1 (θh n ω).2.1 (X k ω)) -
            log (gevLocScaleDensity 0 μ₀ σ₀ (X k ω))) =
          2 * (∑ i : Fin 3, (![d.1, d.2.1, d.2.2] i) * gumbelScoreVec3 μ₀ σ₀ (X k ω) i) +
          ∑ i : Fin 3, ∑ j : Fin 3,
            (![d.1, d.2.1, d.2.2] i) * (![d.1, d.2.1, d.2.2] j) *
              gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω) := by
        intro k hk
        have hk_lt : k < n := Finset.mem_range.1 hk
        rw [← gevZeroLog_eq_log_density hσθ (hadm ⟨k, hk_lt⟩),
          ← gevZeroLog_eq_log_density (θ := (μ₀, σ₀, 0)) hσ₀ (by simp),
          gevZeroLog_sub_eq_taylor hσ₀ hθ_nbhd (hseg k hk_lt)]
        have hD_lin : gevZeroD (μ₀, σ₀, 0) d (X k ω) =
            ∑ i : Fin 3, (![d.1, d.2.1, d.2.2] i) * gumbelScoreVec3 μ₀ σ₀ (X k ω) i := by
          rw [gevZeroD_eq_sum]
          simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
            gevZeroD_basis_zero]
        have hH_int : 2 * ∫ s in (0 : ℝ)..1, (1 - s) *
              gevZeroH (gevStep (μ₀, σ₀, 0) d s) d d (X k ω) =
            ∑ i : Fin 3, ∑ j : Fin 3, (![d.1, d.2.1, d.2.2] i) * (![d.1, d.2.1, d.2.2] j) *
              gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω) := by
          rw [← intervalIntegral.integral_const_mul]
          have hrew : (fun s => 2 * ((1 - s) * gevZeroH (gevStep (μ₀, σ₀, 0) d s) d d (X k ω))) =
              fun s => ∑ i : Fin 3, ∑ j : Fin 3,
                (![d.1, d.2.1, d.2.2] i) * (![d.1, d.2.1, d.2.2] j) *
                  (2 * (1 - s) * gevZeroH (gevStep (μ₀, σ₀, 0) d s) (gevZeroBasis i) (gevZeroBasis j) (X k ω)) := by
            funext s
            rw [gevZeroH_eq_sum]
            simp only [Fin.sum_univ_three]
            ring
          rw [hrew]
          have hint_ij : ∀ i j : Fin 3, IntervalIntegrable (fun s =>
              (![d.1, d.2.1, d.2.2] i) * (![d.1, d.2.1, d.2.2] j) *
                (2 * (1 - s) * gevZeroH (gevStep (μ₀, σ₀, 0) d s) (gevZeroBasis i) (gevZeroBasis j) (X k ω)))
              volume 0 1 := fun i j => by
            refine (ContinuousOn.intervalIntegrable ?_)
            refine continuousOn_const.mul
              ((continuous_const.mul (continuous_const.sub continuous_id)).continuousOn.mul ?_)
            intro s hs
            rw [uIcc_of_le zero_le_one] at hs
            have hm := gevStep_mem_gevZeroNbhd hθ_nbhd hs.1 hs.2
            have hσs : 0 < (gevStep (μ₀, σ₀, 0) d s).2.1 := by linarith [(mem_gevZeroNbhd_bounds hm).2.1]
            have hus : 0 < 1 + (gevStep (μ₀, σ₀, 0) d s).2.2 * gevZeroZ (gevStep (μ₀, σ₀, 0) d s) (X k ω) := by
              linarith [neg_abs_le ((gevStep (μ₀, σ₀, 0) d s).2.2 *
                gevZeroZ (gevStep (μ₀, σ₀, 0) d s) (X k ω)), hseg k hk_lt s hs]
            have hγc : ContinuousAt (fun r => (gevStep (μ₀, σ₀, 0) d r, X k ω)) s := by
              unfold gevStep; fun_prop
            exact (ContinuousAt.comp (f := fun r => (gevStep (μ₀, σ₀, 0) d r, X k ω))
              (g := fun p : (ℝ × ℝ × ℝ) × ℝ => gevZeroH p.1 (gevZeroBasis i) (gevZeroBasis j) p.2)
              (continuousAt_gevZeroH_basis hσs hus i j) hγc).continuousWithinAt
          have hint_i : ∀ i : Fin 3, IntervalIntegrable (fun s => ∑ j : Fin 3,
              (![d.1, d.2.1, d.2.2] i) * (![d.1, d.2.1, d.2.2] j) *
                (2 * (1 - s) * gevZeroH (gevStep (μ₀, σ₀, 0) d s) (gevZeroBasis i) (gevZeroBasis j) (X k ω)))
              volume 0 1 := fun i => IntervalIntegrable.sum Finset.univ fun j _ => hint_ij i j
          rw [intervalIntegral.integral_finsetSum (f := fun i s => ∑ j : Fin 3,
              (![d.1, d.2.1, d.2.2] i) * (![d.1, d.2.1, d.2.2] j) *
                (2 * (1 - s) * gevZeroH (gevStep (μ₀, σ₀, 0) d s) (gevZeroBasis i) (gevZeroBasis j) (X k ω)))
            fun i _ => hint_i i]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [intervalIntegral.integral_finsetSum (f := fun j s =>
              (![d.1, d.2.1, d.2.2] i) * (![d.1, d.2.1, d.2.2] j) *
                (2 * (1 - s) * gevZeroH (gevStep (μ₀, σ₀, 0) d s) (gevZeroBasis i) (gevZeroBasis j) (X k ω)))
            fun j _ => hint_ij i j]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [intervalIntegral.integral_const_mul]; rfl
        rw [mul_add, hD_lin, hH_int]
      rw [gevLogLikN, gevLogLikN, ← Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_congr rfl hdiff_k, Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [T, S, dotProduct, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
          smul_eq_mul, d, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        have h1 : √(n : ℝ) * (√(n : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hsq0.ne'
        calc 2 * (![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] i *
              ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω) i)
            = 2 * ((√(n : ℝ) * ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] i) *
                ((√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω) i)) := by
              rw [show (√(n : ℝ) * ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] i) *
                  ((√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω) i) =
                  (√(n : ℝ) * (√(n : ℝ))⁻¹) * (![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] i *
                  ∑ k ∈ Finset.range n, gumbelScoreVec3 μ₀ σ₀ (X k ω) i) by ring, h1, one_mul]
          _ = ∑ x ∈ Finset.range n, 2 * (√(n : ℝ) * ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] i *
                ((√(n : ℝ))⁻¹ * (gumbelScoreVec3 μ₀ σ₀ (X x ω)).ofLp i)) := by
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      · rw [Finset.sum_comm]
        simp only [T, BW, dotProduct, Matrix.mulVec, Matrix.of_apply, d]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum]
        have : (n : ℝ)⁻¹ * (√(n : ℝ) * √(n : ℝ)) = 1 := by rw [hsq2, inv_mul_cancel₀ hn0.ne']
        calc (![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] i *
              ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j) *
              ∑ k ∈ Finset.range n, gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω)
            = ((n : ℝ)⁻¹ * (√(n : ℝ) * √(n : ℝ))) *
              ((![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] i *
                ![(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2] j) *
                ∑ k ∈ Finset.range n, gevZeroSegHW μ₀ σ₀ (θh n ω) i j (X k ω)) := by rw [this, one_mul]
          _ = _ := by ring
    -- 3. Bound `|2(ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - Sᵀ I₀⁻¹ S|` using completion of the square
    have hid := two_mul_dotProduct_sub_quad_eq hI₀_sym hI₀mul (T n ω) (S n ω)
    have hrew : 2 * (gevLogLikN (θh n ω).2.2 (θh n ω).1 (θh n ω).2.1 (fun i => X i ω) n -
        gevLogLikN 0 μ₀ σ₀ (fun i => X i ω) n) - S n ω ⬝ᵥ I₀inv *ᵥ S n ω =
        T n ω ⬝ᵥ (BW n ω + I₀) *ᵥ T n ω - (T n ω - I₀inv *ᵥ S n ω) ⬝ᵥ I₀ *ᵥ (T n ω - I₀inv *ᵥ S n ω) := by
      rw [hdev_eq]
      have hsplit : T n ω ⬝ᵥ (BW n ω + I₀) *ᵥ T n ω =
          T n ω ⬝ᵥ (BW n ω) *ᵥ T n ω + T n ω ⬝ᵥ I₀ *ᵥ T n ω := by
        rw [Matrix.add_mulVec, dotProduct_add]
      linarith
    -- Coordinate bound `|T n ω i| ≤ M'`
    have hT_coord : ∀ i : Fin 3, |T n ω i| ≤ M' := fun i => by
      have h1 : |T n ω i| ≤ ‖√(n : ℝ) • !₂[(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2]‖ := by
        simpa [T, Real.norm_eq_abs, PiLp.smul_apply, smul_eq_mul] using
          PiLp.norm_apply_le (√(n : ℝ) • !₂[(θh n ω).1 - μ₀, (θh n ω).2.1 - σ₀, (θh n ω).2.2]) i
      exact h1.trans (hTlt.le.trans (le_max_left MT 1))
    -- Term A: `|Tᵀ (BW + I₀) T| ≤ 9 * δB * M'² ≤ ε / 2`
    have htermA : |T n ω ⬝ᵥ (BW n ω + I₀) *ᵥ T n ω| ≤ ε / 2 := by
      have h1 : |T n ω ⬝ᵥ (BW n ω + I₀) *ᵥ T n ω| ≤
          ∑ i : Fin 3, ∑ j : Fin 3, |T n ω i| * |BW n ω i j + I₀ i j| * |T n ω j| := by
        simp only [dotProduct, Matrix.mulVec, Matrix.add_apply, Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        have h : |T n ω i * ((BW n ω i j + I₀ i j) * T n ω j)| =
            |T n ω i| * |BW n ω i j + I₀ i j| * |T n ω j| :=
          calc |T n ω i * ((BW n ω i j + I₀ i j) * T n ω j)|
              = |T n ω i| * |(BW n ω i j + I₀ i j) * T n ω j| := abs_mul _ _
            _ = |T n ω i| * (|BW n ω i j + I₀ i j| * |T n ω j|) := by congr 1; exact abs_mul _ _
            _ = _ := by ring
        exact h.le
      have h2 : ∑ i : Fin 3, ∑ j : Fin 3, |T n ω i| * |BW n ω i j + I₀ i j| * |T n ω j| ≤
          9 * δB * M' ^ 2 := by
        calc _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, M' * δB * M' := Finset.sum_le_sum fun i _ =>
                Finset.sum_le_sum fun j _ => by
                  have hbij : |BW n ω i j + I₀ i j| ≤ δB := by
                    simpa [sub_neg_eq_add] using (hBWlt i j).le
                  have h1 := mul_le_mul (hT_coord i) hbij (abs_nonneg _) hM'0.le
                  exact mul_le_mul h1 (hT_coord j) (abs_nonneg _) (mul_nonneg hM'0.le hδB.le)
          _ = 9 * δB * M' ^ 2 := by simp; ring
      have h3 : δB ≤ ε / (2 * 9 * M' ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
      have h4 : 9 * δB * M' ^ 2 ≤ ε / 2 := by
        have := mul_le_mul_of_nonneg_right h3 (show (0 : ℝ) ≤ 9 * M' ^ 2 by positivity)
        have heq : ε / (2 * 9 * M' ^ 2) * (9 * M' ^ 2) = ε / 2 := by field_simp [hM'0.ne']
        linarith
      exact h1.trans (h2.trans h4)
    -- Term B: `T - I₀⁻¹ S = I₀⁻¹ (B + I₀) T`, so `|(T - I₀⁻¹ S)_i| ≤ 3 * C_inv * δB * M'`
    have hTS_eq : T n ω - I₀inv *ᵥ S n ω = I₀inv *ᵥ ((B n ω + I₀) *ᵥ T n ω) := by
      rw [Matrix.add_mulVec, hBT, Matrix.mulVec_add, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, hI₀invmul, Matrix.one_mulVec]
      ext i; simp [sub_eq_add_neg, add_comm]
    have hTS_coord : ∀ i : Fin 3, |(T n ω - I₀inv *ᵥ S n ω) i| ≤ 3 * C_inv * δB * M' := fun i => by
      rw [hTS_eq]
      have hBT_j : ∀ l : Fin 3, |((B n ω + I₀) *ᵥ T n ω) l| ≤ 3 * δB * M' := fun l => by
        simp only [Matrix.mulVec, dotProduct, Matrix.add_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ j : Fin 3, |(B n ω l j + I₀ l j) * T n ω j|
            ≤ ∑ _j : Fin 3, δB * M' := Finset.sum_le_sum fun j _ => by
              rw [abs_mul]
              exact mul_le_mul (by simpa [sub_neg_eq_add] using (hBlt l j).le) (hT_coord j)
                (abs_nonneg _) hδB.le
          _ = 3 * δB * M' := by simp; ring
      simp only [Matrix.mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l : Fin 3, |I₀inv i l * ((B n ω + I₀) *ᵥ T n ω) l|
          ≤ ∑ l : Fin 3, |I₀inv i l| * (3 * δB * M') := Finset.sum_le_sum fun l _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hBT_j l) (abs_nonneg _)
        _ = (∑ l : Fin 3, |I₀inv i l|) * (3 * δB * M') := (Finset.sum_mul _ _ _).symm
        _ ≤ C_inv * (3 * δB * M') := by
            have hle : ∑ l : Fin 3, |I₀inv i l| ≤ C_inv := by
              have h1 : ∑ l : Fin 3, |I₀inv i l| ≤ ∑ r : Fin 3, ∑ l : Fin 3, |I₀inv r l| :=
                Finset.single_le_sum (f := fun r => ∑ l : Fin 3, |I₀inv r l|)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
              simp only [C_inv]; linarith
            exact mul_le_mul_of_nonneg_right hle (by positivity)
        _ = 3 * C_inv * δB * M' := by ring
    have htermB : |(T n ω - I₀inv *ᵥ S n ω) ⬝ᵥ I₀ *ᵥ (T n ω - I₀inv *ᵥ S n ω)| < ε / 2 := by
      have h1 : |(T n ω - I₀inv *ᵥ S n ω) ⬝ᵥ I₀ *ᵥ (T n ω - I₀inv *ᵥ S n ω)| ≤
          C_I * (3 * C_inv * δB * M') ^ 2 := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i : Fin 3, |∑ j : Fin 3, (T n ω - I₀inv *ᵥ S n ω) i * (I₀ i j * (T n ω - I₀inv *ᵥ S n ω) j)|
            ≤ ∑ i : Fin 3, ∑ j : Fin 3, |I₀ i j| * (3 * C_inv * δB * M') ^ 2 :=
              Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun j _ => by
                  rw [abs_mul, abs_mul]
                  have hi := hTS_coord i; have hj := hTS_coord j
                  have hprod := mul_le_mul hi hj (abs_nonneg _) (by positivity)
                  calc |(T n ω - I₀inv *ᵥ S n ω) i| * (|I₀ i j| * |(T n ω - I₀inv *ᵥ S n ω) j|)
                      = |I₀ i j| * (|(T n ω - I₀inv *ᵥ S n ω) i| * |(T n ω - I₀inv *ᵥ S n ω) j|) := by ring
                    _ ≤ |I₀ i j| * ((3 * C_inv * δB * M') * (3 * C_inv * δB * M')) :=
                          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
                    _ = _ := by ring)
          _ = (∑ i : Fin 3, ∑ j : Fin 3, |I₀ i j|) * (3 * C_inv * δB * M') ^ 2 := by
                simp_rw [← Finset.sum_mul]
          _ ≤ C_I * (3 * C_inv * δB * M') ^ 2 := by
                have : ∑ i : Fin 3, ∑ j : Fin 3, |I₀ i j| ≤ C_I := by simp only [C_I]; linarith
                exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      have hδ2 : δB ^ 2 ≤ ε / (4 * C_I * (3 * C_inv * M') ^ 2) := by
        have hle : δB ≤ √(ε / (4 * C_I * (3 * C_inv * M') ^ 2)) :=
          (min_le_right _ _).trans (min_le_left _ _)
        calc δB ^ 2 ≤ (√(ε / (4 * C_I * (3 * C_inv * M') ^ 2))) ^ 2 :=
              pow_le_pow_left₀ hδB.le hle 2
          _ = ε / (4 * C_I * (3 * C_inv * M') ^ 2) := Real.sq_sqrt (by positivity)
      have h2 : C_I * (3 * C_inv * δB * M') ^ 2 ≤ ε / 4 := by
        have heq : C_I * (3 * C_inv * δB * M') ^ 2 = (C_I * (3 * C_inv * M') ^ 2) * δB ^ 2 := by ring
        rw [heq]
        calc (C_I * (3 * C_inv * M') ^ 2) * δB ^ 2
            ≤ (C_I * (3 * C_inv * M') ^ 2) * (ε / (4 * C_I * (3 * C_inv * M') ^ 2)) :=
              mul_le_mul_of_nonneg_left hδ2 (by positivity)
          _ = ε / 4 := by field_simp [hCI.ne', hCinv.ne', hM'0.ne']
      linarith
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hω
    rw [hrew] at hω
    have htri := abs_sub (T n ω ⬝ᵥ (BW n ω + I₀) *ᵥ T n ω)
      ((T n ω - I₀inv *ᵥ S n ω) ⬝ᵥ I₀ *ᵥ (T n ω - I₀inv *ᵥ S n ω))
    linarith
  -- Sum the 22 union bounds
  have hB_sum : P (⋃ i : Fin 3, ⋃ j : Fin 3, {ω | δB ≤ |B n ω i j - (-I₀ i j)|}) ≤ 9 * (η / 22) := by
    refine (measure_iUnion_fintype_le P _).trans ?_
    calc ∑ i : Fin 3, P (⋃ j : Fin 3, {ω | δB ≤ |B n ω i j - (-I₀ i j)|})
        ≤ ∑ i : Fin 3, ∑ j : Fin 3, P {ω | δB ≤ |B n ω i j - (-I₀ i j)|} :=
          Finset.sum_le_sum fun i _ => measure_iUnion_fintype_le P _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (η / 22) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hBn i j
      _ = 9 * (η / 22) := by simp; ring
  have hBW_sum : P (⋃ i : Fin 3, ⋃ j : Fin 3, {ω | δB ≤ |BW n ω i j - (-I₀ i j)|}) ≤ 9 * (η / 22) := by
    refine (measure_iUnion_fintype_le P _).trans ?_
    calc ∑ i : Fin 3, P (⋃ j : Fin 3, {ω | δB ≤ |BW n ω i j - (-I₀ i j)|})
        ≤ ∑ i : Fin 3, ∑ j : Fin 3, P {ω | δB ≤ |BW n ω i j - (-I₀ i j)|} :=
          Finset.sum_le_sum fun i _ => measure_iUnion_fintype_le P _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (η / 22) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hBWn i j
      _ = 9 * (η / 22) := by simp; ring
  have hle22 : (η / 22 + η / 22) + ((η / 22 + η / 22) + (9 * (η / 22) + 9 * (η / 22))) = η := by
    have hsum : (η / 22 + η / 22) + ((η / 22 + η / 22) + (9 * (η / 22) + 9 * (η / 22))) = 22 * (η / 22) := by
      ring
    rw [hsum, mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  refine (measure_mono hsub).trans ?_
  have hm := (measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans (add_le_add hMTn h1))
    ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add h2 h3))
      ((measure_union_le _ _).trans (add_le_add hB_sum hBW_sum)))))
  exact hm.trans hle22.le

set_option maxHeartbeats 400000 in
/-- **Wilks' theorem for the three-parameter GEV local MLE at the Gumbel boundary `ξ₀ = 0`**
([Coles, §2.6.5]; [Smith 1985]), in the library's `(ξ, μ, σ)` parameter order:
`2 (ℓₙ(θ̂ₙ) - ℓₙ(0, μ₀, σ₀)) ⇒ χ²₃`. -/
theorem tendstoInDistribution_gevLocalDeviance_zero (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : TendstoInMeasure P θh atTop (fun _ => ((0 : ℝ), μ₀, σ₀)))
    (hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).1| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0))
    (hloc : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω)})
      atTop (𝓝 0))
    {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 3) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        2 * (gevLogLikN (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (fun i => X i ω) n -
          gevLogLikN 0 μ₀ σ₀ (fun i => X i ω) n))
      atTop Z (fun _ => P) P' := by
  let sw : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p => (p.2.1, p.2.2, p.1)
  have hsw_cont : Continuous sw := by unfold sw; fun_prop
  set θh' : ℕ → Ω → ℝ × ℝ × ℝ := fun n ω => sw (θh n ω)
  have hθ'm : ∀ n, AEMeasurable (θh' n) P := fun n => hsw_cont.measurable.comp_aemeasurable (hθm n)
  have hcons' : TendstoInMeasure P θh' atTop (fun _ => (μ₀, σ₀, (0 : ℝ))) :=
    hcons.comp_continuousAt hsw_cont.continuousAt
  have hloc' : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.2.2 p.1 p.2.1 (fun i : Fin n => X i ω)) (θh' n ω)})
      atTop (𝓝 0) := by
    refine hloc.congr fun n => ?_; congr 1; ext ω
    simp only [mem_ofPred_eq, not_iff_not]
    constructor
    · intro h
      have hsw_inv : Continuous (fun p : ℝ × ℝ × ℝ => (p.2.2, p.1, p.2.1)) := by fun_prop
      have h' : IsLocalMax (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω))
          ((θh' n ω).2.2, (θh' n ω).1, (θh' n ω).2.1) := by simpa [θh', sw] using h
      exact (hsw_inv.continuousAt.tendsto.eventually h').mono fun p hp => hp
    · intro h
      exact (hsw_cont.continuousAt.tendsto.eventually h).mono fun p hp => by simpa [sw] using hp
  have hsub := tendstoInMeasure_gevLocalDeviance_zero_sub_muSigmaXi hσ₀ hX hind hθ'm hcons' hξmax hloc'
  set I₀ := gevFisherInfoZero σ₀
  have hI₀pos : I₀.PosDef := posDef_gevFisherInfoZero hσ₀
  have hW : HasLaw (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (multivariateGaussian 0 I₀) (multivariateGaussian 0 I₀) := HasLaw.id
  have hscore := tendstoInDistribution_gumbelScoreVec3 hσ₀ hX hind hW
  let q : EuclideanSpace ℝ (Fin 3) → ℝ := fun v => v.ofLp ⬝ᵥ I₀⁻¹ *ᵥ v.ofLp
  have hq_cont : Continuous q := by
    unfold q; simp only [dotProduct, Matrix.mulVec]
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul
        (continuous_finsetSum _ fun j _ =>
          continuous_const.mul ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _)))
  have hqLaw : HasLaw (q ∘ id) (chiSquared 3) (multivariateGaussian 0 I₀) :=
    hasLaw_dotProduct_inv_mulVec_chiSquared hI₀pos hW
  have hquad_clt := tendstoInDistribution_congr_limit (hscore.continuous_comp hq_cont) hqLaw hZ
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX i).aemeasurable
  have hDm : ∀ n, AEMeasurable (fun ω =>
      2 * (gevLogLikN (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (fun i => X i ω) n -
        gevLogLikN 0 μ₀ σ₀ (fun i => X i ω) n)) P := fun n =>
    ((aemeasurable_gevLogLikN hXm (hθm n) n).sub
      (aemeasurable_gevLogLikN hXm (θ := fun _ => (0, μ₀, σ₀)) aemeasurable_const n)).const_mul 2
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ Z hquad_clt hsub hDm

/-- **Asymptotic coverage of the local-MLE deviance set at the Gumbel boundary `ξ₀ = 0`**:
`P(2 (ℓₙ(θ̂ₙ) - ℓₙ(0, μ₀, σ₀)) ≤ c) → χ²₃((-∞, c])`. -/
theorem tendsto_measure_mem_gevLocalDeviance_zero (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : TendstoInMeasure P θh atTop (fun _ => ((0 : ℝ), μ₀, σ₀)))
    (hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).1| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0))
    (hloc : Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
      (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω)) (θh n ω)})
      atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun n : ℕ => P {ω |
        2 * (gevLogLikN (θh n ω).1 (θh n ω).2.1 (θh n ω).2.2 (fun i => X i ω) n -
          gevLogLikN 0 μ₀ σ₀ (fun i => X i ω) n) ≤ c})
      atTop (𝓝 (chiSquared 3 (Iic c))) :=
  (tendstoInDistribution_gevLocalDeviance_zero hσ₀ hX hind hθm hcons hξmax hloc
    (Z := id) (P' := chiSquared 3) HasLaw.id).tendsto_measure_le_of_noAtoms HasLaw.id c

/-- **Unconditional Wilks' theorem at the Gumbel boundary `ξ₀ = 0`**: given a compact
`K₂ ⊂ ℝ × (0, ∞)` with `(μ₀, σ₀) ∈ interior K₂`, there exists a data-driven measurable estimator
`gₙ : ℝⁿ → ℝ³` (independent of `(μ₀, σ₀)`) which with probability tending to `1` is a genuine
local maximizer of `gevLogLikE` and satisfies `2 (ℓₙ(gₙ(X)) - ℓₙ(0, μ₀, σ₀)) ⇒ χ²₃` and
`P(2 (ℓₙ(gₙ(X)) - ℓₙ(0, μ₀, σ₀)) ≤ c) → χ²₃((-∞, c])`. -/
theorem exists_gevLocalMLE_deviance_tendstoInDistribution_zero {K₂ : Set (ℝ × ℝ)}
    (hK₂ : IsCompact K₂) (hKS₂ : ∀ p ∈ K₂, 0 < p.2) (hθ₀ : (μ₀, σ₀) ∈ interior K₂)
    (hσ₀ : 0 < σ₀) (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF 0 μ₀ hσ₀).measure P)
    (hind : iIndepFun X P) {Z : Ω' → ℝ} (hZ : HasLaw Z (chiSquared 3) P') :
    ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ × ℝ, (∀ n, Measurable (g n)) ∧
      Tendsto (fun n : ℕ => P {ω | ¬ IsLocalMax
        (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 (fun i : Fin n => X i ω))
        (g n (fun i : Fin n => X i ω))}) atTop (𝓝 0) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          2 * (gevLogLikN (g n (fun i : Fin n => X i ω)).1 (g n (fun i : Fin n => X i ω)).2.1
              (g n (fun i : Fin n => X i ω)).2.2 (fun i => X i ω) n -
            gevLogLikN 0 μ₀ σ₀ (fun i => X i ω) n))
        atTop Z (fun _ => P) P' := by
  obtain ⟨g, hgm, hloc, hclt⟩ := exists_gevLocalMLE_tendstoInDistribution_zero
    hK₂ hKS₂ hθ₀ hσ₀ hX hind (W := id) (P' := multivariateGaussian 0 (gevMLECovZero σ₀)) HasLaw.id
  set θh : ℕ → Ω → ℝ × ℝ × ℝ := fun n ω => g n (fun i : Fin n => X i ω)
  have hθm : ∀ n, AEMeasurable (θh n) P := fun n =>
    (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i => (hX i).aemeasurable)
  have hT_bd : IsBoundedInProbability P
      (fun n ω => ‖√(n : ℝ) • !₂[(θh n ω).1, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀]‖) :=
    isBoundedInProbability_of_tendstoInDistribution (hclt.continuous_comp continuous_norm)
  have hcons : TendstoInMeasure P θh atTop (fun _ => ((0 : ℝ), μ₀, σ₀)) := by
    have hinv : TendstoInMeasure P (fun (n : ℕ) (_ : Ω) => (√(n : ℝ))⁻¹) atTop (fun _ => 0) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ fun _ =>
        tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
    have hprod := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hT_bd hinv
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hp := (tendstoInMeasure_iff_norm.1 hprod) ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hsq0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
    set v : EuclideanSpace ℝ (Fin 3) := !₂[(θh n ω).1, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀]
    have hdist_le : dist (θh n ω) ((0 : ℝ), μ₀, σ₀) ≤ ‖v‖ := by
      have h0 : |(θh n ω).1| ≤ ‖v‖ := by simpa [v, Real.norm_eq_abs] using PiLp.norm_apply_le v 0
      have h1 : |(θh n ω).2.1 - μ₀| ≤ ‖v‖ := by simpa [v, Real.norm_eq_abs] using PiLp.norm_apply_le v 1
      have h2 : |(θh n ω).2.2 - σ₀| ≤ ‖v‖ := by simpa [v, Real.norm_eq_abs] using PiLp.norm_apply_le v 2
      simp only [Prod.dist_eq, Real.dist_eq, sub_zero, max_le_iff]
      exact ⟨h0, h1, h2⟩
    have heq : |(√(n : ℝ))⁻¹ * ‖√(n : ℝ) • v‖| = ‖v‖ := by
      rw [norm_smul, Real.norm_of_nonneg hsq0.le, abs_of_nonneg (by positivity),
        ← mul_assoc, inv_mul_cancel₀ hsq0.ne', one_mul]
    rw [heq]; exact hω.trans hdist_le
  have hξmax : TendstoInMeasure P
      (fun (n : ℕ) ω => |(θh n ω).1| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n)
      atTop (fun _ => 0) := by
    have hrm := tendstoInMeasure_runMax_abs_gumbel_div_rpow hσ₀ (show (0 : ℝ) < 1 / 2 by norm_num) hX
    have hprod := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hT_bd hrm
    rw [tendstoInMeasure_iff_norm] at hprod ⊢
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hprod ε hε)
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
    have hnn1 : 0 ≤ |(θh n ω).1| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n :=
      mul_nonneg (abs_nonneg _) (runMax_nonneg _ _)
    have hnn2 : 0 ≤ (runMax (fun i => |(X i ω - μ₀) / σ₀|) n / (n : ℝ) ^ (1 / 2 : ℝ)) *
        ‖√(n : ℝ) • !₂[(θh n ω).1, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀]‖ := by
      have : 0 ≤ runMax (fun i => |(X i ω - μ₀) / σ₀|) n / (n : ℝ) ^ (1 / 2 : ℝ) :=
        div_nonneg (runMax_nonneg _ _) (rpow_nonneg hn0.le _)
      positivity
    rw [abs_of_nonneg hnn1] at hω
    rw [abs_of_nonneg hnn2]
    have h0 : √(n : ℝ) * |(θh n ω).1| ≤
        ‖√(n : ℝ) • !₂[(θh n ω).1, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀]‖ := by
      have := PiLp.norm_apply_le (√(n : ℝ) • !₂[(θh n ω).1, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀]) 0
      simpa [Real.norm_eq_abs, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hsq0] using this
    have hrpow : (n : ℝ) ^ (1 / 2 : ℝ) = √(n : ℝ) := (Real.sqrt_eq_rpow (n : ℝ)).symm
    rw [hrpow]
    calc ε ≤ |(θh n ω).1| * runMax (fun i => |(X i ω - μ₀) / σ₀|) n := hω
      _ = (runMax (fun i => |(X i ω - μ₀) / σ₀|) n / √(n : ℝ)) * (√(n : ℝ) * |(θh n ω).1|) := by
          field_simp [hsq0.ne']
      _ ≤ (runMax (fun i => |(X i ω - μ₀) / σ₀|) n / √(n : ℝ)) *
            ‖√(n : ℝ) • !₂[(θh n ω).1, (θh n ω).2.1 - μ₀, (θh n ω).2.2 - σ₀]‖ :=
          mul_le_mul_of_nonneg_left h0 (div_nonneg (runMax_nonneg _ _) hsq0.le)
  exact ⟨g, hgm, hloc, tendstoInDistribution_gevLocalDeviance_zero hσ₀ hX hind hθm hcons hξmax hloc hZ⟩

end GumbelBoundary

end ExtremeValueTheory
