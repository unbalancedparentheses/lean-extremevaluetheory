/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ForMathlib.Probability.TriangularArrayCLT
import Mathlib.Probability.BrownianMotion.Basic

/-!
# The uniform tail empirical process

Let `U 0, U 1, …` be i.i.d. uniform on `[0, 1]` and let `k = k n` be an intermediate sequence,
`k → ∞`, `k / n → 0`. The **uniform tail empirical process** is
`W_n(t) = √k ((1/k) ∑_{i < n} 1{U_i ≥ 1 - (k/n) t} - t)`, `t ≥ 0`:
it counts the `k t` expected exceedances of the high level `1 - (k/n) t` and centers and scales
the count. (We use the non-strict inequality `U_i ≥ 1 - (k/n) t` so that the paths
`t ↦ W_n(t)` are càdlàg; for every fixed `t` this differs from `U_i > 1 - (k/n) t` only on a
null event.)

We prove that the finite-dimensional distributions of `W_n` converge to those of a standard
Brownian motion ([de Haan–Ferreira, *Extreme Value Theory*, Theorem 2.4.8 / 5.1.4];
[Einmahl 1992]): for every finite set of times `I`, the vector `(W_n(t))_{t ∈ I}` converges in
distribution to the centered Gaussian vector with covariance `min s t`, i.e. to
`ProbabilityTheory.BrownianReal.projectiveFamily I`.

The proof is the Cramér–Wold device together with a central limit theorem for triangular arrays
with uniformly small summands (`ProbabilityTheory.tendsto_charFun_sum_range_of_bounded`): a linear
combination `∑_{t ∈ I} a_t W_n(t)` is the row sum `∑_{i < n} f_n(U_i)` with
`f_n(u) = k^{-1/2} ∑_t a_t (1{u ≥ 1 - (k/n) t} - (k/n) t)`, which is centered, bounded by
`O(k^{-1/2})`, and has `n ∫ f_n ^ 2 = ∑_{s, t} a_s a_t (min s t - (k/n) s t) → ∑ a_s a_t min s t`.

## Main definitions

* `ExtremeValueTheory.tailEmpiricalProcess U n k t ω`: the uniform tail empirical process.

## Main statements

* `ExtremeValueTheory.tendstoInDistribution_tailEmpiricalProcess_fdd`: convergence of the
  finite-dimensional distributions to `BrownianReal.projectiveFamily I`.
* `ExtremeValueTheory.tendstoInDistribution_tailEmpiricalProcess_fdd_of_isPreBrownianReal`: the
  same statement with the limit given by a (pre-)Brownian motion.

## References

* [L. de Haan, A. Ferreira, *Extreme Value Theory: An Introduction*], Theorems 2.4.8 and 5.1.4
* [J. H. J. Einmahl, *Limit theorems for tail processes with application to intermediate quantile
  estimation*, J. Statist. Plann. Inference 32 (1992)]
* [H. Drees, *On smooth statistical tail functionals*, Scand. J. Statist. 25 (1998)]
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology Complex
open scoped ENNReal NNReal Real

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The **uniform tail empirical process**
`W_n(t) = √k ((1/k) ∑_{i < n} 1{U_i ≥ 1 - (k/n) t} - t)`. -/
noncomputable def tailEmpiricalProcess (U : ℕ → Ω → ℝ) (n k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  √k * ((k : ℝ)⁻¹ * ∑ i ∈ range n, (Set.Ici (1 - k / n * t)).indicator 1 (U i ω) - t)

/-- The uniform law on `[0, 1]`. -/
noncomputable abbrev μU : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure μU := ⟨by simp⟩

lemma measureReal_uniform_Ici {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    μU.real (Set.Ici (1 - x)) = x := by
  have e : Set.Ici (1 - x) ∩ Set.Icc 0 1 = Set.Icc (1 - x) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ici, e, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

lemma integral_uniform_indicator_Ici {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ u, (Set.Ici (1 - x)).indicator (1 : ℝ → ℝ) u ∂μU = x := by
  rw [integral_indicator_one measurableSet_Ici, measureReal_uniform_Ici hx0 hx1]

lemma indicator_Ici_mul_indicator_Ici (x y u : ℝ) :
    (Set.Ici x).indicator (1 : ℝ → ℝ) u * (Set.Ici y).indicator 1 u =
      (Set.Ici (max x y)).indicator 1 u := by
  simp only [Set.indicator, Set.mem_Ici, max_le_iff, Pi.one_apply]
  split_ifs <;> simp_all

/-- The summand of the row sum representing the linear combination `∑_t a_t W_n(t)`. -/
noncomputable def tailSummand {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ) (n k : ℕ) (u : ℝ) : ℝ :=
  (√k)⁻¹ * ∑ t : ι, a t * ((Set.Ici (1 - k / n * (τ t : ℝ))).indicator 1 u - k / n * τ t)

lemma measurable_tailSummand {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ) (n k : ℕ) :
    Measurable (tailSummand τ a n k) := by
  unfold tailSummand
  refine Measurable.const_mul (Finset.measurable_sum _ fun t _ ↦ ?_) _
  exact ((measurable_one.indicator measurableSet_Ici).sub_const _).const_mul _

lemma sqrt_mul_inv_sub_eq {n k : ℕ} (hn : n ≠ 0) (S t : ℝ) :
    √(k : ℝ) * ((k : ℝ)⁻¹ * S - t) = (√(k : ℝ))⁻¹ * (S - n * (k / n * t)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hs : √(k : ℝ) ≠ 0 := (Real.sqrt_pos.2 hk').ne'
  have hsq : √(k : ℝ) ^ 2 = k := Real.sq_sqrt hk'.le
  field_simp
  rw [hsq]

lemma sum_mul_tailEmpiricalProcess_eq {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ) (U : ℕ → Ω → ℝ) {n : ℕ}
    (hn : n ≠ 0) (k : ℕ) (ω : Ω) :
    ∑ t : ι, a t * tailEmpiricalProcess U n k (τ t) ω = ∑ i ∈ range n, tailSummand τ a n k (U i ω) := by
  unfold tailEmpiricalProcess tailSummand
  simp_rw [sqrt_mul_inv_sub_eq hn]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

lemma integrable_uniform_indicator_Ici (x : ℝ) :
    Integrable ((Set.Ici x).indicator (1 : ℝ → ℝ)) μU :=
  (integrable_const (1 : ℝ)).indicator measurableSet_Ici

lemma integral_uniform_indicator_sub_mul {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) :
    ∫ u, ((Set.Ici (1 - x)).indicator 1 u - x) * ((Set.Ici (1 - y)).indicator 1 u - y) ∂μU =
      min x y - x * y := by
  have e : (fun u ↦ ((Set.Ici (1 - x)).indicator (1 : ℝ → ℝ) u - x) *
      ((Set.Ici (1 - y)).indicator 1 u - y)) = fun u ↦
      (Set.Ici (1 - min x y)).indicator 1 u - (y * (Set.Ici (1 - x)).indicator 1 u +
        x * (Set.Ici (1 - y)).indicator 1 u) + x * y := by
    ext u
    have := indicator_Ici_mul_indicator_Ici (1 - x) (1 - y) u
    rw [max_sub_sub_left] at this
    rw [← this]
    ring
  have i0 := integrable_uniform_indicator_Ici (1 - min x y)
  have ix := integrable_uniform_indicator_Ici (1 - x)
  have iy := integrable_uniform_indicator_Ici (1 - y)
  rw [e, integral_add (by exact i0.sub ((ix.const_mul _).add (iy.const_mul _)))
      (integrable_const _),
    integral_sub (by exact i0) (by exact (ix.const_mul _).add (iy.const_mul _)),
    integral_add (by exact ix.const_mul _) (by exact iy.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_uniform_indicator_Ici (le_min hx0 hy0) ((min_le_left _ _).trans hx1),
    integral_uniform_indicator_Ici hx0 hx1, integral_uniform_indicator_Ici hy0 hy1]
  simp only [integral_const, probReal_univ, one_smul]
  ring

lemma integral_tailSummand {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ) {n k : ℕ}
    (hp : ∀ t : ι, (k : ℝ) / n * τ t ≤ 1) : ∫ u, tailSummand τ a n k u ∂μU = 0 := by
  unfold tailSummand
  rw [integral_const_mul, integral_finsetSum _ fun t _ ↦ by
    exact ((integrable_uniform_indicator_Ici _).sub (integrable_const _)).const_mul _]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ ↦ ?_)
  rw [integral_const_mul, integral_sub (integrable_uniform_indicator_Ici _) (integrable_const _),
    integral_uniform_indicator_Ici (by positivity) (hp t)]
  simp

lemma abs_tailSummand_le {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ) (n k : ℕ) (u : ℝ) :
    |tailSummand τ a n k u| ≤ (√(k : ℝ))⁻¹ * ∑ t : ι, |a t| * (1 + k / n * τ t) := by
  unfold tailSummand
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun t _ ↦ ?_)) (by positivity)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _)
  · by_cases h : u ∈ Set.Ici (1 - k / n * (τ t : ℝ)) <;> simp [h]
  · rw [abs_of_nonneg (by positivity)]

lemma mul_integral_tailSummand_sq {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ) {n k : ℕ} (hn : n ≠ 0)
    (hk : k ≠ 0) (hp : ∀ t : ι, (k : ℝ) / n * τ t ≤ 1) :
    n * ∫ u, tailSummand τ a n k u ^ 2 ∂μU =
      ∑ t : ι, ∑ s : ι, a t * a s * (min (τ t : ℝ) (τ s) - k / n * τ t * τ s) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hp0 : (0 : ℝ) ≤ k / n := by positivity
  set g : ι → ℝ → ℝ := fun t u ↦ (Set.Ici (1 - k / n * (τ t : ℝ))).indicator 1 u - k / n * τ t
  have hg (t : ι) : Integrable (g t) μU :=
    (integrable_uniform_indicator_Ici _).sub (integrable_const _)
  have hsq (u : ℝ) : tailSummand τ a n k u ^ 2 =
      (k : ℝ)⁻¹ * ∑ t : ι, ∑ s : ι, a t * a s * (g t u * g s u) := by
    unfold tailSummand
    rw [mul_pow, inv_pow, Real.sq_sqrt hk'.le, sq, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
    ring
  simp_rw [hsq]
  have hint (t s : ι) : Integrable (fun u ↦ a t * a s * (g t u * g s u)) μU := by
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound (C := (1 + k / n * τ t) * (1 + k / n * τ s))
      ((hg t).aestronglyMeasurable.mul (hg s).aestronglyMeasurable) (ae_of_all _ fun u ↦ ?_)
    rw [norm_mul]
    have hb (r : ι) : ‖g r u‖ ≤ 1 + k / n * τ r := by
      simp only [g, Real.norm_eq_abs]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · by_cases h : u ∈ Set.Ici (1 - k / n * (τ r : ℝ)) <;> simp [h]
      · rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (hb t) (hb s) (norm_nonneg _) (by positivity)
  rw [integral_const_mul, integral_finsetSum _ fun t _ ↦ integrable_finsetSum _ fun s _ ↦
    hint t s]
  simp_rw [integral_finsetSum _ fun s _ ↦ hint _ s, integral_const_mul]
  rw [← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have := integral_uniform_indicator_sub_mul (x := k / n * τ t) (y := k / n * τ s) (by positivity)
    (hp t) (by positivity) (hp s)
  simp only [g]
  rw [this, ← mul_min_of_nonneg _ _ hp0]
  field_simp

lemma measurable_tailEmpiricalProcess {U : ℕ → Ω → ℝ} (hU : ∀ i, Measurable (U i)) (n k : ℕ)
    (t : ℝ) : Measurable (tailEmpiricalProcess U n k t) := by
  unfold tailEmpiricalProcess
  refine Measurable.const_mul (Measurable.sub_const (Measurable.const_mul
    (Finset.measurable_sum _ fun i _ ↦ ?_) _) _) _
  exact (measurable_one.indicator measurableSet_Ici).comp (hU i)

variable {U : ℕ → Ω → ℝ} {k : ℕ → ℕ}

/-- The characteristic functions of the linear combinations `∑_t a_t W_n(t)` converge to the
characteristic function of the centered Gaussian law with variance `∑_{s,t} a_s a_t min s t`. -/
theorem tendsto_charFun_sum_mul_tailEmpiricalProcess (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U P) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ) (s : ℝ) :
    Tendsto (fun n ↦ charFun (P.map (fun ω ↦ ∑ t : ι, a t *
        tailEmpiricalProcess U n (k n) (τ t) ω)) s) atTop
      (𝓝 (cexp (-((s : ℂ) ^ 2 * (∑ t : ι, ∑ r : ι, a t * a r * min (τ t : ℝ) (τ r) : ℝ) / 2)))) := by
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  -- eventually all the levels `(k/n) t` lie in `[0, 1]`, and `n, k n ≠ 0`
  have hp : ∀ᶠ n in atTop, ∀ t : ι, (k n : ℝ) / n * τ t ≤ 1 := by
    rw [eventually_all]
    intro t
    have : Tendsto (fun n ↦ (k n : ℝ) / n * τ t) atTop (𝓝 (0 * τ t)) := hkn.mul_const _
    rw [zero_mul] at this
    exact this.eventually (ge_mem_nhds zero_lt_one)
  have hn0 : ∀ᶠ n : ℕ in atTop, n ≠ 0 := eventually_ne_atTop 0
  have hk0 : ∀ᶠ n in atTop, k n ≠ 0 := hk.eventually_ne_atTop 0
  -- the bound on the summands
  set M : ℕ → ℝ := fun n ↦ (√(k n : ℝ))⁻¹ * ∑ t : ι, |a t| * (1 + k n / n * τ t) with hM
  have hMlim : Tendsto M atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ (√(k n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hkR)
    have h2 : Tendsto (fun n ↦ ∑ t : ι, |a t| * (1 + k n / n * τ t)) atTop
        (𝓝 (∑ t : ι, |a t| * (1 + 0 * τ t))) :=
      tendsto_finsetSum _ fun t _ ↦ ((hkn.mul_const _).const_add _).const_mul _
    have := h1.mul h2
    rw [zero_mul] at this
    exact this
  have hvar : Tendsto (fun n : ℕ ↦ n * ∫ u, tailSummand τ a n (k n) u ^ 2 ∂μU) atTop
      (𝓝 (∑ t : ι, ∑ r : ι, a t * a r * min (τ t : ℝ) (τ r))) := by
    have hlim : Tendsto (fun n ↦ ∑ t : ι, ∑ r : ι, a t * a r * (min (τ t : ℝ) (τ r) - k n / n * τ t * τ r))
        atTop (𝓝 (∑ t : ι, ∑ r : ι, a t * a r * (min (τ t : ℝ) (τ r) - 0 * τ t * τ r))) :=
      tendsto_finsetSum _ fun t _ ↦ tendsto_finsetSum _ fun r _ ↦
        (tendsto_const_nhds.sub ((hkn.mul_const _).mul_const _)).const_mul _
    simp only [zero_mul, sub_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [hp, hn0, hk0] with n hpn hn hkn'
    exact (mul_integral_tailSummand_sq τ a hn hkn' hpn).symm
  have key := tendsto_charFun_sum_range_of_bounded hU hind hlaw (μ := μU)
    (f := fun n ↦ tailSummand τ a n (k n)) (fun n ↦ measurable_tailSummand τ a n (k n)) hMlim
    (fun n u ↦ abs_tailSummand_le τ a n (k n) u)
    (by filter_upwards [hp] with n hpn; exact integral_tailSummand τ a hpn) hvar s
  refine key.congr' ?_
  filter_upwards [hn0] with n hn
  congr 2
  ext ω
  exact (sum_mul_tailEmpiricalProcess_eq τ a U hn (k n) ω).symm

/-- **Finite-dimensional convergence of the uniform tail empirical process** to Brownian motion
([de Haan–Ferreira, Theorem 2.4.8]; [Einmahl 1992]). If `U 0, U 1, …` are i.i.d. uniform on
`[0, 1]`, `k n → ∞` and `k n / n → 0`, then for every finite set of times `I`, the vector
`(W_n(t))_{t ∈ I}` converges in distribution to the centered Gaussian vector with covariance
`min s t`, the finite-dimensional law `BrownianReal.projectiveFamily I` of Brownian motion. -/
theorem tendstoInDistribution_tailEmpiricalProcess_fdd [IsProbabilityMeasure P]
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    (I : Finset ℝ≥0) :
    TendstoInDistribution (fun n ω ↦ fun t : I ↦ tailEmpiricalProcess U n (k n) t ω) atTop id
      (fun _ ↦ P) (BrownianReal.projectiveFamily I) := by
  set V : ℕ → Ω → EuclideanSpace ℝ I :=
    fun n ω ↦ WithLp.toLp 2 (fun t : I ↦ tailEmpiricalProcess U n (k n) t ω) with hV
  have hVm (n : ℕ) : Measurable (V n) :=
    (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 fun t ↦ measurable_tailEmpiricalProcess hU n (k n) t)
  have hconv : TendstoInDistribution V atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (BrownianReal.covMatrix I)) := by
    refine .of_tendsto_charFun (fun n ↦ (hVm n).aemeasurable) aemeasurable_id fun a ↦ ?_
    rw [Measure.map_id, charFun_multivariateGaussian (BrownianReal.posSemidef_covMatrix I)]
    simp_rw [charFun_map_eq_charFun_map_inner_one (hVm _).aemeasurable a]
    have hinner (n : ℕ) (ω : Ω) :
        inner ℝ (V n ω) a = ∑ t : I, a t * tailEmpiricalProcess U n (k n) t ω := by
      simp [hV, PiLp.inner_apply, mul_comm]
    simp_rw [hinner]
    convert tendsto_charFun_sum_mul_tailEmpiricalProcess hU hind hlaw hk hkn (fun t : I ↦ (t : ℝ≥0))
      (fun t ↦ a t) 1
      using 2
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    congr 3
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
    ring
  have hcomp := hconv.continuous_comp (PiLp.continuous_ofLp 2 _)
  refine ⟨fun n ↦ (measurable_pi_iff.2 fun t : I ↦
    measurable_tailEmpiricalProcess hU n (k n) t).aemeasurable, aemeasurable_id, ?_⟩
  have h := hcomp.tendsto
  simp only [Function.comp_id, (BrownianReal.measurePreserving_ofLp_multivariateGaussian I).map_eq]
    at h
  simp only [Measure.map_id]
  exact h

/-- The covariance matrix `min (τ i) (τ j)` of Brownian motion at the times `τ i`. -/
def brownianCovMatrix {ι : Type*} (τ : ι → ℝ≥0) : Matrix ι ι ℝ :=
  .of fun i j ↦ min (τ i : ℝ) (τ j)

lemma posSemidef_brownianCovMatrix {ι : Type*} [Finite ι] (τ : ι → ℝ≥0) :
    (brownianCovMatrix τ).PosSemidef := by
  have : brownianCovMatrix τ = .of fun i j ↦ volume.real (Set.Icc 0 (τ i : ℝ) ∩
      Set.Icc 0 (τ j : ℝ)) := by
    ext i j
    simp [brownianCovMatrix, Set.Icc_inter_Icc]
  rw [this]
  exact posSemidef_matrix_measure_inter (fun _ ↦ measurableSet_Icc)
    (fun j ↦ by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

/-- The law of Brownian motion at the times `τ i` (`i : ι`, possibly repeated): the centered
Gaussian vector with covariance `min (τ i) (τ j)`. -/
noncomputable def brownianFdd {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ≥0) :
    Measure (ι → ℝ) :=
  (multivariateGaussian 0 (brownianCovMatrix τ)).map WithLp.ofLp

instance {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ≥0) :
    IsProbabilityMeasure (brownianFdd τ) :=
  ⟨by rw [brownianFdd, Measure.map_apply (by fun_prop) MeasurableSet.univ]; simp⟩

/-- **Finite-dimensional convergence of the uniform tail empirical process**, for an arbitrary
finite family of times `τ i`: `(W_n(τ i))_i` converges in distribution to `brownianFdd τ`. -/
theorem tendstoInDistribution_tailEmpiricalProcess_comp [IsProbabilityMeasure P]
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ι → ℝ≥0) :
    TendstoInDistribution (fun n ω ↦ fun i : ι ↦ tailEmpiricalProcess U n (k n) (τ i) ω) atTop
      id (fun _ ↦ P) (brownianFdd τ) := by
  set V : ℕ → Ω → EuclideanSpace ℝ ι :=
    fun n ω ↦ WithLp.toLp 2 (fun i : ι ↦ tailEmpiricalProcess U n (k n) (τ i) ω) with hV
  have hVm (n : ℕ) : Measurable (V n) :=
    (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 fun i ↦ measurable_tailEmpiricalProcess hU n (k n) _)
  have hconv : TendstoInDistribution V atTop id (fun _ ↦ P)
      (multivariateGaussian 0 (brownianCovMatrix τ)) := by
    refine .of_tendsto_charFun (fun n ↦ (hVm n).aemeasurable) aemeasurable_id fun a ↦ ?_
    rw [Measure.map_id, charFun_multivariateGaussian (posSemidef_brownianCovMatrix τ)]
    simp_rw [charFun_map_eq_charFun_map_inner_one (hVm _).aemeasurable a]
    have hinner (n : ℕ) (ω : Ω) :
        inner ℝ (V n ω) a = ∑ i : ι, a i * tailEmpiricalProcess U n (k n) (τ i) ω := by
      simp [hV, PiLp.inner_apply, mul_comm]
    simp_rw [hinner]
    convert tendsto_charFun_sum_mul_tailEmpiricalProcess hU hind hlaw hk hkn τ
      (fun i ↦ a i) 1 using 2
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, brownianCovMatrix]
    congr 3
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
    ring
  have hcomp := hconv.continuous_comp (PiLp.continuous_ofLp 2 _)
  refine ⟨fun n ↦ (measurable_pi_iff.2 fun i : ι ↦
    measurable_tailEmpiricalProcess hU n (k n) _).aemeasurable, aemeasurable_id, ?_⟩
  have h := hcomp.tendsto
  simp only [Function.comp_id] at h
  simp only [Measure.map_id, brownianFdd]
  exact h

/-- **Finite-dimensional convergence of the uniform tail empirical process to a Brownian
motion**: for a pre-Brownian motion `B` (a process with the finite-dimensional laws of Brownian
motion) and every finite set of times `I`, `(W_n(t))_{t ∈ I}` converges in distribution to
`(B t)_{t ∈ I}`. -/
theorem tendstoInDistribution_tailEmpiricalProcess_fdd_of_isPreBrownianReal
    [IsProbabilityMeasure P] {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ} (hB : IsPreBrownianReal B P')
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    (I : Finset ℝ≥0) :
    TendstoInDistribution (fun n ω ↦ fun t : I ↦ tailEmpiricalProcess U n (k n) t ω) atTop
      (fun ω ↦ I.restrict (B · ω)) (fun _ ↦ P) P' := by
  have h := tendstoInDistribution_tailEmpiricalProcess_fdd hU hind hlaw hk hkn I
  refine ⟨h.forall_aemeasurable, (hB.hasLaw I).aemeasurable, ?_⟩
  have h' := h.tendsto
  simp only [Measure.map_id] at h'
  simp only [(hB.hasLaw I).map_eq]
  exact h'

end ExtremeValueTheory
