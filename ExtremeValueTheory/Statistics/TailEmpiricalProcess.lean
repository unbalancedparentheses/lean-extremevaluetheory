/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ForMathlib.Probability.TriangularArrayCLT
import ExtremeValueTheory.ForMathlib.Probability.FourthMoment
import ExtremeValueTheory.ForMathlib.Probability.DyadicChaining
import ExtremeValueTheory.ForMathlib.Probability.SkorokhodBlockTightness
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
noncomputable def tailSummand {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ) (n k : ℕ)
    (u : ℝ) : ℝ :=
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

lemma sum_mul_tailEmpiricalProcess_eq {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ)
    (U : ℕ → Ω → ℝ) {n : ℕ}
    (hn : n ≠ 0) (k : ℕ) (ω : Ω) :
    ∑ t : ι, a t * tailEmpiricalProcess U n k (τ t) ω =
      ∑ i ∈ range n, tailSummand τ a n k (U i ω) := by
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

lemma mul_integral_tailSummand_sq {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (a : ι → ℝ) {n k : ℕ}
    (hn : n ≠ 0)
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
      (𝓝 (cexp (-((s : ℂ) ^ 2 *
        (∑ t : ι, ∑ r : ι, a t * a r * min (τ t : ℝ) (τ r) : ℝ) / 2)))) := by
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
    have hlim : Tendsto (fun n ↦ ∑ t : ι, ∑ r : ι,
        a t * a r * (min (τ t : ℝ) (τ r) - k n / n * τ t * τ r))
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

instance isProbabilityMeasure_brownianFdd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ≥0) : IsProbabilityMeasure (brownianFdd τ) :=
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

/-! ### Moments of the increments -/

/-- The summand of the row sum representing an increment `W_n(t) - W_n(s)`. -/
noncomputable def tailIncrement (n k : ℕ) (s t u : ℝ) : ℝ :=
  (√(k : ℝ))⁻¹ * ((Set.Ici (1 - k / n * t)).indicator 1 u -
    (Set.Ici (1 - k / n * s)).indicator 1 u - k / n * (t - s))

lemma measurable_tailIncrement (n k : ℕ) (s t : ℝ) : Measurable (tailIncrement n k s t) := by
  unfold tailIncrement
  refine Measurable.const_mul (Measurable.sub_const (Measurable.sub ?_ ?_) _) _ <;>
    exact measurable_one.indicator measurableSet_Ici

lemma tailEmpiricalProcess_sub_eq_sum (U : ℕ → Ω → ℝ) {n : ℕ} (hn : n ≠ 0) (k : ℕ) (s t : ℝ)
    (ω : Ω) : tailEmpiricalProcess U n k t ω - tailEmpiricalProcess U n k s ω =
      ∑ i ∈ range n, tailIncrement n k s t (U i ω) := by
  unfold tailEmpiricalProcess tailIncrement
  rw [sqrt_mul_inv_sub_eq hn, sqrt_mul_inv_sub_eq hn, ← Finset.mul_sum, ← mul_sub]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
  ring

/-- The indicator increment `1{u ≥ 1 - p t} - 1{u ≥ 1 - p s}` lies in `[0, 1]` for `s ≤ t`. -/
lemma indicator_Ici_sub_mem_Icc {p s t : ℝ} (hp : 0 ≤ p) (hst : s ≤ t) (u : ℝ) :
    (Set.Ici (1 - p * t)).indicator (1 : ℝ → ℝ) u - (Set.Ici (1 - p * s)).indicator 1 u ∈
      Set.Icc (0 : ℝ) 1 := by
  have hsub : Set.Ici (1 - p * s) ⊆ Set.Ici (1 - p * t) := Set.Ici_subset_Ici.2 (by nlinarith)
  by_cases h1 : u ∈ Set.Ici (1 - p * s)
  · simp [h1, hsub h1]
  · by_cases h2 : u ∈ Set.Ici (1 - p * t) <;> simp [h1, h2]

lemma abs_tailIncrement_le {n k : ℕ} {s t : ℝ} (hst : s ≤ t) (ht : (k : ℝ) / n * t ≤ 1)
    (hs : 0 ≤ s) (u : ℝ) : |tailIncrement n k s t u| ≤ (√(k : ℝ))⁻¹ := by
  have hp : (0 : ℝ) ≤ k / n := by positivity
  have hD := indicator_Ici_sub_mem_Icc hp hst u
  have hq0 : 0 ≤ (k : ℝ) / n * (t - s) := mul_nonneg hp (by linarith)
  have hq1 : (k : ℝ) / n * (t - s) ≤ 1 := by nlinarith
  unfold tailIncrement
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_of_le_one_right (by positivity) (abs_le.2 ⟨?_, ?_⟩) <;> linarith [hD.1, hD.2]

lemma integral_tailIncrement {n k : ℕ} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : (k : ℝ) / n * t ≤ 1) : ∫ u, tailIncrement n k s t u ∂μU = 0 := by
  have hp : (0 : ℝ) ≤ k / n := by positivity
  unfold tailIncrement
  have i1 := integrable_uniform_indicator_Ici (1 - k / n * t)
  have i2 := integrable_uniform_indicator_Ici (1 - k / n * s)
  rw [integral_const_mul, integral_sub (by exact i1.sub i2) (integrable_const _),
    integral_sub (by exact i1) (by exact i2),
    integral_uniform_indicator_Ici (mul_nonneg hp (hs.trans hst)) ht,
    integral_uniform_indicator_Ici (mul_nonneg hp hs) (by nlinarith)]
  simp only [integral_const, probReal_univ, one_smul]
  ring

lemma integral_tailIncrement_sq_le {n k : ℕ} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : (k : ℝ) / n * t ≤ 1) :
    ∫ u, tailIncrement n k s t u ^ 2 ∂μU ≤ 2 * (k / n * (t - s)) / k := by
  have hp : (0 : ℝ) ≤ k / n := by positivity
  set q : ℝ := k / n * (t - s) with hq
  have hq0 : 0 ≤ q := mul_nonneg hp (by linarith)
  have hq1 : q ≤ 1 := by nlinarith
  set D : ℝ → ℝ := fun u ↦ (Set.Ici (1 - k / n * t)).indicator (1 : ℝ → ℝ) u -
    (Set.Ici (1 - k / n * s)).indicator 1 u with hD
  have hDi : Integrable D μU :=
    (integrable_uniform_indicator_Ici _).sub (integrable_uniform_indicator_Ici _)
  have hbound (u : ℝ) : tailIncrement n k s t u ^ 2 ≤ (k : ℝ)⁻¹ * (D u + q) := by
    have hDu := indicator_Ici_sub_mem_Icc hp hst u
    unfold tailIncrement
    rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    simp only [hD] at hDu ⊢
    nlinarith [hDu.1, hDu.2]
  have hint : Integrable (fun u ↦ (k : ℝ)⁻¹ * (D u + q)) μU :=
    (hDi.add (integrable_const _)).const_mul _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun u ↦ sq_nonneg _) hint
    (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul, integral_add hDi (integrable_const _), hD]
  simp only
  rw [integral_sub (integrable_uniform_indicator_Ici _) (integrable_uniform_indicator_Ici _),
    integral_uniform_indicator_Ici (mul_nonneg hp (hs.trans hst)) ht,
    integral_uniform_indicator_Ici (mul_nonneg hp hs) (by nlinarith)]
  simp only [integral_const, probReal_univ, one_smul, hq]
  ring

/-- **Fourth moment of the increments of the tail empirical process**:
`E (W_n(t) - W_n(s)) ^ 4 ≤ 12 (t - s) ^ 2 + 2 (t - s) / k` for `0 ≤ s ≤ t ≤ n / k`. -/
theorem integral_tailEmpiricalProcess_sub_pow_four_le [IsProbabilityMeasure P]
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ} (hn : n ≠ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : (k : ℝ) / n * t ≤ 1) :
    ∫ ω, (tailEmpiricalProcess U n k t ω - tailEmpiricalProcess U n k s ω) ^ 4 ∂P ≤
      12 * (t - s) ^ 2 + 2 * (t - s) / k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [tailEmpiricalProcess, Nat.cast_zero, Real.sqrt_zero, zero_mul, sub_self]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero,
      div_zero, add_zero]
    positivity
  set X : ℕ → Ω → ℝ := fun i ω ↦ tailIncrement n k s t (U i ω) with hX
  have hXm (i : ℕ) : Measurable (X i) := (measurable_tailIncrement n k s t).comp (hU i)
  have hXind : iIndepFun X P := hind.comp (fun _ ↦ tailIncrement n k s t)
    (fun _ ↦ measurable_tailIncrement n k s t)
  have hXC (i : ℕ) (ω : Ω) : |X i ω| ≤ (√(k : ℝ))⁻¹ := abs_tailIncrement_le hst ht hs _
  have hmap (i : ℕ) (j : ℕ) : ∫ ω, X i ω ^ j ∂P = ∫ u, tailIncrement n k s t u ^ j ∂μU := by
    rw [show μU = P.map (U i) from (hlaw i).symm, integral_map (hU i).aemeasurable (by
      exact ((measurable_tailIncrement n k s t).pow_const j).aestronglyMeasurable)]
  have hX0 (i : ℕ) : ∫ ω, X i ω ∂P = 0 := by
    have := hmap i 1
    simp only [pow_one] at this
    rw [this, integral_tailIncrement hs hst ht]
  have hp : (0 : ℝ) ≤ k / n := by positivity
  have h2 (i : ℕ) : ∫ ω, X i ω ^ 2 ∂P ≤ 2 * (k / n * (t - s)) / k := by
    rw [hmap]; exact integral_tailIncrement_sq_le hs hst ht
  have h4 (i : ℕ) : ∫ ω, X i ω ^ 4 ∂P ≤ (k : ℝ)⁻¹ * (2 * (k / n * (t - s)) / k) := by
    have hle : ∀ ω, X i ω ^ 4 ≤ (k : ℝ)⁻¹ * X i ω ^ 2 := fun ω ↦ by
      have hx := hXC i ω
      have hx2 : X i ω ^ 2 ≤ (k : ℝ)⁻¹ := by
        rw [← Real.sq_sqrt (inv_nonneg.2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)), Real.sqrt_inv,
          ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      nlinarith [sq_nonneg (X i ω)]
    refine (integral_mono (integrable_pow_of_abs_le (hXm i) (hXC i) 4)
      ((integrable_pow_of_abs_le (hXm i) (hXC i) 2).const_mul _) hle).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (h2 i) (by positivity)
  have hsum (ω : Ω) : tailEmpiricalProcess U n k t ω - tailEmpiricalProcess U n k s ω =
      ∑ i ∈ range n, X i ω := tailEmpiricalProcess_sub_eq_sum U hn k s t ω
  simp_rw [hsum]
  refine (integral_sum_range_pow_four_le hXm hXind hXC hX0 n).trans ?_
  have hS4 : ∑ i ∈ range n, ∫ ω, X i ω ^ 4 ∂P ≤ n * ((k : ℝ)⁻¹ * (2 * (k / n * (t - s)) / k)) := by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ range n) ↦ h4 i
  have hS2 : ∑ i ∈ range n, ∫ ω, X i ω ^ 2 ∂P ≤ n * (2 * (k / n * (t - s)) / k) := by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ range n) ↦ h2 i
  have hS2' : 0 ≤ ∑ i ∈ range n, ∫ ω, X i ω ^ 2 ∂P :=
    Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have e1 : (n : ℝ) * ((k : ℝ)⁻¹ * (2 * (k / n * (t - s)) / k)) = 2 * (t - s) / k := by
    field_simp
  have e2 : (n : ℝ) * (2 * (k / n * (t - s)) / k) = 2 * (t - s) := by
    field_simp
  rw [e1] at hS4
  rw [e2] at hS2
  have : (∑ i ∈ range n, ∫ ω, X i ω ^ 2 ∂P) ^ 2 ≤ (2 * (t - s)) ^ 2 :=
    pow_le_pow_left₀ hS2' hS2 2
  nlinarith

/-! ### A maximal inequality on blocks -/

/-- Between grid points, a function that can decrease at most linearly (with slope `c`) stays
close to its values at the grid points. -/
lemma abs_sub_le_of_grid {w : ℝ → ℝ} {c a h lam : ℝ} {q : ℕ} (hh : 0 < h)
    (hmono : ∀ u v, u ≤ v → w u ≤ w v + c * (v - u)) (hc : 0 ≤ c)
    (hgrid : ∀ j : ℕ, j ≤ 2 ^ q → |w (a + j * h) - w a| ≤ lam) {u : ℝ}
    (hu : u ∈ Set.Icc a (a + 2 ^ q * h)) : |w u - w a| ≤ lam + c * h := by
  have hq : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  set j : ℕ := min ⌊(u - a) / h⌋₊ (2 ^ q - 1) with hj
  have hua : 0 ≤ (u - a) / h := div_nonneg (by linarith [hu.1]) hh.le
  have hjs : a + j * h ≤ u := by
    have : (j : ℝ) ≤ (u - a) / h :=
      (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le hua)
    rw [le_div_iff₀ hh] at this
    linarith
  have hjq : j + 1 ≤ 2 ^ q := by omega
  have hju : u ≤ a + ((j + 1 : ℕ) : ℝ) * h := by
    rcases le_or_gt ⌊(u - a) / h⌋₊ (2 ^ q - 1) with hle | hgt
    · rw [hj, min_eq_left hle]
      have := Nat.lt_floor_add_one ((u - a) / h)
      rw [div_lt_iff₀ hh] at this
      push_cast
      linarith
    · rw [hj, min_eq_right hgt.le, Nat.sub_add_cancel hq]
      push_cast
      exact hu.2
  have h1 := hgrid j ((min_le_right _ _).trans (Nat.sub_le _ _))
  have h2 := hgrid (j + 1) hjq
  have hup := hmono u _ hju
  have hdown := hmono _ u hjs
  have e : a + ((j + 1 : ℕ) : ℝ) * h - u ≤ h := by push_cast at hju ⊢; linarith
  have e' : u - (a + j * h) ≤ h := by push_cast at hju ⊢; linarith
  push_cast at hup e h2 ⊢
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left e hc, mul_le_mul_of_nonneg_left e' hc]

/-- The tail empirical process decreases at most with slope `√k`. -/
lemma tailEmpiricalProcess_le_add (U : ℕ → Ω → ℝ) (n k : ℕ) {u v : ℝ} (huv : u ≤ v) (ω : Ω) :
    tailEmpiricalProcess U n k u ω ≤ tailEmpiricalProcess U n k v ω + √(k : ℝ) * (v - u) := by
  unfold tailEmpiricalProcess
  have hS : ∑ i ∈ range n, (Set.Ici (1 - k / n * u)).indicator (1 : ℝ → ℝ) (U i ω) ≤
      ∑ i ∈ range n, (Set.Ici (1 - k / n * v)).indicator 1 (U i ω) := by
    refine Finset.sum_le_sum fun i _ ↦ Set.indicator_le_indicator_of_subset
      (Set.Ici_subset_Ici.2 ?_) (fun _ ↦ zero_le_one) _
    have : (0 : ℝ) ≤ k / n := by positivity
    nlinarith
  have : (0 : ℝ) ≤ √(k : ℝ) * (k : ℝ)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hS this]

lemma abs_tailEmpiricalProcess_le (U : ℕ → Ω → ℝ) (n k : ℕ) (t : ℝ) (ω : Ω) :
    |tailEmpiricalProcess U n k t ω| ≤ √(k : ℝ) * ((k : ℝ)⁻¹ * n + |t|) := by
  unfold tailEmpiricalProcess
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ le_rfl))
    (Real.sqrt_nonneg _)
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)]
  simpa using Finset.sum_le_sum fun i (_ : i ∈ range n) ↦
    Set.indicator_le_self' (s := Set.Ici (1 - k / n * t)) (f := (1 : ℝ → ℝ))
      (fun _ _ ↦ zero_le_one) (U i ω)

lemma integrable_tailEmpiricalProcess_sub_pow [IsFiniteMeasure P] (hU : ∀ i, Measurable (U i))
    (n k : ℕ) (s t : ℝ) (j : ℕ) :
    Integrable (fun ω ↦ (tailEmpiricalProcess U n k t ω - tailEmpiricalProcess U n k s ω) ^ j)
      P := by
  refine Integrable.of_bound (C := (√(k : ℝ) * ((k : ℝ)⁻¹ * n + |t|) +
      √(k : ℝ) * ((k : ℝ)⁻¹ * n + |s|)) ^ j)
    (((measurable_tailEmpiricalProcess hU n k t).sub
      (measurable_tailEmpiricalProcess hU n k s)).pow_const j).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add
    (abs_tailEmpiricalProcess_le U n k t ω) (abs_tailEmpiricalProcess_le U n k s ω))) j

lemma sum_range_geom_le_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (q : ℕ) :
    ∑ ℓ ∈ range q, r ^ ℓ ≤ (1 - r)⁻¹ := by
  have h := geom_sum_mul r q
  have hpos : 0 < 1 - r := by linarith
  have : 0 ≤ r ^ q := pow_nonneg hr0 q
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  nlinarith

/-- **Maximal inequality for the tail empirical process on a block** `[a, a + L]`: with
`q` dyadic refinement levels, fine enough that `√k · L / 2 ^ q ≤ λ`,
`P (∃ u ∈ [a, a + L], 2 λ < |W_n(u) - W_n(a)|) ≤ 8⁴ / λ⁴ · (84 L² + 2 ^ (q + 2) L / k)`.
This combines the fourth-moment bound for the increments, dyadic chaining on the grid
`a + j L / 2 ^ q`, and the monotonicity of the counts between grid points. -/
theorem measureReal_exists_abs_tailEmpiricalProcess_sub_gt_le [IsProbabilityMeasure P]
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ} (hn : n ≠ 0)
    {a L lam : ℝ} (ha : 0 ≤ a) (hL : 0 < L) (hp : (k : ℝ) / n * (a + L) ≤ 1) (hlam : 0 < lam)
    (q : ℕ) (hq : √(k : ℝ) * (L / 2 ^ q) ≤ lam) :
    P.real {ω | ∃ u ∈ Set.Icc a (a + L),
      2 * lam < |tailEmpiricalProcess U n k u ω - tailEmpiricalProcess U n k a ω|} ≤
      8 ^ 4 / lam ^ 4 * (84 * L ^ 2 + 2 ^ (q + 2) * L / k) := by
  set h : ℝ := L / 2 ^ q with hh
  have hh0 : 0 < h := by positivity
  set Y : ℕ → Ω → ℝ := fun j ω ↦ tailEmpiricalProcess U n k (a + j * h) ω with hY
  set lamℓ : ℕ → ℝ := fun ℓ ↦ lam * (7 / 8) ^ ℓ / 8 with hlamℓ
  have hlamℓ0 (ℓ : ℕ) : 0 < lamℓ ℓ := by positivity
  have hsumlam : ∑ ℓ ∈ range (q + 1), lamℓ ℓ ≤ lam := by
    have hg := sum_range_geom_le_of_lt_one (r := 7 / 8) (by norm_num) (by norm_num) (q + 1)
    norm_num at hg
    simp only [hlamℓ, ← Finset.sum_div, ← Finset.mul_sum]
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  have hsub : {ω | ∃ u ∈ Set.Icc a (a + L),
      2 * lam < |tailEmpiricalProcess U n k u ω - tailEmpiricalProcess U n k a ω|} ⊆
      {ω | ∃ j ≤ 2 ^ q, ∑ ℓ ∈ range (q + 1), lamℓ ℓ < |Y j ω - Y 0 ω|} := by
    intro ω ⟨u, hu, hlt⟩
    by_contra hω
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hω
    have hY0 : Y 0 ω = tailEmpiricalProcess U n k a ω := by simp [hY]
    have hgrid : ∀ j : ℕ, j ≤ 2 ^ q → |tailEmpiricalProcess U n k (a + j * h) ω -
        tailEmpiricalProcess U n k a ω| ≤ lam := fun j hj ↦ by
      have := (hω j hj).trans hsumlam
      rwa [hY0] at this
    have hL' : a + 2 ^ q * h = a + L := by rw [hh]; field_simp
    have := abs_sub_le_of_grid (w := fun u ↦ tailEmpiricalProcess U n k u ω) hh0
      (fun u v huv ↦ tailEmpiricalProcess_le_add U n k huv ω) (Real.sqrt_nonneg _) hgrid
      (u := u) (by rw [hL']; exact hu)
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  set B : ℕ → ℝ := fun ℓ ↦ 12 * (L / 2 ^ ℓ) ^ 2 + 2 * (L / 2 ^ ℓ) / k with hB
  have hinc (ℓ : ℕ) (hℓ : ℓ ∈ range (q + 1)) (i : ℕ) :
      ((((i + 1) * 2 ^ (q - ℓ) : ℕ) : ℝ) * h) - (((i * 2 ^ (q - ℓ) : ℕ) : ℝ) * h) =
        L / 2 ^ ℓ := by
    have hℓq : ℓ ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    rw [hh]
    push_cast
    rw [show (2 : ℝ) ^ q = 2 ^ (q - ℓ) * 2 ^ ℓ by rw [← pow_add, Nat.sub_add_cancel hℓq]]
    field_simp
    ring
  have hle (ℓ : ℕ) (hℓ : ℓ ∈ range (q + 1)) (i : ℕ) (hi : i < 2 ^ ℓ) :
      a + (((i + 1) * 2 ^ (q - ℓ) : ℕ) : ℝ) * h ≤ a + L := by
    have hℓq : ℓ ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    have h1 : (((i + 1) * 2 ^ (q - ℓ) : ℕ) : ℝ) ≤ 2 ^ q := by
      have : (i + 1) * 2 ^ (q - ℓ) ≤ 2 ^ ℓ * 2 ^ (q - ℓ) := Nat.mul_le_mul_right _ hi
      rw [← pow_add, Nat.add_sub_cancel' hℓq] at this
      exact_mod_cast this
    have h2 : (((i + 1) * 2 ^ (q - ℓ) : ℕ) : ℝ) * h ≤ 2 ^ q * h :=
      mul_le_mul_of_nonneg_right h1 hh0.le
    have hL' : 2 ^ q * h = L := by rw [hh]; field_simp
    linarith
  have hchain := measureReal_exists_lt_abs_sub_le (P := P) q (Y := Y) hlamℓ0 (B := B)
    (fun ℓ hℓ i hi ↦ integrable_tailEmpiricalProcess_sub_pow hU n k _ _ 4)
    (fun ℓ hℓ i hi ↦ by
      have hd := hinc ℓ hℓ i
      have hL0 : (0 : ℝ) ≤ L / 2 ^ ℓ := by positivity
      have hst : a + ((i * 2 ^ (q - ℓ) : ℕ) : ℝ) * h ≤
          a + (((i + 1) * 2 ^ (q - ℓ) : ℕ) : ℝ) * h := by linarith
      have hp0 : (0 : ℝ) ≤ k / n := by positivity
      have hmom := integral_tailEmpiricalProcess_sub_pow_four_le hU hind hlaw hn
        (s := a + ((i * 2 ^ (q - ℓ) : ℕ) : ℝ) * h) (by positivity) hst
        ((mul_le_mul_of_nonneg_left (hle ℓ hℓ i hi) hp0).trans hp)
      have e : a + (((i + 1) * 2 ^ (q - ℓ) : ℕ) : ℝ) * h - (a + ((i * 2 ^ (q - ℓ) : ℕ) : ℝ) * h) =
          L / 2 ^ ℓ := by linarith
      rw [e] at hmom
      exact hmom)
  refine hchain.trans ?_
  -- the arithmetic
  have hterm (ℓ : ℕ) : (2 : ℝ) ^ ℓ * (B ℓ / lamℓ ℓ ^ 4) =
      8 ^ 4 / lam ^ 4 * (12 * L ^ 2 * (2048 / 2401) ^ ℓ + 2 * L / k * (4096 / 2401) ^ ℓ) := by
    have e1 : (2048 / 2401 : ℝ) ^ ℓ = ((2 : ℝ) ^ ℓ * ((7 / 8 : ℝ) ^ ℓ) ^ 4)⁻¹ := by
      rw [← pow_mul, mul_comm ℓ 4, pow_mul, ← mul_pow, ← inv_pow]
      norm_num
    have e2 : (4096 / 2401 : ℝ) ^ ℓ = (((7 / 8 : ℝ) ^ ℓ) ^ 4)⁻¹ := by
      rw [← pow_mul, mul_comm ℓ 4, pow_mul, ← inv_pow]
      norm_num
    rw [e1, e2]
    simp only [hB, hlamℓ]
    have : (2 : ℝ) ^ ℓ ≠ 0 := by positivity
    have : ((7 / 8 : ℝ) ^ ℓ) ≠ 0 := by positivity
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hs1 : ∑ ℓ ∈ range (q + 1), (2048 / 2401 : ℝ) ^ ℓ ≤ 7 :=
    (sum_range_geom_le_of_lt_one (by norm_num) (by norm_num) _).trans (by norm_num)
  have hs2 : ∑ ℓ ∈ range (q + 1), (4096 / 2401 : ℝ) ^ ℓ ≤ 2 ^ (q + 1) := by
    calc ∑ ℓ ∈ range (q + 1), (4096 / 2401 : ℝ) ^ ℓ ≤ ∑ ℓ ∈ range (q + 1), (2 : ℝ) ^ ℓ :=
          Finset.sum_le_sum fun ℓ _ ↦ pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ
      _ ≤ 2 ^ (q + 1) := by
          have := geom_sum_mul (2 : ℝ) (q + 1)
          norm_num at this
          linarith
  have hL2 : 0 ≤ 12 * L ^ 2 := by positivity
  have hLk : 0 ≤ 2 * L / k := by positivity
  calc 12 * L ^ 2 * ∑ ℓ ∈ range (q + 1), (2048 / 2401 : ℝ) ^ ℓ +
        2 * L / k * ∑ ℓ ∈ range (q + 1), (4096 / 2401 : ℝ) ^ ℓ
      ≤ 12 * L ^ 2 * 7 + 2 * L / k * 2 ^ (q + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hs1 hL2) (mul_le_mul_of_nonneg_left hs2 hLk)
    _ = 84 * L ^ 2 + 2 ^ (q + 2) * L / k := by ring

/-- **Maximal inequality on all the blocks** `[i/m, (i+1)/m]`, `i < m`. -/
theorem measureReal_exists_block_abs_tailEmpiricalProcess_sub_gt_le [IsProbabilityMeasure P]
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1)) {n k : ℕ} (hn : n ≠ 0)
    (hkn : k ≤ n) {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam) (q : ℕ)
    (hq : √(k : ℝ) * ((1 / m : ℝ) / 2 ^ q) ≤ lam) :
    P.real {ω | ∃ i < m, ∃ u ∈ Set.Icc ((i : ℝ) / m) ((i + 1 : ℝ) / m),
      2 * lam < |tailEmpiricalProcess U n k u ω - tailEmpiricalProcess U n k (i / m) ω|} ≤
      8 ^ 4 / lam ^ 4 * (84 / m + 2 ^ (q + 2) / k) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsub : {ω | ∃ i < m, ∃ u ∈ Set.Icc ((i : ℝ) / m) ((i + 1 : ℝ) / m),
      2 * lam < |tailEmpiricalProcess U n k u ω - tailEmpiricalProcess U n k (i / m) ω|} ⊆
      ⋃ i ∈ range m, {ω | ∃ u ∈ Set.Icc ((i : ℝ) / m) ((i : ℝ) / m + 1 / m),
        2 * lam < |tailEmpiricalProcess U n k u ω - tailEmpiricalProcess U n k (i / m) ω|} := by
    rintro ω ⟨i, hi, u, hu, hlt⟩
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hi)) ⟨u, ?_, hlt⟩
    rwa [show (i : ℝ) / m + 1 / m = (i + 1) / m by ring]
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  have hblock (i : ℕ) (hi : i ∈ range m) :
      P.real {ω | ∃ u ∈ Set.Icc ((i : ℝ) / m) ((i : ℝ) / m + 1 / m),
        2 * lam < |tailEmpiricalProcess U n k u ω - tailEmpiricalProcess U n k (i / m) ω|} ≤
        8 ^ 4 / lam ^ 4 * (84 * (1 / m) ^ 2 + 2 ^ (q + 2) * (1 / m) / k) := by
    refine measureReal_exists_abs_tailEmpiricalProcess_sub_gt_le hU hind hlaw hn
      (by positivity) (by positivity) ?_ hlam q hq
    have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.1 hi
    have hk : (k : ℝ) / n ≤ 1 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]
      · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).2 (by exact_mod_cast hkn)
    have h1 : (i : ℝ) / m + 1 / m ≤ 1 := by
      rw [← add_div, div_le_one hm']; exact hi'
    have h0 : 0 ≤ (i : ℝ) / m + 1 / m := by positivity
    calc (k : ℝ) / n * ((i : ℝ) / m + 1 / m) ≤ 1 * 1 :=
          mul_le_mul hk h1 h0 zero_le_one
      _ = 1 := one_mul 1
  refine (Finset.sum_le_sum hblock).trans_eq ?_
  rw [Finset.sum_const, card_range, nsmul_eq_mul]
  field_simp

/-! ### The tail empirical process as a random element of `D([0, 1])` -/

lemma isCadlag_indicator_Ici {p c : ℝ} (hp : 0 ≤ p) :
    IsCadlag (fun t : unitInterval ↦ (Set.Ici (1 - p * t)).indicator (1 : ℝ → ℝ) c) := by
  have hmono : Monotone (fun t : unitInterval ↦ (Set.Ici (1 - p * t)).indicator (1 : ℝ → ℝ) c) :=
    fun t t' htt' ↦ Set.indicator_le_indicator_of_subset (Set.Ici_subset_Ici.2
      (by have : (t : ℝ) ≤ t' := htt'; nlinarith)) (fun _ ↦ zero_le_one) c
  refine ⟨fun t ↦ ?_, fun t ↦ ⟨_, hmono.tendsto_nhdsLT t⟩⟩
  by_cases h : 1 - p * t ≤ c
  · refine (continuousWithinAt_const (b := (1 : ℝ))).congr (fun y hy ↦ ?_) ?_
    · have : 1 - p * y ≤ c := by
        have : (t : ℝ) ≤ y := le_of_lt (show t < y from hy)
        nlinarith
      simp [Set.indicator, this]
    · simp [Set.indicator, h]
  · refine ((continuousAt_const (y := (0 : ℝ))).congr ?_).continuousWithinAt
    have hopen : IsOpen {t' : unitInterval | c < 1 - p * t'} :=
      isOpen_lt continuous_const (by fun_prop)
    filter_upwards [hopen.mem_nhds (show c < 1 - p * t from not_le.1 h)] with y hy
    simp [Set.indicator, not_le.2 (show c < 1 - p * y from hy)]

lemma isCadlag_tailEmpiricalProcess (U : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    IsCadlag (fun t : unitInterval ↦ tailEmpiricalProcess U n k t ω) := by
  have hp : (0 : ℝ) ≤ k / n := by positivity
  have hsum : ∀ N, IsCadlag (fun t : unitInterval ↦
      ∑ i ∈ range N, (Set.Ici (1 - k / n * (t : ℝ))).indicator (1 : ℝ → ℝ) (U i ω)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have := ih.add (isCadlag_indicator_Ici (c := U N ω) hp)
      convert this using 1
      ext t
      simp [Finset.sum_range_succ]
  unfold tailEmpiricalProcess
  have hid : IsCadlag (fun t : unitInterval ↦ (t : ℝ)) := continuous_subtype_val.isCadlag
  have := ((hsum n).const_smul ((k : ℝ)⁻¹)).sub hid |>.const_smul (√(k : ℝ))
  convert this using 1

/-- The **uniform tail empirical process** as a random element of the Skorokhod space
`D([0, 1])`: `t ↦ W_n(t)`, `t ∈ [0, 1]`. -/
noncomputable def tailEmpiricalPath (U : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : SkorokhodSpace ℝ :=
  ⟨fun t : unitInterval ↦ tailEmpiricalProcess U n k t ω, isCadlag_tailEmpiricalProcess U n k ω⟩

@[simp]
lemma tailEmpiricalPath_apply (U : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) (t : unitInterval) :
    tailEmpiricalPath U n k ω t = tailEmpiricalProcess U n k t ω := rfl

lemma measurable_tailEmpiricalPath (hU : ∀ i, Measurable (U i)) (n k : ℕ) :
    Measurable (tailEmpiricalPath U n k) := by
  have h : Measurable fun ω ↦ ⇑(tailEmpiricalPath U n k ω) :=
    measurable_pi_iff.2 fun t ↦ measurable_tailEmpiricalProcess hU n k t
  rw [measurable_iff_comap_le, SkorokhodSpace.measurableSpace_eq_comap_coeFn,
    MeasurableSpace.comap_comp]
  exact h.comap_le

/-! ### Tightness and weak convergence in `D([0, 1])` -/

lemma ofReal_inv_nat_succ_le {N : ℕ} :
    ENNReal.ofReal (1 / ((N : ℝ) + 1)) ≤ (N : ℝ≥0∞)⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_add (by positivity)
    zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  exact ENNReal.inv_le_inv.2 le_self_add

/-- At time `0` the tail empirical process vanishes almost surely. -/
lemma measure_tailEmpiricalProcess_zero_ne_zero [IsProbabilityMeasure P]
    (hU : ∀ i, Measurable (U i)) (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    (n k : ℕ) : P {ω | 0 < |tailEmpiricalProcess U n k 0 ω|} = 0 := by
  have hnull (i : ℕ) : P {ω | 1 ≤ U i ω} = 0 := by
    have h := measureReal_uniform_Ici (x := 0) le_rfl zero_le_one
    rw [sub_zero, measureReal_eq_zero_iff] at h
    rw [show {ω | 1 ≤ U i ω} = U i ⁻¹' Set.Ici 1 from rfl, ← Measure.map_apply (hU i)
      measurableSet_Ici, hlaw i]
    exact h
  refine measure_mono_null (fun ω hω ↦ ?_) ((measure_biUnion_null_iff
    (Finset.range n).countable_toSet).2 fun i _ ↦ hnull i)
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hcon
  have : tailEmpiricalProcess U n k 0 ω = 0 := by
    unfold tailEmpiricalProcess
    rw [Finset.sum_eq_zero fun i hi ↦ ?_]
    · simp
    · simp [Set.indicator, not_le.2 (hcon i (Finset.mem_coe.2 hi))]
  simp [this] at hω

/-- The block oscillation condition for the uniform tail empirical process. -/
theorem exists_eventually_measure_blockOscillation_le [IsProbabilityMeasure P]
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0))
    {ε η : ℝ≥0∞} (hε : 0 < ε) (hη : 0 < η) :
    ∃ m > 0, ∀ᶠ n in atTop,
      P.map (tailEmpiricalPath U n (k n)) {x | ε ≤ blockOscillation (⇑x) m} ≤ η := by
  obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  obtain ⟨M, hM⟩ := ENNReal.exists_inv_nat_lt hη.ne'
  set lam : ℝ := 1 / (2 * ((N : ℝ) + 1)) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamε : ENNReal.ofReal (2 * lam) < ε := by
    have : 2 * lam = 1 / ((N : ℝ) + 1) := by rw [hlam]; field_simp
    rw [this]
    exact ofReal_inv_nat_succ_le.trans_lt hN
  set η' : ℝ := 1 / ((M : ℝ) + 1) with hη'
  have hη'0 : 0 < η' := by positivity
  have hη'η : ENNReal.ofReal η' ≤ η := ofReal_inv_nat_succ_le.trans hM.le
  set C : ℝ := 8 ^ 4 / lam ^ 4 with hC
  have hC0 : 0 < C := by positivity
  set m : ℕ := ⌈2 * C * 84 / η'⌉₊ + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos _
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm0
  have hCm : C * (84 / m) ≤ η' / 2 := by
    have h1 : 2 * C * 84 / η' ≤ m := by
      rw [hm]; push_cast; linarith [Nat.le_ceil (2 * C * 84 / η')]
    rw [div_le_iff₀ hη'0] at h1
    rw [mul_div_assoc', div_le_iff₀ hm']
    nlinarith
  refine ⟨m, hm0, ?_⟩
  -- the number of dyadic levels for the `n`-th process
  have hq (n : ℕ) : ∃ q : ℕ, √(k n : ℝ) / (m * lam) ≤ 2 ^ q ∧
      (2 : ℝ) ^ q ≤ 2 * (1 + √(k n : ℝ) / (m * lam)) := by
    obtain ⟨q₀, h1, h2⟩ := exists_nat_pow_near (le_max_left 1 (√(k n : ℝ) / (m * lam)))
      (one_lt_two : (1 : ℝ) < 2)
    refine ⟨q₀ + 1, (le_max_right _ _).trans h2.le, ?_⟩
    rw [pow_succ]
    have : max 1 (√(k n : ℝ) / (m * lam)) ≤ 1 + √(k n : ℝ) / (m * lam) :=
      max_le (by linarith [show 0 ≤ √(k n : ℝ) / (m * lam) by positivity]) (by linarith)
    linarith
  choose q hq1 hq2 using hq
  have hkR : Tendsto (fun n ↦ (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hsmall : Tendsto (fun n ↦ C * (8 * (1 + √(k n : ℝ) / (m * lam)) / k n)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ (k n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hkR
    have h2 : Tendsto (fun n ↦ (√(k n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hkR)
    have h3 : Tendsto (fun n ↦ C * (8 * ((k n : ℝ)⁻¹ + (√(k n : ℝ))⁻¹ / (m * lam))))
        atTop (𝓝 (C * (8 * (0 + 0 / (m * lam))))) :=
      ((h1.add (h2.div_const _)).const_mul _).const_mul _
    simp only [zero_div, add_zero, mul_zero] at h3
    refine h3.congr fun n ↦ ?_
    rw [mul_div_assoc, add_div, one_div, div_right_comm (√(k n : ℝ)), Real.sqrt_div_self',
      one_div]
  have hkn1 : ∀ᶠ n in atTop, k n ≤ n := by
    filter_upwards [hkn.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    rw [div_lt_one hn'] at hn
    exact_mod_cast hn.le
  filter_upwards [hsmall.eventually (ge_mem_nhds (half_pos hη'0)), hkn1, eventually_gt_atTop 0]
    with n hn hkn' hn0
  set E := {ω | ∃ i < m, ∃ u ∈ Set.Icc ((i : ℝ) / m) ((i + 1 : ℝ) / m),
      2 * lam < |tailEmpiricalProcess U n (k n) u ω - tailEmpiricalProcess U n (k n) (i / m) ω|}
    with hE
  have hqn : √(k n : ℝ) * ((1 / m : ℝ) / 2 ^ q n) ≤ lam := by
    have h1 := hq1 n
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_div, mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hPE := measureReal_exists_block_abs_tailEmpiricalProcess_sub_gt_le hU hind hlaw
    hn0.ne' hkn' hm0 hlam0 (q n) hqn
  have hbound : 8 ^ 4 / lam ^ 4 * (84 / m + 2 ^ (q n + 2) / (k n : ℝ)) ≤ η' := by
    have h2 : (2 : ℝ) ^ (q n + 2) / k n ≤ 8 * (1 + √(k n : ℝ) / (m * lam)) / k n := by
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      rw [pow_add]
      nlinarith [hq2 n]
    have : C * (2 ^ (q n + 2) / (k n : ℝ)) ≤ η' / 2 :=
      (mul_le_mul_of_nonneg_left h2 hC0.le).trans hn
    rw [← hC, mul_add]
    linarith
  -- if all blocks are good, the block oscillation is at most `2 λ`
  have hsub : tailEmpiricalPath U n (k n) ⁻¹' {x | ENNReal.ofReal (2 * lam) <
      blockOscillation (⇑x) m} ⊆ E := by
    intro ω hω
    by_contra hωE
    simp only [hE, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hωE
    refine (not_le.2 (show ENNReal.ofReal (2 * lam) < _ from hω)) ?_
    refine iSup₂_le fun i hi ↦ iSup₂_le fun u hu ↦ ?_
    rw [edist_dist, Real.dist_eq, tailEmpiricalPath_apply, tailEmpiricalPath_apply,
      unitInterval.coe_gridPt hi.le]
    exact ENNReal.ofReal_le_ofReal (hωE i hi u hu)
  have hmeas : MeasurableSet {x : SkorokhodSpace ℝ | ENNReal.ofReal (2 * lam) <
      blockOscillation (⇑x) m} :=
    measurableSet_lt measurable_const (SkorokhodSpace.measurable_blockOscillation m)
  calc P.map (tailEmpiricalPath U n (k n)) {x | ε ≤ blockOscillation (⇑x) m}
      ≤ P.map (tailEmpiricalPath U n (k n)) {x | ENNReal.ofReal (2 * lam) <
          blockOscillation (⇑x) m} := measure_mono fun x hx ↦ hlamε.trans_le hx
    _ = P (tailEmpiricalPath U n (k n) ⁻¹' {x | ENNReal.ofReal (2 * lam) <
          blockOscillation (⇑x) m}) := Measure.map_apply (measurable_tailEmpiricalPath hU _ _) hmeas
    _ ≤ P E := measure_mono hsub
    _ = ENNReal.ofReal (P.real E) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal η' := ENNReal.ofReal_le_ofReal (hPE.trans hbound)
    _ ≤ η := hη'η

/-- The finite-dimensional laws of Brownian motion depend continuously on the times. -/
theorem tendsto_brownianFdd {ι : Type*} [Fintype ι] [DecidableEq ι] {τs : ℕ → ι → ℝ≥0}
    {τ : ι → ℝ≥0} (h : ∀ i, Tendsto (fun m ↦ (τs m i : ℝ)) atTop (𝓝 (τ i))) :
    Tendsto (β := ProbabilityMeasure (ι → ℝ))
      (fun m ↦ (⟨brownianFdd (τs m), isProbabilityMeasure_brownianFdd _⟩ :
      ProbabilityMeasure (ι → ℝ))) atTop
      (𝓝 (⟨brownianFdd τ, isProbabilityMeasure_brownianFdd _⟩ : ProbabilityMeasure (ι → ℝ))) := by
  have hG : TendstoInDistribution (fun _ : ℕ ↦ (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι))
      atTop id (fun m ↦ multivariateGaussian 0 (brownianCovMatrix (τs m)))
      (multivariateGaussian 0 (brownianCovMatrix τ)) := by
    refine .of_tendsto_charFun (fun _ ↦ aemeasurable_id) aemeasurable_id fun a ↦ ?_
    simp only [Measure.map_id]
    simp_rw [charFun_multivariateGaussian (posSemidef_brownianCovMatrix _)]
    have hq : Tendsto (fun m ↦ dotProduct a.ofLp (Matrix.mulVec (brownianCovMatrix (τs m)) a.ofLp))
        atTop (𝓝 (dotProduct a.ofLp (Matrix.mulVec (brownianCovMatrix τ) a.ofLp))) := by
      simp only [dotProduct, Matrix.mulVec, brownianCovMatrix, Matrix.of_apply]
      exact tendsto_finsetSum _ fun i _ ↦ (tendsto_finsetSum _ fun j _ ↦
        (((h i).min (h j)).mul_const _)).const_mul _
    exact (Complex.continuous_exp.tendsto _).comp (tendsto_const_nhds.sub
      (((Complex.continuous_ofReal.tendsto _).comp hq).div_const _))
  have h' := (hG.continuous_comp (PiLp.continuous_ofLp 2 _)).tendsto
  simp only [Function.comp_id] at h'
  exact h'

/-- A time `t ∈ [0, 1]` as a nonnegative real number. -/
def _root_.unitInterval.toNNReal' (t : unitInterval) : ℝ≥0 := ⟨t, t.2.1⟩

@[simp]
lemma _root_.unitInterval.coe_toNNReal' (t : unitInterval) :
    ((unitInterval.toNNReal' t : ℝ≥0) : ℝ) = t := rfl

/-- **Weak convergence of the uniform tail empirical process in `D([0, 1])`**
([de Haan–Ferreira, Theorem 5.1.4]; [Einmahl 1992]). If `U 0, U 1, …` are i.i.d. uniform on
`[0, 1]`, `k n → ∞` and `k n / n → 0`, then the laws of the paths `t ↦ W_n(t)`, `t ∈ [0, 1]`,
converge weakly in the Skorokhod space `D([0, 1])` to a probability measure `μ` whose
finite-dimensional distributions are those of Brownian motion: for every finite family of
times `τ i ∈ [0, 1]`, the law of `(x (τ i))_i` under `μ` is `brownianFdd τ`, the centered
Gaussian law with covariance `min (τ i) (τ j)`. Since the finite-dimensional distributions
determine a law on `D([0, 1])` (`SkorokhodSpace.ext_of_forall_map_restrict_eq`), `μ` is unique:
it is the law of Brownian motion on `D([0, 1])`. -/
theorem exists_tendsto_tailEmpiricalPath [IsProbabilityMeasure P]
    (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U P)
    (hlaw : ∀ i, P.map (U i) = volume.restrict (Set.Icc 0 1))
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    ∃ μ : ProbabilityMeasure (SkorokhodSpace ℝ),
      Tendsto (fun n ↦ ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
        (tailEmpiricalPath U n (k n))) atTop (𝓝 μ) ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → unitInterval),
        (μ : Measure (SkorokhodSpace ℝ)).map (fun x : SkorokhodSpace ℝ ↦ fun i ↦ x (τ i)) =
          brownianFdd (fun i ↦ unitInterval.toNNReal' (τ i)) := by
  set μs : ℕ → ProbabilityMeasure (SkorokhodSpace ℝ) := fun n ↦
    ProbabilityMeasure.map (⟨P, inferInstance⟩ : ProbabilityMeasure Ω)
      (tailEmpiricalPath U n (k n)) with hμs
  have hμs_apply (n : ℕ) : (μs n : Measure (SkorokhodSpace ℝ)) =
      P.map (tailEmpiricalPath U n (k n)) := rfl
  set ρ : ∀ J : Finset unitInterval, ProbabilityMeasure (J → ℝ) := fun J ↦
    ⟨brownianFdd (fun t : J ↦ unitInterval.toNNReal' t), isProbabilityMeasure_brownianFdd _⟩
    with hρ
  have hfdd : ∀ J : Finset unitInterval, (J : Set unitInterval) ⊆ Set.univ →
      Tendsto (fun n ↦ (μs n).map (fun x : SkorokhodSpace ℝ ↦ fun t : J ↦ x t)) atTop
        (𝓝 (ρ J)) := by
    intro J _
    have h := (tendstoInDistribution_tailEmpiricalProcess_comp hU hind hlaw hk hkn
      (fun t : J ↦ unitInterval.toNNReal' t)).tendsto
    simp only [Measure.map_id] at h
    refine h.congr fun n ↦ ProbabilityMeasure.toMeasure_injective ?_
    simp only [ProbabilityMeasure.toMeasure_map, hμs_apply]
    rw [Measure.map_map (SkorokhodSpace.measurable_restrict_finset J)
      (measurable_tailEmpiricalPath hU n (k n))]
    rfl
  have htight : IsTightMeasureSet (Set.range fun n ↦ (μs n : Measure (SkorokhodSpace ℝ))) := by
    refine SkorokhodSpace.isTightMeasureSet_of_blockOscillation
      (μs := fun n ↦ (μs n : Measure (SkorokhodSpace ℝ))) (fun η hη ↦ ⟨0, ?_⟩)
      (fun ε hε η hη ↦ ?_)
    · refine Eventually.of_forall fun n ↦ ?_
      have hS : MeasurableSet {x : SkorokhodSpace ℝ | (0 : ℝ) < |x 0|} :=
        measurableSet_lt measurable_const
          (continuous_abs.comp SkorokhodSpace.continuous_apply_zero).measurable
      rw [hμs_apply, Measure.map_apply (measurable_tailEmpiricalPath hU n (k n)) hS]
      have := measure_tailEmpiricalProcess_zero_ne_zero hU hlaw (P := P) n (k n)
      refine le_of_eq_of_le ?_ zero_le
      convert this using 2
      ext ω
      simp
    · obtain ⟨m, hm, hev⟩ := exists_eventually_measure_blockOscillation_le hU hind hlaw hk hkn
        hε hη
      exact ⟨m, hm, hev.mono fun n hn ↦ by rw [hμs_apply]; exact hn⟩
  obtain ⟨μ, hconv, -⟩ := SkorokhodSpace.exists_tendsto_of_tendsto_map_restrict_of_isTight
    (T := Set.univ) (by simp) (Set.mem_univ _) ρ hfdd htight
  refine ⟨μ, hconv, fun {ι} _ _ τ ↦ ?_⟩
  -- the finite-dimensional laws along an arbitrary family of times
  have hfam (σ : ι → unitInterval) : Tendsto (fun n ↦ (μs n).map
      (fun x : SkorokhodSpace ℝ ↦ fun i ↦ x (σ i))) atTop
      (𝓝 ⟨brownianFdd (fun i ↦ unitInterval.toNNReal' (σ i)),
        isProbabilityMeasure_brownianFdd _⟩) := by
    have h := (tendstoInDistribution_tailEmpiricalProcess_comp hU hind hlaw hk hkn
      (fun i ↦ unitInterval.toNNReal' (σ i))).tendsto
    simp only [Measure.map_id] at h
    refine h.congr fun n ↦ ProbabilityMeasure.toMeasure_injective ?_
    simp only [ProbabilityMeasure.toMeasure_map, hμs_apply]
    rw [Measure.map_map (measurable_pi_iff.2 fun i ↦ SkorokhodSpace.measurable_apply (σ i))
      (measurable_tailEmpiricalPath hU n (k n))]
    rfl
  -- at continuity times of `μ`, by the continuous mapping theorem
  have hgood (σ : ι → unitInterval)
      (hσ : ∀ i, σ i ∈ SkorokhodSpace.continuityTimes (μ : Measure (SkorokhodSpace ℝ))) :
      μ.map (fun x : SkorokhodSpace ℝ ↦ fun i ↦ x (σ i)) =
        ⟨brownianFdd (fun i ↦ unitInterval.toNNReal' (σ i)), isProbabilityMeasure_brownianFdd _⟩ :=
    tendsto_nhds_unique (SkorokhodSpace.tendsto_map_comp_of_tendsto hconv hσ) (hfam σ)
  -- approximate arbitrary times from the right by continuity times
  have hdense : Dense (SkorokhodSpace.continuityTimes (μ : Measure (SkorokhodSpace ℝ))) := by
    simpa using unitInterval.dense_compl_of_countable
      (SkorokhodSpace.countable_compl_continuityTimes (μ : Measure (SkorokhodSpace ℝ)))
  have happrox (i : ι) : ∃ s : ℕ → unitInterval,
      (∀ m, s m ∈ SkorokhodSpace.continuityTimes (μ : Measure (SkorokhodSpace ℝ))) ∧
      (∀ x : SkorokhodSpace ℝ, Tendsto (fun m ↦ x (s m)) atTop (𝓝 (x (τ i)))) ∧
      Tendsto (fun m ↦ ((s m : unitInterval) : ℝ)) atTop (𝓝 (τ i)) := by
    by_cases h1 : τ i = 1
    · refine ⟨fun _ ↦ 1, fun _ ↦ SkorokhodSpace.one_mem_continuityTimes _, fun x ↦ ?_, ?_⟩
      · rw [h1]; exact tendsto_const_nhds
      · rw [h1]; exact tendsto_const_nhds
    · obtain ⟨s, hsT, hs⟩ := SkorokhodSpace.exists_seq_mem_tendsto_nhdsGT hdense
        (lt_of_le_of_ne le_top h1)
      exact ⟨s, hsT, fun x ↦ (x.isRightContinuous (τ i)).tendsto.comp hs,
        (continuous_subtype_val.tendsto _).comp (hs.mono_right nhdsWithin_le_nhds)⟩
  choose s hsT hsx hsR using happrox
  have hA : TendstoInDistribution (fun m (x : SkorokhodSpace ℝ) ↦ fun i ↦ x (s i m)) atTop
      (fun (x : SkorokhodSpace ℝ) i ↦ x (τ i)) (fun _ ↦ (μ : Measure (SkorokhodSpace ℝ))) μ :=
    tendstoInDistribution_of_ae_tendsto
      (fun m ↦ (measurable_pi_iff.2 fun i ↦ SkorokhodSpace.measurable_apply (s i m)).aemeasurable)
      (measurable_pi_iff.2 fun i ↦ SkorokhodSpace.measurable_apply (τ i)).aemeasurable
      (ae_of_all _ fun x ↦ tendsto_pi_nhds.2 fun i ↦ hsx i x)
  have hB := tendsto_brownianFdd (τs := fun m i ↦ unitInterval.toNNReal' (s i m))
    (τ := fun i ↦ unitInterval.toNNReal' (τ i)) fun i ↦ hsR i
  have hA' := hA.tendsto
  have heq : (fun m ↦ (⟨(μ : Measure (SkorokhodSpace ℝ)).map
      (fun x : SkorokhodSpace ℝ ↦ fun i ↦ x (s i m)), inferInstance⟩ :
        ProbabilityMeasure (ι → ℝ))) = fun m ↦
      ⟨brownianFdd (fun i ↦ unitInterval.toNNReal' (s i m)),
        isProbabilityMeasure_brownianFdd _⟩ := by
    funext m
    exact congrArg (fun ν : ProbabilityMeasure (ι → ℝ) ↦ ν) (hgood (fun i ↦ s i m) fun i ↦ hsT i m)
  rw [heq] at hA'
  have := congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hA' hB)
  simpa using this

end ExtremeValueTheory
