/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Basic
import ExtremeValueTheory.ForMathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Pareto
import Mathlib.Probability.ConditionalProbability

/-!
# Regularly varying time series and the tail process

We follow Basrak and Segers, *Regularly varying multivariate time series*, Stochastic Process.
Appl. 119 (2009) [BS09], and Kulik and Soulier, *Heavy-Tailed Time Series* (Springer, 2020),
Chapter 5 [KS20].

## The polar decomposition

The heart of [BS09, Theorem 2.1] is a statement about a single random vector: let `Z ≥ 0` be a
random variable and `V` a random vector. Then the following are equivalent:

* `P(Z > x)` is regularly varying with index `-α` and the law of `V / Z` given `Z > x` converges
  weakly to a law `μ` (the law of the *spectral* vector `Θ`);
* the law of `(Z / x, V / x)` given `Z > x` converges weakly to a law `ν` whose first marginal
  is the Pareto law `P(R > r) = r ^ (-α)`, `r ≥ 1`.

Moreover `ν` is then the law of `(R, R • Θ)` with `R` Pareto and independent of `Θ`.

## Main definitions

* `ExtremeValueTheory.TendstoLawCond P s Y l ν`: the laws of `Y i` under the conditional
  probabilities `P[|s i]` converge weakly to `ν` along `l`.
* `ExtremeValueTheory.HasSpectralTailProcess`: a time series `(X_t)_{t ∈ ℤ}` is jointly regularly
  varying with index `α`, with spectral tail process `(Θ_t)` ([BS09, Theorem 2.1 (iii)],
  [KS20, Definition 5.1.1 and Theorem 5.2.2]).
* `ExtremeValueTheory.HasTailProcess`: the tail process `(Y_t)` ([BS09, Theorem 2.1 (ii)]).

## Main results

* `ExtremeValueTheory.tendstoLawCond_polar`: spectral convergence and regular variation imply
  convergence of `(Z / x, V / x)` to the law of `(R, R • Θ)` with `R` Pareto independent of `Θ`.
* `ExtremeValueTheory.tendstoLawCond_spectral_of_polar`: the converse.
* `ExtremeValueTheory.hasSpectralTailProcess_iff_hasTailProcess`: the Basrak–Segers
  equivalence [BS09, Theorem 2.1] for windows of a time series.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### The Pareto law -/

section Pareto

variable {α : ℝ}

/-- The tail of the Pareto law: `P(R > u) = u ^ (-α)` for `u ≥ 1`. -/
theorem paretoMeasure_one_Ioi (hα : 0 < α) {u : ℝ} (hu : 1 ≤ u) :
    paretoMeasure 1 α (Ioi u) = ENNReal.ofReal (u ^ (-α)) := by
  have hu0 : 0 < u := one_pos.trans_le hu
  rw [paretoMeasure, withDensity_apply _ measurableSet_Ioi,
    setLIntegral_congr_fun measurableSet_Ioi
      (g := fun y => ENNReal.ofReal (α * y ^ (-(α + 1)))) (fun y hy => by
        rw [paretoPDF_of_le (hu.trans (le_of_lt hy)), Real.one_rpow, mul_one])]
  have hint : IntegrableOn (fun y : ℝ => α * y ^ (-(α + 1))) (Ioi u) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hu0).const_mul α
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hu0,
      show -(α + 1) + 1 = -α by ring]
    field_simp
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun y hy =>
      mul_nonneg hα.le (Real.rpow_pos_of_pos (hu0.trans hy) _).le

theorem paretoMeasure_one_real_Ioi (hα : 0 < α) {u : ℝ} (hu : 1 ≤ u) :
    (paretoMeasure 1 α).real (Ioi u) = u ^ (-α) := by
  rw [measureReal_def, paretoMeasure_one_Ioi hα hu,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (one_pos.trans_le hu) _).le]

theorem paretoMeasure_singleton (t : ℝ) (u : ℝ) : paretoMeasure t α {u} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

theorem paretoMeasure_one_Iic_one : paretoMeasure 1 α (Iic 1) = 0 := by
  refine le_antisymm ?_ zero_le
  rw [← Iio_union_right]
  refine (measure_union_le _ _).trans ?_
  rw [paretoMeasure_singleton, add_zero, paretoMeasure, withDensity_apply _ measurableSet_Iio,
    lintegral_paretoPDF_of_le le_rfl]

/-- A Pareto random variable is `> 1` almost surely. -/
theorem ae_one_lt_paretoMeasure : ∀ᵐ r ∂paretoMeasure 1 α, 1 < r := by
  rw [ae_iff]
  simp only [not_lt]
  exact paretoMeasure_one_Iic_one

end Pareto

/-! ### Weak convergence of conditional laws -/

section TendstoLawCond

variable {ι Ω E F : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace E] [MeasurableSpace E]

/-- The laws of `Y i` under the conditional probability measures `P[|s i]` converge weakly to
`ν` along the filter `l`: `E[f(Y i) | s i] → ∫ f dν` for every bounded continuous `f`. -/
def TendstoLawCond (P : Measure Ω) (s : ι → Set Ω) (Y : ι → Ω → E) (l : Filter ι)
    (ν : Measure E) : Prop :=
  ∀ f : E →ᵇ ℝ, Tendsto (fun i => ∫ ω, f (Y i ω) ∂P[|s i]) l (𝓝 (∫ y, f y ∂ν))

variable {P : Measure Ω} {s : ι → Set Ω} {Y Y' : ι → Ω → E} {l : Filter ι} {ν : Measure E}

/-- Continuous mapping theorem for conditional laws. -/
theorem TendstoLawCond.comp [OpensMeasurableSpace E] [TopologicalSpace F] [MeasurableSpace F]
    [BorelSpace F] (h : TendstoLawCond P s Y l ν) {φ : E → F} (hφ : Continuous φ) :
    TendstoLawCond P s (fun i ω => φ (Y i ω)) l (ν.map φ) := by
  intro f
  rw [integral_map hφ.measurable.aemeasurable
    (f.continuous.aestronglyMeasurable)]
  exact h (f.compContinuous ⟨φ, hφ⟩)

/-- Conditional laws only depend on the random elements almost surely on the conditioning
events. -/
theorem TendstoLawCond.congr (h : TendstoLawCond P s Y l ν)
    (hYY' : ∀ᶠ i in l, ∀ᵐ ω ∂P[|s i], Y i ω = Y' i ω) : TendstoLawCond P s Y' l ν := by
  intro f
  refine (h f).congr' ?_
  filter_upwards [hYY'] with i hi
  exact integral_congr_ae (hi.mono fun ω hω => by simp only [hω])

/-- If the conditional laws converge to a probability measure, the conditioning events have
eventually positive probability. -/
theorem TendstoLawCond.eventually_measure_ne_zero [IsProbabilityMeasure ν]
    (h : TendstoLawCond P s Y l ν) : ∀ᶠ i in l, P (s i) ≠ 0 := by
  have h1 := h (BoundedContinuousFunction.const E 1)
  simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
    probReal_univ] at h1
  filter_upwards [h1.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))] with i hi hzero
  simp [cond_eq_zero_of_meas_eq_zero hzero] at hi
  linarith

end TendstoLawCond

/-- Integral against a conditional probability measure. -/
theorem integral_cond_eq {Ω G : Type*} {_ : MeasurableSpace Ω} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (P : Measure Ω) (s : Set Ω) (f : Ω → G) :
    ∫ ω, f ω ∂P[|s] = (P.real s)⁻¹ • ∫ ω in s, f ω ∂P := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, measureReal_def]

theorem integrable_of_abs_le {X : Type*} {_ : MeasurableSpace X} {ν : Measure X}
    [IsFiniteMeasure ν] {F : X → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ p, |F p| ≤ C) :
    Integrable F ν :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ fun p => by
    simpa [Real.norm_eq_abs] using hC p)

/-! ### The polar decomposition -/

section Polar

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  {Z : Ω → ℝ} {T : Ω → E} {μ : Measure E} [IsProbabilityMeasure μ] {α : ℝ}

/-- Auxiliary class of test functions `F(r, θ)` for which `E[F(Z / x, T) | Z > x]` converges to
the integral of `F` against `Pareto(α) ⊗ μ`. -/
private def PolarGood (P : Measure Ω) (Z : Ω → ℝ) (T : Ω → E) (μ : Measure E) (α : ℝ)
    (F : ℝ × E → ℝ) : Prop :=
  Measurable F ∧ (∃ C, ∀ p, |F p| ≤ C) ∧
    Tendsto (fun x => ∫ ω, F (Z ω / x, T ω) ∂P[|{ω | x < Z ω}]) atTop
      (𝓝 (∫ p, F p ∂((paretoMeasure 1 α).prod μ)))

omit [IsProbabilityMeasure P] in
private lemma polarGood_zero : PolarGood P Z T μ α (fun _ => 0) :=
  ⟨measurable_const, ⟨0, fun _ => by simp⟩, by simp⟩

omit [IsProbabilityMeasure P] in
private lemma PolarGood.add (hα : 0 < α) (hZ : Measurable Z) (hT : Measurable T)
    {F G : ℝ × E → ℝ} (hF : PolarGood P Z T μ α F) (hG : PolarGood P Z T μ α G) :
    PolarGood P Z T μ α (fun p => F p + G p) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  obtain ⟨hFm, ⟨C, hC⟩, hFt⟩ := hF
  obtain ⟨hGm, ⟨D, hD⟩, hGt⟩ := hG
  refine ⟨hFm.add hGm, ⟨C + D, fun p => (abs_add_le _ _).trans (add_le_add (hC p) (hD p))⟩, ?_⟩
  have hcomp : ∀ x : ℝ, Measurable fun ω => (Z ω / x, T ω) := fun x =>
    (hZ.div_const x).prodMk hT
  rw [integral_add (integrable_of_abs_le hFm hC) (integrable_of_abs_le hGm hD)]
  refine (hFt.add hGt).congr fun x => ?_
  exact (integral_add (f := fun ω => F (Z ω / x, T ω)) (g := fun ω => G (Z ω / x, T ω))
    (integrable_of_abs_le (hFm.comp (hcomp x)) fun ω => hC _)
    (integrable_of_abs_le (hGm.comp (hcomp x)) fun ω => hD _)).symm

omit [IsProbabilityMeasure P] in
private lemma polarGood_sum (hα : 0 < α) (hZ : Measurable Z) (hT : Measurable T)
    {F : ℕ → ℝ × E → ℝ} (s : Finset ℕ) (hF : ∀ i ∈ s, PolarGood P Z T μ α (F i)) :
    PolarGood P Z T μ α (fun p => ∑ i ∈ s, F i p) := by
  induction s using Finset.induction_on with
  | empty => simpa using polarGood_zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hF j (Finset.mem_insert_self j s)).add hα hZ hT
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- The basic test functions `1{r > u} g(θ)`, `u ≥ 1`: here
`E[1{Z > u x} g(T) | Z > x] = P(Z > u x) / P(Z > x) · E[g(T) | Z > u x] → u^(-α) ∫ g dμ`. -/
private lemma polarGood_indicator (hα : 0 < α) (hZ : Measurable Z) (hT : Measurable T)
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < Z ω}) (-α))
    (hconv : TendstoLawCond P (fun x => {ω | x < Z ω}) (fun _ => T) atTop μ)
    {u : ℝ} (hu : 1 ≤ u) {g : E → ℝ} (hg : Continuous g) {C : ℝ} (hgC : ∀ θ, |g θ| ≤ C) :
    PolarGood P Z T μ α (fun p => (Ioi u).indicator 1 p.1 * g p.2) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hu0 : 0 < u := one_pos.trans_le hu
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  refine ⟨((measurable_one.indicator measurableSet_Ioi).comp measurable_fst).mul
    (hg.measurable.comp measurable_snd), ⟨C, fun p => ?_⟩, ?_⟩
  · by_cases hp : p.1 ∈ Ioi u
    · simpa [indicator_of_mem hp] using hgC p.2
    · simpa [indicator_of_notMem hp] using hC0
  let gb : E →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨g, hg⟩ (2 * C) fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    linarith [abs_sub (g x) (g y), hgC x, hgC y]
  have hRHS : ∫ p, (Ioi u).indicator 1 p.1 * g p.2 ∂((paretoMeasure 1 α).prod μ) =
      u ^ (-α) * ∫ θ, gb θ ∂μ := by
    rw [integral_prod_mul (fun r => (Ioi u).indicator (1 : ℝ → ℝ) r) g,
      integral_indicator_one measurableSet_Ioi, paretoMeasure_one_real_Ioi hα hu]
    rfl
  rw [hRHS]
  have key := (hRV.tendsto hu0).mul ((hconv gb).comp (tendsto_id.const_mul_atTop hu0))
  refine key.congr' ?_
  have hpos := (tendsto_id.const_mul_atTop hu0).eventually hRV.eventually_pos
  filter_upwards [hpos, eventually_gt_atTop 0] with x hx hx0
  simp only [id, Function.comp_apply] at hx ⊢
  have hS : ∀ y : ℝ, MeasurableSet {ω | y < Z ω} := fun y => measurableSet_lt measurable_const hZ
  have hsub : {ω | u * x < Z ω} ⊆ {ω | x < Z ω} := fun ω (hω : u * x < Z ω) =>
    show x < Z ω by nlinarith
  have hind : ∀ ω, (Ioi u).indicator 1 (Z ω / x) * g (T ω) =
      {ω | u * x < Z ω}.indicator (fun ω => g (T ω)) ω := by
    intro ω
    by_cases hω : u * x < Z ω
    · have : Z ω / x ∈ Ioi u := by rw [mem_Ioi, lt_div_iff₀ hx0]; exact hω
      simp [indicator_of_mem this, indicator_of_mem (show ω ∈ {ω | u * x < Z ω} from hω)]
    · have : Z ω / x ∉ Ioi u := by rw [mem_Ioi, lt_div_iff₀ hx0]; exact hω
      simp [indicator_of_notMem this, indicator_of_notMem (show ω ∉ {ω | u * x < Z ω} from hω)]
  simp_rw [hind]
  rw [integral_cond_eq, integral_cond_eq, setIntegral_indicator (hS _),
    inter_eq_right.2 hsub, smul_eq_mul, smul_eq_mul]
  simp only [gb, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
  field_simp

omit [IsProbabilityMeasure P] in
/-- Approximation: a bounded measurable `F` which is approximated by good functions, up to an error
controlled by a good function of small integral, is good. -/
private lemma polarGood_of_approx (hα : 0 < α) (hZ : Measurable Z) (hT : Measurable T)
    {F : ℝ × E → ℝ} (hFm : Measurable F) (hFC : ∃ C, ∀ p, |F p| ≤ C)
    (h : ∀ ε > 0, ∃ G e : ℝ × E → ℝ, PolarGood P Z T μ α G ∧ PolarGood P Z T μ α e ∧
      (∀ p : ℝ × E, 1 < p.1 → |F p - G p| ≤ e p) ∧
      ∫ p, e p ∂((paretoMeasure 1 α).prod μ) < ε) :
    PolarGood P Z T μ α F := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  obtain ⟨C, hC⟩ := hFC
  refine ⟨hFm, ⟨C, hC⟩, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
  obtain ⟨G, e, ⟨hGm, ⟨CG, hCG⟩, hGt⟩, ⟨hem, ⟨Ce, hCe⟩, het⟩, hFGe, hint⟩ :=
    h (ε / 3) (by positivity)
  have h1 := Metric.tendsto_nhds.1 hGt (ε / 3) (by positivity)
  have h2 := het.eventually (gt_mem_nhds hint)
  have hπ : ∀ᵐ p ∂((paretoMeasure 1 α).prod μ), 1 < p.1 :=
    Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure
  have hB : |∫ p, F p ∂((paretoMeasure 1 α).prod μ) - ∫ p, G p ∂((paretoMeasure 1 α).prod μ)|
      ≤ ∫ p, e p ∂((paretoMeasure 1 α).prod μ) := by
    rw [← integral_sub (integrable_of_abs_le hFm hC) (integrable_of_abs_le hGm hCG)]
    refine (abs_integral_le_integral_abs).trans (integral_mono_ae ?_
      (integrable_of_abs_le hem hCe) ?_)
    · exact (integrable_of_abs_le (hFm.sub hGm) fun p =>
        (abs_sub _ _).trans (add_le_add (hC p) (hCG p))).abs
    · filter_upwards [hπ] with p hp using hFGe p hp
  filter_upwards [h1, h2, eventually_gt_atTop 0] with x hx1 hx2 hx0
  have hcomp : Measurable fun ω => (Z ω / x, T ω) := (hZ.div_const x).prodMk hT
  have hρ : ∀ᵐ ω ∂P[|{ω | x < Z ω}], 1 < (Z ω / x, T ω).1 := by
    filter_upwards [ae_cond_mem (measurableSet_lt measurable_const hZ)] with ω hω
    exact (one_lt_div hx0).2 hω
  have hA : |∫ ω, F (Z ω / x, T ω) ∂P[|{ω | x < Z ω}] - ∫ ω, G (Z ω / x, T ω) ∂P[|{ω | x < Z ω}]|
      ≤ ∫ ω, e (Z ω / x, T ω) ∂P[|{ω | x < Z ω}] := by
    rw [← integral_sub (f := fun ω => F (Z ω / x, T ω)) (g := fun ω => G (Z ω / x, T ω))
      (integrable_of_abs_le (hFm.comp hcomp) fun ω => hC _)
      (integrable_of_abs_le (hGm.comp hcomp) fun ω => hCG _)]
    refine (abs_integral_le_integral_abs).trans (integral_mono_ae ?_
      (integrable_of_abs_le (hem.comp hcomp) fun ω => hCe _) ?_)
    · exact (integrable_of_abs_le ((hFm.comp hcomp).sub (hGm.comp hcomp)) fun ω =>
        (abs_sub _ _).trans (add_le_add (hC _) (hCG _))).abs
    · filter_upwards [hρ] with ω hω using hFGe _ hω
  rw [Real.dist_eq] at hx1 ⊢
  have t1 := abs_sub_le (∫ ω, F (Z ω / x, T ω) ∂P[|{ω | x < Z ω}])
    (∫ ω, G (Z ω / x, T ω) ∂P[|{ω | x < Z ω}]) (∫ p, F p ∂((paretoMeasure 1 α).prod μ))
  have t2 := abs_sub_le (∫ ω, G (Z ω / x, T ω) ∂P[|{ω | x < Z ω}])
    (∫ p, G p ∂((paretoMeasure 1 α).prod μ)) (∫ p, F p ∂((paretoMeasure 1 α).prod μ))
  rw [abs_sub_comm (∫ p, G p ∂_)] at t2
  linarith

/-- The key step: `F(r, θ) = f(r • θ)` is good for bounded Lipschitz `f`. We discretize `r` on
the grid `uᵢ = 1 + i δ`, `δ = 1/(n+1)`, `i ≤ (n+1)²`, writing the discretization as a telescoping
sum of basic functions `1{r > uᵢ} gᵢ(θ)`; the error is at most
`min(2M, K δ ‖θ‖) + 2M · 1{r > n + 2}`. -/
private lemma polarGood_lipschitz (hα : 0 < α) (hZ : Measurable Z) (hT : Measurable T)
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < Z ω}) (-α))
    (hconv : TendstoLawCond P (fun x => {ω | x < Z ω}) (fun _ => T) atTop μ)
    {f : E → ℝ} {M : ℝ} (hfM : ∀ y, |f y| ≤ M) {K : ℝ≥0} (hfK : LipschitzWith K f) :
    PolarGood P Z T μ α (fun p => f (p.1 • p.2)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  have hfc := hfK.continuous
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
  set m : ℕ → ℕ := fun n => (n + 1) ^ 2 with hmdef
  set u : ℕ → ℕ → ℝ := fun n i => 1 + i * δ n with hudef
  set a : ℕ → ℕ → E → ℝ := fun n i θ => if i = 0 then 0 else f (u n (i - 1) • θ) with hadef
  set G : ℕ → ℝ × E → ℝ := fun n p => ∑ i ∈ Finset.range (m n + 1),
    (Ioi (u n i)).indicator 1 p.1 * (a n (i + 1) p.2 - a n i p.2) with hGdef
  set e : ℕ → ℝ × E → ℝ := fun n p => (Ioi 1).indicator 1 p.1 * min (2 * M) (K * δ n * ‖p.2‖)
    + (Ioi (u n (m n))).indicator 1 p.1 * (2 * M) with hedef
  have hδ : ∀ n, 0 < δ n := fun n => by simp only [hδdef]; positivity
  have hu1 : ∀ n i, 1 ≤ u n i := fun n i => by
    simp only [hudef]; linarith [mul_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ i) (hδ n).le]
  have ha_cont : ∀ n i, Continuous (a n i) := by
    intro n i
    rcases i with _ | i
    · simpa [hadef] using continuous_const
    · exact (hfc.comp (continuous_const.smul continuous_id) :
        Continuous fun θ => f (u n i • θ)).congr fun θ => by simp [hadef]
  have ha_bd : ∀ n i θ, |a n i θ| ≤ M := by
    intro n i θ
    rcases i with _ | i
    · simpa [hadef] using hM
    · simpa [hadef] using hfM _
  have hGgood : ∀ n, PolarGood P Z T μ α (G n) := fun n =>
    polarGood_sum hα hZ hT _ fun i _ => polarGood_indicator hα hZ hT hRV hconv (hu1 n i)
      ((ha_cont n (i + 1)).sub (ha_cont n i)) (C := 2 * M) fun θ => by
        show |a n (i + 1) θ - a n i θ| ≤ 2 * M
        linarith [abs_sub (a n (i + 1) θ) (a n i θ), ha_bd n (i + 1) θ, ha_bd n i θ]
  have hmin_cont : ∀ n, Continuous fun θ : E => min (2 * M) (K * δ n * ‖θ‖) := fun n =>
    continuous_const.min (continuous_const.mul continuous_norm)
  have hmin_bd : ∀ n (θ : E), |min (2 * M) (K * δ n * ‖θ‖)| ≤ 2 * M := fun n θ => by
    rw [abs_of_nonneg (le_min (by linarith)
      (mul_nonneg (mul_nonneg K.coe_nonneg (hδ n).le) (norm_nonneg θ)))]
    exact min_le_left _ _
  have hegood : ∀ n, PolarGood P Z T μ α (e n) := fun n =>
    (polarGood_indicator hα hZ hT hRV hconv le_rfl (hmin_cont n) (hmin_bd n)).add hα hZ hT
      (polarGood_indicator hα hZ hT hRV hconv (hu1 n (m n)) continuous_const
        (C := 2 * M) fun _ => by rw [abs_of_nonneg (by linarith)])
  have hum : ∀ n, u n (m n) = n + 2 := fun n => by
    simp only [hudef, hmdef, hδdef]
    push_cast
    field_simp
    ring
  have heint : ∀ n, ∫ p, e n p ∂((paretoMeasure 1 α).prod μ) =
      ∫ θ, min (2 * M) (K * δ n * ‖θ‖) ∂μ + ((n : ℝ) + 2) ^ (-α) * (2 * M) := by
    intro n
    have I1 : Integrable (fun p : ℝ × E => (Ioi (1 : ℝ)).indicator (1 : ℝ → ℝ) p.1 *
        min (2 * M) (K * δ n * ‖p.2‖)) ((paretoMeasure 1 α).prod μ) := by
      refine integrable_of_abs_le
        (((measurable_one.indicator measurableSet_Ioi).comp measurable_fst).mul
          ((hmin_cont n).measurable.comp measurable_snd)) (C := 2 * M) fun p => ?_
      by_cases hp : p.1 ∈ Ioi (1 : ℝ)
      · simpa [indicator_of_mem hp] using hmin_bd n p.2
      · simp [indicator_of_notMem hp]; linarith
    have I2 : Integrable (fun p : ℝ × E => (Ioi (u n (m n))).indicator (1 : ℝ → ℝ) p.1 *
        (2 * M)) ((paretoMeasure 1 α).prod μ) := by
      refine integrable_of_abs_le (((measurable_one.indicator measurableSet_Ioi).comp
        measurable_fst).mul measurable_const) (C := 2 * M) fun p => ?_
      by_cases hp : p.1 ∈ Ioi (u n (m n))
      · simp [indicator_of_mem hp, abs_of_nonneg hM]
      · simp [indicator_of_notMem hp]; linarith
    simp only [hedef]
    rw [integral_add I1 I2,
      integral_prod_mul (fun r => (Ioi (1 : ℝ)).indicator (1 : ℝ → ℝ) r)
        (fun θ => min (2 * M) (K * δ n * ‖θ‖)),
      integral_prod_mul (fun r => (Ioi (u n (m n))).indicator (1 : ℝ → ℝ) r) (fun _ => 2 * M),
      integral_indicator_one measurableSet_Ioi, integral_indicator_one measurableSet_Ioi,
      paretoMeasure_one_real_Ioi hα le_rfl, paretoMeasure_one_real_Ioi hα (hu1 n (m n)),
      hum, integral_const]
    simp
  have hlim : Tendsto (fun n => ∫ p, e n p ∂((paretoMeasure 1 α).prod μ)) atTop (𝓝 0) := by
    simp_rw [heint]
    have h1 : Tendsto (fun n => ∫ θ, min (2 * M) (K * δ n * ‖θ‖) ∂μ) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => 2 * M)
        (fun n => (hmin_cont n).aestronglyMeasurable) (integrable_const _)
        (fun n => ae_of_all _ fun θ => by simpa [Real.norm_eq_abs] using hmin_bd n θ)
        (ae_of_all _ fun θ => (show Tendsto (fun n => min (2 * M) (K * δ n * ‖θ‖)) atTop
          (𝓝 (min (2 * M) (K * 0 * ‖θ‖))) from
            tendsto_const_nhds.min
              ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (K : ℝ)).mul_const ‖θ‖)))
      simpa [min_eq_right (show (0 : ℝ) ≤ 2 * M by linarith)] using this
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2) ^ (-α) * (2 * M)) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop hα).comp
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)).mul_const (2 * M)
    simpa using h1.add h2
  refine polarGood_of_approx hα hZ hT (hfc.measurable.comp (continuous_smul.measurable))
    ⟨M, fun p => hfM _⟩ fun ε hε => ?_
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨G n, e n, hGgood n, hegood n, fun p hp => ?_, hn⟩
  obtain ⟨r, θ⟩ := p
  simp only at hp ⊢
  set c := ⌈(r - 1) / δ n⌉₊ with hc
  have hiff : ∀ i : ℕ, u n i < r ↔ i < c := fun i => by
    rw [hc, Nat.lt_ceil, lt_div_iff₀ (hδ n)]
    simp only [hudef]
    constructor <;> intro h <;> linarith
  have hG : G n (r, θ) = a n (min (m n + 1) c) θ := by
    simp only [hGdef]
    have hterm : ∀ i ∈ Finset.range (m n + 1),
        (Ioi (u n i)).indicator 1 r * (a n (i + 1) θ - a n i θ) =
          if i < c then a n (i + 1) θ - a n i θ else 0 := by
      intro i _
      by_cases hi : i < c
      · simp [indicator_of_mem (show r ∈ Ioi (u n i) from (hiff i).2 hi), hi]
      · simp [indicator_of_notMem (show r ∉ Ioi (u n i) from fun h => hi ((hiff i).1 h)), hi]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    have hfilter : (Finset.range (m n + 1)).filter (· < c) = Finset.range (min (m n + 1) c) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilter, Finset.sum_range_sub (fun i => a n i θ)]
    simp [hadef]
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1
    (Nat.ceil_pos.2 (div_pos (by linarith) (hδ n))))
  have he1 : (Ioi (1 : ℝ)).indicator 1 r = (1 : ℝ) := by
    rw [indicator_of_mem (show r ∈ Ioi (1 : ℝ) from hp)]; rfl
  have hind0 : 0 ≤ (Ioi (u n (m n))).indicator (1 : ℝ → ℝ) r * (2 * M) :=
    mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (by linarith)
  have hmin0 : 0 ≤ min (2 * M) (K * δ n * ‖θ‖) := le_min (by linarith)
    (mul_nonneg (mul_nonneg K.coe_nonneg (hδ n).le) (norm_nonneg θ))
  rw [hG]
  rcases le_or_gt c (m n) with hcm | hcm
  · have hk : min (m n + 1) c = (c - 1) + 1 := by omega
    rw [hk]
    simp only [hadef, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    have hlo : u n (c - 1) < r := (hiff _).2 (by omega)
    have hhi : r ≤ u n (c - 1) + δ n := by
      have h1 := Nat.le_ceil ((r - 1) / δ n)
      rw [← hc, div_le_iff₀ (hδ n)] at h1
      simp only [hudef, Nat.cast_sub hc1, Nat.cast_one]
      nlinarith
    have hlip : |f (r • θ) - f (u n (c - 1) • θ)| ≤ K * δ n * ‖θ‖ := by
      have h := hfK.dist_le_mul (r • θ) (u n (c - 1) • θ)
      rw [Real.dist_eq, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (sub_pos.2 hlo)] at h
      calc _ ≤ K * ((r - u n (c - 1)) * ‖θ‖) := h
        _ ≤ K * (δ n * ‖θ‖) := by gcongr; linarith
        _ = _ := by ring
    have h2M : |f (r • θ) - f (u n (c - 1) • θ)| ≤ 2 * M := by
      linarith [abs_sub (f (r • θ)) (f (u n (c - 1) • θ)), hfM (r • θ), hfM (u n (c - 1) • θ)]
    simp only [hedef, he1, one_mul]
    linarith [le_min h2M hlip]
  · have hk : min (m n + 1) c = m n + 1 := by omega
    rw [hk]
    simp only [hadef, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    have hlt : u n (m n) < r := (hiff _).2 hcm
    have h2M : |f (r • θ) - f (u n (m n) • θ)| ≤ 2 * M := by
      linarith [abs_sub (f (r • θ)) (f (u n (m n) • θ)), hfM (r • θ), hfM (u n (m n) • θ)]
    simp only [hedef, he1, one_mul, indicator_of_mem (show r ∈ Ioi (u n (m n)) from hlt),
      Pi.one_apply]
    linarith

/-- **Polar decomposition, direct part** ([BS09, Theorem 2.1, (iii) ⇒ (ii)], [KS20,
Theorem 2.2.3]). Let `Z` be a random variable whose tail `P(Z > x)` is regularly varying with
index `-α`, `α > 0`, and let `T` be a random vector such that the law of `T` given `Z > x`
converges weakly to `μ`. Then the law of `(Z / x) • T` given `Z > x` converges weakly to the law of
`R • Θ`, where `R` is Pareto(`α`) and independent of `Θ ∼ μ`. -/
theorem tendstoLawCond_smul (hα : 0 < α) (hZ : Measurable Z) (hT : Measurable T)
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < Z ω}) (-α))
    (hconv : TendstoLawCond P (fun x => {ω | x < Z ω}) (fun _ => T) atTop μ) :
    TendstoLawCond P (fun x => {ω | x < Z ω}) (fun x ω => (Z ω / x) • T ω) atTop
      (((paretoMeasure 1 α).prod μ).map fun p => p.1 • p.2) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hsmul : Measurable fun p : ℝ × E => p.1 • p.2 := continuous_smul.measurable
  have hY : ∀ x : ℝ, Measurable fun ω => (Z ω / x) • T ω := fun x =>
    hsmul.comp ((hZ.div_const x).prodMk hT)
  have hμs : ∀ᶠ x in atTop,
      IsProbabilityMeasure ((P[|{ω | x < Z ω}]).map fun ω => (Z ω / x) • T ω) := by
    filter_upwards [hRV.eventually_pos] with x hx
    have : IsProbabilityMeasure (P[|{ω | x < Z ω}]) :=
      cond_isProbabilityMeasure (by
        rw [measureReal_def] at hx; exact fun h => by simp [h] at hx)
    infer_instance
  have : IsProbabilityMeasure (((paretoMeasure 1 α).prod μ).map fun p => p.1 • p.2) :=
    inferInstance
  intro f
  have key := tendsto_integral_of_forall_lipschitz hμs
    (μ := ((paretoMeasure 1 α).prod μ).map fun p => p.1 • p.2) ?_ f
  · refine key.congr fun x => ?_
    rw [integral_map (hY x).aemeasurable f.continuous.aestronglyMeasurable]
  intro g ⟨C, hC⟩ ⟨L, hL⟩
  have hgM : ∀ y, |g y| ≤ |g 0| + C := fun y => by
    have := hC y 0
    rw [Real.dist_eq] at this
    linarith [abs_sub_abs_le_abs_sub (g y) (g 0)]
  have := (polarGood_lipschitz hα hZ hT hRV hconv hgM hL).2.2
  rw [integral_map hsmul.aemeasurable hL.continuous.aestronglyMeasurable]
  refine this.congr fun x => ?_
  rw [integral_map (hY x).aemeasurable hL.continuous.aestronglyMeasurable]

end Polar

end ExtremeValueTheory
