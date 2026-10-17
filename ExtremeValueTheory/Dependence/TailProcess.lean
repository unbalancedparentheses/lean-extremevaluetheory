/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Basic
import ExtremeValueTheory.ForMathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Pareto
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration

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
  [KS20, Chapter 5]).
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

/-- If the random elements eventually satisfy `g (Y i) = 0` almost surely on the conditioning
events, for a nonnegative bounded continuous `g`, then `g = 0` almost surely under the limit. -/
theorem TendstoLawCond.ae_eq_zero [OpensMeasurableSpace E] [l.NeBot] (h : TendstoLawCond P s Y l ν) [IsFiniteMeasure ν]
    (g : E →ᵇ ℝ) (hg : ∀ y, 0 ≤ g y) (hY : ∀ᶠ i in l, ∀ᵐ ω ∂P[|s i], g (Y i ω) = 0) :
    ∀ᵐ y ∂ν, g y = 0 := by
  have h0 : ∫ y, g y ∂ν = 0 := by
    refine tendsto_nhds_unique (h g) (tendsto_const_nhds.congr' ?_)
    filter_upwards [hY] with i hi
    rw [integral_eq_zero_of_ae hi]
  exact (integral_eq_zero_iff_of_nonneg hg (g.integrable ν)).1 h0

/-- Weak limits of conditional laws are unique. -/
theorem TendstoLawCond.unique [HasOuterApproxClosed E] [BorelSpace E] [l.NeBot]
    {ν' : Measure E} [IsFiniteMeasure ν] [IsFiniteMeasure ν'] (h : TendstoLawCond P s Y l ν)
    (h' : TendstoLawCond P s Y l ν') : ν = ν' :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => tendsto_nhds_unique (h f) (h' f)

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
Chapter 5]).  Let `Z` be a random variable whose tail `P(Z > x)` is regularly varying with
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

omit [IsProbabilityMeasure P] [IsProbabilityMeasure μ] in
/-- `(ρ ⊗ μ.map g).map (r, θ) ↦ r • θ` rewritten on `ρ ⊗ μ`. -/
private lemma map_prod_map_smul {G F : Type*} {_ : MeasurableSpace G} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (ρ : Measure ℝ) [SFinite ρ]
    {μ : Measure G} [SFinite μ] {g : G → F} (hg : Measurable g) :
    (ρ.prod (μ.map g)).map (fun p => p.1 • p.2) = (ρ.prod μ).map (fun p => p.1 • g p.2) := by
  have h : ρ.prod (μ.map g) = (ρ.prod μ).map (Prod.map id g) := by
    rw [← Measure.map_prod_map _ _ measurable_id hg, Measure.map_id]
  rw [h, Measure.map_map continuous_smul.measurable (measurable_id.prodMap hg)]
  rfl

/-- **Polar decomposition, joint form** ([BS09, Theorem 2.1, (iii) ⇒ (ii)]). If `P(Z > x)` is
regularly varying with index `-α`, `α > 0`, and the law of `V / Z` given `Z > x` converges weakly
to `μ`, then the law of `(Z / x, V / x)` given `Z > x` converges weakly to the law of `(R, R • Θ)`,
with `R` Pareto(`α`) independent of `Θ ∼ μ`. -/
theorem tendstoLawCond_polar {V : Ω → E} (hα : 0 < α) (hZ : Measurable Z) (hV : Measurable V)
    (hRV : IsRegularlyVarying (fun x => P.real {ω | x < Z ω}) (-α))
    (hconv : TendstoLawCond P (fun x => {ω | x < Z ω}) (fun _ ω => (Z ω)⁻¹ • V ω) atTop μ) :
    TendstoLawCond P (fun x => {ω | x < Z ω}) (fun x ω => (Z ω / x, x⁻¹ • V ω)) atTop
      (((paretoMeasure 1 α).prod μ).map fun p => (p.1, p.1 • p.2)) := by
  have hg : Continuous fun θ : E => ((1 : ℝ), θ) := continuous_const.prodMk continuous_id
  have hc' := hconv.comp hg
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have key := tendstoLawCond_smul (E := ℝ × E) (T := fun ω => ((1 : ℝ), (Z ω)⁻¹ • V ω)) hα hZ
    (measurable_const.prodMk (hZ.inv.smul hV)) hRV hc'
  rw [map_prod_map_smul _ hg.measurable] at key
  have hfun : (fun p : ℝ × E => p.1 • ((1 : ℝ), p.2)) = fun p => (p.1, p.1 • p.2) := by
    funext p; simp [Prod.smul_mk]
  rw [hfun] at key
  refine key.congr ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  filter_upwards [ae_cond_mem (measurableSet_lt measurable_const hZ)] with ω hω
  have hZ0 : Z ω ≠ 0 := (hx.trans hω).ne'
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, smul_smul]
  congr 2
  field_simp

end Polar

/-! ### The converse -/

section Converse

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  {Z : Ω → ℝ} {V : Ω → E} {ν : Measure (ℝ × E)} [IsProbabilityMeasure ν] {α : ℝ}

omit [IsProbabilityMeasure P] [IsProbabilityMeasure ν] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E] in
/-- Under `ν`, the first coordinate is `> 1` almost surely if its law is Pareto. -/
theorem ae_one_lt_fst_of_map_fst (hν : ν.map Prod.fst = paretoMeasure 1 α) :
    ∀ᵐ p ∂ν, 1 < p.1 :=
  ae_of_ae_map measurable_fst.aemeasurable (hν ▸ ae_one_lt_paretoMeasure)

/-- **Polar decomposition, converse: regular variation** ([BS09, Theorem 2.1, (ii) ⇒ (i)]). If
the law of `(Z / x, V / x)` given `Z > x` converges weakly to `ν` whose first marginal is
Pareto(`α`), then `P(Z > x)` is regularly varying with index `-α`. -/
theorem isRegularlyVarying_of_tendstoLawCond (hα : 0 < α) (hZ : Measurable Z)
    (hV : Measurable V) (hν : ν.map Prod.fst = paretoMeasure 1 α)
    (h : TendstoLawCond P (fun x => {ω | x < Z ω}) (fun x ω => (Z ω / x, x⁻¹ • V ω)) atTop ν) :
    IsRegularlyVarying (fun x => P.real {ω | x < Z ω}) (-α) := by
  have hS : ∀ y : ℝ, MeasurableSet {ω | y < Z ω} := fun y => measurableSet_lt measurable_const hZ
  have hne := h.eventually_measure_ne_zero
  have hpos : ∀ᶠ x in atTop, 0 < P.real {ω | x < Z ω} := by
    filter_upwards [hne] with x hx
    exact ENNReal.toReal_pos hx (measure_ne_top _ _)
  have hY : ∀ x : ℝ, Measurable fun ω => (Z ω / x, x⁻¹ • V ω) := fun x =>
    (hZ.div_const x).prodMk (hV.const_smul _)
  -- the case `u ≥ 1`
  have hge : ∀ u : ℝ, 1 ≤ u → Tendsto (fun x => P.real {ω | u * x < Z ω} / P.real {ω | x < Z ω})
      atTop (𝓝 (u ^ (-α))) := by
    intro u hu
    have hμs : ∀ᶠ x in atTop, IsProbabilityMeasure
        ((P[|{ω | x < Z ω}]).map fun ω => (Z ω / x, x⁻¹ • V ω)) := by
      filter_upwards [hne] with x hx
      have := cond_isProbabilityMeasure (μ := P) hx
      infer_instance
    have hlim := tendsto_measure_of_null_frontier_of_forall_integral_tendsto hμs (μ := ν)
      (fun f => (h f).congr fun x => by
        rw [integral_map (hY x).aemeasurable f.continuous.aestronglyMeasurable])
      (E := {p : ℝ × E | u < p.1}) (by
        refine measure_mono_null (frontier_lt_subset_eq continuous_const continuous_fst) ?_
        have : ν {p : ℝ × E | u = p.1} = ν.map Prod.fst {u} := by
          rw [Measure.map_apply measurable_fst (measurableSet_singleton u)]
          congr 1; ext p; simp [eq_comm]
        rw [this, hν, paretoMeasure_singleton])
    have hνu : ν {p : ℝ × E | u < p.1} = ENNReal.ofReal (u ^ (-α)) := by
      rw [← paretoMeasure_one_Ioi hα hu, ← hν, Measure.map_apply measurable_fst measurableSet_Ioi]
      rfl
    rw [hνu] at hlim
    have hlim' := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hlim
    rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos (one_pos.trans_le hu) _).le] at hlim'
    refine hlim'.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hsub : {ω | u * x < Z ω} ⊆ {ω | x < Z ω} := fun ω (hω : u * x < Z ω) =>
      show x < Z ω by nlinarith
    have hpre : (fun ω => (Z ω / x, x⁻¹ • V ω)) ⁻¹' {p : ℝ × E | u < p.1} = {ω | u * x < Z ω} := by
      ext ω; simp [lt_div_iff₀ hx]
    simp only [Function.comp_apply]
    rw [Measure.map_apply (hY x) (measurableSet_lt measurable_const measurable_fst), hpre,
      cond_apply (hS x), inter_eq_right.2 hsub, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ← measureReal_def, ← measureReal_def, div_eq_inv_mul]
  refine ⟨hpos, fun c hc => ?_⟩
  rcases le_or_gt 1 c with hc1 | hc1
  · exact hge c hc1
  · -- invert: `f(c x) / f(x) = (f(c⁻¹ (c x)) / f(c x))⁻¹`
    have h1 := (hge c⁻¹ (one_le_inv₀ hc |>.2 hc1.le)).comp (tendsto_id.const_mul_atTop hc)
    have h2 := h1.inv₀ (Real.rpow_pos_of_pos (inv_pos.2 hc) _).ne'
    rw [Real.inv_rpow hc.le, Real.rpow_neg hc.le, inv_inv, ← Real.rpow_neg hc.le] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, id, inv_div, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- **Polar decomposition, converse: spectral convergence** ([BS09, Theorem 2.1, (ii) ⇒ (iii)]).
If the law of `(Z / x, V / x)` given `Z > x` converges weakly to `ν` whose first marginal is
Pareto(`α`), then the law of `V / Z` given `Z > x` converges weakly to the law of `Y / R` under
`(R, Y) ∼ ν`. -/
theorem tendstoLawCond_spectral_of_tendstoLawCond (hZ : Measurable Z)
    (hν : ν.map Prod.fst = paretoMeasure 1 α)
    (h : TendstoLawCond P (fun x => {ω | x < Z ω}) (fun x ω => (Z ω / x, x⁻¹ • V ω)) atTop ν) :
    TendstoLawCond P (fun x => {ω | x < Z ω}) (fun _ ω => (Z ω)⁻¹ • V ω) atTop
      (ν.map fun p => p.1⁻¹ • p.2) := by
  have hφ : Continuous fun p : ℝ × E => (max p.1 1)⁻¹ • p.2 :=
    ((continuous_fst.max continuous_const).inv₀ fun p =>
      (one_pos.trans_le (le_max_right _ _)).ne').smul continuous_snd
  have key := h.comp hφ
  have hmap : ν.map (fun p : ℝ × E => (max p.1 1)⁻¹ • p.2) = ν.map fun p => p.1⁻¹ • p.2 := by
    refine Measure.map_congr ?_
    filter_upwards [ae_one_lt_fst_of_map_fst hν] with p hp
    rw [max_eq_left hp.le]
  rw [hmap] at key
  refine key.congr ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  filter_upwards [ae_cond_mem (measurableSet_lt measurable_const hZ)] with ω hω
  have hZ0 : Z ω ≠ 0 := (hx.trans hω).ne'
  have h1 : max (Z ω / x) 1 = Z ω / x := max_eq_left ((one_lt_div hx).2 hω).le
  simp only [h1, smul_smul]
  congr 1
  field_simp

/-- **Independence of the radial and spectral parts** ([BS09, Theorem 2.1], [KS20,
Chapter 5]). Under the hypotheses of `tendstoLawCond_spectral_of_tendstoLawCond`, `ν` is the law of
`(R, R • Θ)` with `R` Pareto(`α`) independent of `Θ = Y / R`. -/
theorem eq_map_prod_of_tendstoLawCond (hα : 0 < α) (hZ : Measurable Z) (hV : Measurable V)
    (hν : ν.map Prod.fst = paretoMeasure 1 α)
    (h : TendstoLawCond P (fun x => {ω | x < Z ω}) (fun x ω => (Z ω / x, x⁻¹ • V ω)) atTop ν) :
    ν = (((paretoMeasure 1 α).prod (ν.map fun p => p.1⁻¹ • p.2)).map
      fun p => (p.1, p.1 • p.2)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have : IsProbabilityMeasure (ν.map fun p => p.1⁻¹ • p.2) :=
    inferInstance
  exact h.unique (tendstoLawCond_polar hα hZ hV
    (isRegularlyVarying_of_tendstoLawCond hα hZ hV hν h)
    (tendstoLawCond_spectral_of_tendstoLawCond hZ hν h))

omit [IsProbabilityMeasure ν] in
/-- The first marginal of the law of `(R, R • Θ)` is Pareto. -/
theorem map_fst_map_polar (hα : 0 < α) (μ : Measure E) [IsProbabilityMeasure μ] :
    (((paretoMeasure 1 α).prod μ).map fun p => (p.1, p.1 • p.2)).map Prod.fst =
      paretoMeasure 1 α := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  rw [Measure.map_map measurable_fst (measurable_fst.prodMk continuous_smul.measurable)]
  change ((paretoMeasure 1 α).prod μ).map Prod.fst = _
  simp

omit [IsProbabilityMeasure ν] in
/-- **The Basrak–Segers equivalence for a random vector** ([BS09, Theorem 2.1, (ii) ⇔ (iii)]).
The following are equivalent, for `α > 0`:
* `P(Z > x)` is regularly varying with index `-α` and the law of `V / Z` given `Z > x` converges
  weakly to some probability measure;
* the law of `(Z / x, V / x)` given `Z > x` converges weakly to some probability measure with
  Pareto(`α`) first marginal. -/
theorem polar_iff (hα : 0 < α) (hZ : Measurable Z) (hV : Measurable V) :
    (IsRegularlyVarying (fun x => P.real {ω | x < Z ω}) (-α) ∧
      ∃ μ : Measure E, IsProbabilityMeasure μ ∧
        TendstoLawCond P (fun x => {ω | x < Z ω}) (fun _ ω => (Z ω)⁻¹ • V ω) atTop μ) ↔
    ∃ ν : Measure (ℝ × E), IsProbabilityMeasure ν ∧ ν.map Prod.fst = paretoMeasure 1 α ∧
      TendstoLawCond P (fun x => {ω | x < Z ω}) (fun x ω => (Z ω / x, x⁻¹ • V ω)) atTop ν := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  constructor
  · rintro ⟨hRV, μ, hμ, hconv⟩
    exact ⟨_, inferInstance,
      map_fst_map_polar hα μ, tendstoLawCond_polar hα hZ hV hRV hconv⟩
  · rintro ⟨ν, hν, hfst, h⟩
    exact ⟨isRegularlyVarying_of_tendstoLawCond hα hZ hV hfst h, _,
      inferInstance,
      tendstoLawCond_spectral_of_tendstoLawCond hZ hfst h⟩

end Converse

/-! ### Regularly varying time series -/

section TimeSeries

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q]

/-- A time series `(X_t)_{t ∈ ℤ}` is *jointly regularly varying with index `α`* and *spectral tail
process* `(Θ_t)_{t ∈ ℤ}` (defined on `(Ω', Q)`) if `P(|X_0| > x)` is regularly varying with index
`-α` and, for every finite window `S ⊆ ℤ`, the law of `(X_t / |X_0|)_{t ∈ S}` given `|X_0| > x`
converges weakly to the law of `(Θ_t)_{t ∈ S}` ([BS09, Theorem 2.1 (iii)], [KS20,
Chapter 5]). Windows are arbitrary finite sets, which covers the windows
`{s, …, t}` of [KS20] and `{-n, …, n}` of [BS09]. -/
def HasSpectralTailProcess (P : Measure Ω) (X : ℤ → Ω → ℝ) (α : ℝ) (Q : Measure Ω')
    (Θ : ℤ → Ω' → ℝ) : Prop :=
  IsRegularlyVarying (fun x => P.real {ω | x < |X 0 ω|}) (-α) ∧
    ∀ S : Finset ℤ, TendstoLawCond P (fun x => {ω | x < |X 0 ω|})
      (fun _ ω (t : S) => X t ω / |X 0 ω|) atTop (Q.map fun ω' (t : S) => Θ t ω')

/-- A time series `(X_t)_{t ∈ ℤ}` has *tail process* `(Y_t)_{t ∈ ℤ}` (defined on `(Ω', Q)`) with
index `α` if `|Y_0|` is Pareto(`α`), `P(|Y_0| > y) = y^(-α)` for `y ≥ 1`, and, for every finite
window `S ⊆ ℤ`, the law of `(X_t / x)_{t ∈ S}` given `|X_0| > x` converges weakly to the law of
`(Y_t)_{t ∈ S}` ([BS09, Theorem 2.1 (ii)], [KS20, Chapter 5]). -/
def HasTailProcess (P : Measure Ω) (X : ℤ → Ω → ℝ) (α : ℝ) (Q : Measure Ω')
    (Y : ℤ → Ω' → ℝ) : Prop :=
  Q.map (fun ω' => |Y 0 ω'|) = paretoMeasure 1 α ∧
    ∀ S : Finset ℤ, TendstoLawCond P (fun x => {ω | x < |X 0 ω|})
      (fun x ω (t : S) => X t ω / x) atTop (Q.map fun ω' (t : S) => Y t ω')

omit [IsProbabilityMeasure P] in
/-- The spectral tail process satisfies `|Θ_0| = 1` almost surely ([BS09, Theorem 2.1]). -/
theorem HasSpectralTailProcess.ae_abs_eq_one {Θ : ℤ → Ω' → ℝ} (hΘm : ∀ t, Measurable (Θ t))
    (hX : Measurable (X 0)) (h : HasSpectralTailProcess P X α Q Θ) :
    ∀ᵐ ω' ∂Q, |Θ 0 ω'| = 1 := by
  set S : Finset ℤ := {0}
  have h0 : (0 : ℤ) ∈ S := Finset.mem_singleton_self 0
  let g : (S → ℝ) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun y => min 1 |(|y ⟨0, h0⟩|) - 1|, continuous_const.min
      (((continuous_apply _).abs.sub continuous_const).abs)⟩ 1 fun y z => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have := min_le_left 1 |(|y ⟨0, h0⟩|) - 1|
      have := min_le_left 1 |(|z ⟨0, h0⟩|) - 1|
      have : 0 ≤ min 1 |(|y ⟨0, h0⟩|) - 1| := le_min zero_le_one (abs_nonneg _)
      have : 0 ≤ min 1 |(|z ⟨0, h0⟩|) - 1| := le_min zero_le_one (abs_nonneg _)
      rw [abs_le]; constructor <;> linarith
  have hg0 : ∀ y, 0 ≤ g y := fun y => le_min zero_le_one (abs_nonneg _)
  have key := (h.2 S).ae_eq_zero g hg0 (by
    filter_upwards [eventually_gt_atTop 0] with x hx
    filter_upwards [ae_cond_mem (measurableSet_lt measurable_const (continuous_abs.measurable.comp hX))] with ω hω
    have hne : |X 0 ω| ≠ 0 := (hx.trans hω).ne'
    change min 1 (abs (abs (X 0 ω / abs (X 0 ω)) - 1)) = 0
    rw [abs_div, abs_abs, div_self hne]; simp)
  have hm : Measurable fun ω' (t : S) => Θ t ω' := measurable_pi_iff.2 fun t : S => hΘm (t : ℤ)
  have := ae_of_ae_map hm.aemeasurable key
  filter_upwards [this] with ω' hω'
  change min 1 |(|Θ 0 ω'|) - 1| = 0 at hω'
  rcases min_eq_iff.1 hω' with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 one_ne_zero
  · linarith [abs_eq_zero.1 h1]

omit [IsProbabilityMeasure Q] in
private lemma measurable_window {Y : ℤ → Ω' → ℝ} (hY : ∀ t, Measurable (Y t)) (S : Finset ℤ) :
    Measurable fun ω' (t : S) => Y t ω' :=
  measurable_pi_iff.2 fun t : S => hY (t : ℤ)

private lemma window_div_abs (X : ℤ → Ω → ℝ) (S : Finset ℤ) :
    (fun (_ : ℝ) ω (t : S) => X t ω / |X 0 ω|) =
      fun _ ω => (|X 0 ω|)⁻¹ • fun t : S => X t ω := by
  funext x ω t; simp [div_eq_inv_mul]

private lemma window_div (X : ℤ → Ω → ℝ) (S : Finset ℤ) :
    (fun (x : ℝ) ω (t : S) => X t ω / x) = fun x ω => x⁻¹ • fun t : S => X t ω := by
  funext x ω t; simp [div_eq_inv_mul]

/-- **From the spectral tail process to the tail process** ([BS09, Theorem 2.1, (iii) ⇒ (ii)],
[KS20, Chapter 5]): if `(X_t)` has spectral tail process `(Θ_t)`, then it has tail process
`Y_t = R Θ_t`, with `R` Pareto(`α`) independent of `(Θ_t)`, realized on the product space. -/
theorem HasSpectralTailProcess.hasTailProcess {Θ : ℤ → Ω' → ℝ} (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (h : HasSpectralTailProcess P X α Q Θ) :
    HasTailProcess P X α ((paretoMeasure 1 α).prod Q) (fun t p => p.1 * Θ t p.2) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hZ : Measurable fun ω => |X 0 ω| := continuous_abs.measurable.comp (hX 0)
  constructor
  · have hae : ∀ᵐ p ∂((paretoMeasure 1 α).prod Q), |p.1 * Θ 0 p.2| = p.1 := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure,
        Measure.quasiMeasurePreserving_snd.ae (h.ae_abs_eq_one hΘm (hX 0))] with p h1 h2
      rw [abs_mul, h2, mul_one, abs_of_pos (one_pos.trans h1)]
    rw [Measure.map_congr hae]
    simp
  · intro S
    have hconv := h.2 S
    rw [window_div_abs] at hconv
    have key := (tendstoLawCond_polar hα hZ (measurable_window hX S) h.1 hconv).comp
      continuous_snd
    rw [Measure.map_map measurable_snd (measurable_fst.prodMk continuous_smul.measurable)] at key
    change TendstoLawCond _ _ _ _ (((paretoMeasure 1 α).prod _).map fun p => p.1 • p.2) at key
    rw [map_prod_map_smul _ (measurable_window hΘm S)] at key
    rw [window_div]
    exact key

omit [IsProbabilityMeasure Q] in
/-- The joint convergence of `(|X_0| / x, (X_t / x)_{t ∈ S})` for a time series with a tail
process. -/
private lemma HasTailProcess.joint {Y : ℤ → Ω' → ℝ} (hYm : ∀ t, Measurable (Y t))
    (h : HasTailProcess P X α Q Y) (S : Finset ℤ) :
    TendstoLawCond P (fun x => {ω | x < |X 0 ω|})
      (fun x ω => (|X 0 ω| / x, x⁻¹ • fun t : S => X t ω)) atTop
      (Q.map fun ω' => (|Y 0 ω'|, fun t : S => Y t ω')) := by
  classical
  set S' := insert 0 S
  let π : (S' → ℝ) → ℝ × (S → ℝ) := fun y =>
    (|y ⟨0, Finset.mem_insert_self 0 S⟩|, fun t => y ⟨t, Finset.mem_insert_of_mem t.2⟩)
  have hπ : Continuous π :=
    (continuous_apply _).abs.prodMk (continuous_pi fun t => continuous_apply _)
  have key := (h.2 S').comp hπ
  rw [Measure.map_map hπ.measurable (measurable_window hYm S')] at key
  refine key.congr ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  refine ae_of_all _ fun ω => ?_
  simp only [π, abs_div, abs_of_pos hx]
  congr 1
  funext t
  simp [div_eq_inv_mul]

/-- **From the tail process to the spectral tail process** ([BS09, Theorem 2.1, (ii) ⇒ (iii)]):
if `(X_t)` has tail process `(Y_t)`, then `P(|X_0| > x)` is regularly varying with index `-α` and
`Θ_t = Y_t / |Y_0|` is a spectral tail process. -/
theorem HasTailProcess.hasSpectralTailProcess {Y : ℤ → Ω' → ℝ} (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hYm : ∀ t, Measurable (Y t)) (h : HasTailProcess P X α Q Y) :
    HasSpectralTailProcess P X α Q (fun t ω' => Y t ω' / |Y 0 ω'|) := by
  have hZ : Measurable fun ω => |X 0 ω| := continuous_abs.measurable.comp (hX 0)
  have hYw : ∀ S : Finset ℤ, Measurable fun ω' => (|Y 0 ω'|, fun t : S => Y t ω') := fun S =>
    (continuous_abs.measurable.comp (hYm 0)).prodMk (measurable_window hYm S)
  have hfst : ∀ S : Finset ℤ,
      (Q.map fun ω' => (|Y 0 ω'|, fun t : S => Y t ω')).map Prod.fst = paretoMeasure 1 α := by
    intro S
    rw [Measure.map_map measurable_fst
      (hYw S)]
    exact h.1
  refine ⟨isRegularlyVarying_of_tendstoLawCond hα hZ (measurable_window hX ∅) (hfst ∅)
    (h.joint hYm ∅), fun S => ?_⟩
  have key := tendstoLawCond_spectral_of_tendstoLawCond hZ (hfst S) (h.joint hYm S)
  rw [Measure.map_map (show Measurable fun p : ℝ × (S → ℝ) => p.1⁻¹ • p.2 from
    measurable_fst.inv.smul measurable_snd) (hYw S)] at key
  rw [window_div_abs]
  convert key using 2
  funext ω' t
  simp [div_eq_inv_mul]

/-- **Structure of the tail process** ([BS09, Theorem 2.1], [KS20, Chapter 5]): every finite
window of the tail process is `(R Θ_t)_{t ∈ S}`, where `R` is Pareto(`α`) and independent of the
spectral tail process `Θ_t = Y_t / |Y_0|`. -/
theorem HasTailProcess.map_window_eq {Y : ℤ → Ω' → ℝ} (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hYm : ∀ t, Measurable (Y t)) (h : HasTailProcess P X α Q Y)
    (S : Finset ℤ) :
    Q.map (fun ω' (t : S) => Y t ω') = ((paretoMeasure 1 α).prod Q).map
      (fun p (t : S) => p.1 * (Y t p.2 / |Y 0 p.2|)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hΘm : ∀ t, Measurable fun ω' => Y t ω' / |Y 0 ω'| := fun t =>
    (hYm t).div (continuous_abs.measurable.comp (hYm 0))
  exact (h.2 S).unique ((h.hasSpectralTailProcess hα hX hYm).hasTailProcess hα hX hΘm |>.2 S)

/-- **Independent coordinates do not cluster** (see [BS09, §2] and [KS20, Chapter 5]):
if `X_t` is independent of `X_0`, then `Θ_t = 0` almost surely. In particular the spectral tail
process of an iid sequence vanishes outside `t = 0`. Only the independence of the single pair
`(X_t, X_0)` is used (no identical distribution, no joint independence). -/
theorem HasSpectralTailProcess.ae_eq_zero_of_indepFun {Θ : ℤ → Ω' → ℝ}
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (h : HasSpectralTailProcess P X α Q Θ) {t : ℤ} (hind : IndepFun (X t) (X 0) P) :
    ∀ᵐ ω' ∂Q, Θ t ω' = 0 := by
  classical
  set S : Finset ℤ := {t}
  have ht : t ∈ S := Finset.mem_singleton_self t
  set s : ℝ → Set Ω := fun x => {ω | x < |X 0 ω|}
  have hZ : Measurable fun ω => |X 0 ω| := continuous_abs.measurable.comp (hX 0)
  have hs : ∀ x, MeasurableSet (s x) := fun x => measurableSet_lt measurable_const hZ
  set w : ℝ → Ω → (S → ℝ) := fun _ ω u => X u ω / |X 0 ω|
  have hw : ∀ x, Measurable (w x) := fun x => measurable_pi_iff.2 fun u => (hX u).div hZ
  have hpos : ∀ᶠ x in atTop, 0 < P.real (s x) := h.1.eventually_pos
  have hconv0 : TendstoLawCond P s w atTop (Measure.dirac 0) := by
    intro f
    have hμs : ∀ᶠ x in atTop, IsProbabilityMeasure ((P[|s x]).map (w x)) := by
      filter_upwards [hpos] with x hx
      have : P (s x) ≠ 0 := fun h0 => by simp [measureReal_def, h0] at hx
      have := cond_isProbabilityMeasure (μ := P) this
      infer_instance
    have key := tendsto_integral_of_forall_lipschitz hμs (μ := Measure.dirac (0 : S → ℝ)) ?_ f
    · refine key.congr fun x => ?_
      rw [integral_map (hw x).aemeasurable f.continuous.aestronglyMeasurable]
    intro g ⟨C, hC⟩ ⟨K, hK⟩
    have hgM : ∀ y, |g y| ≤ |g 0| + C := fun y => by
      have := hC y 0
      rw [Real.dist_eq] at this
      linarith [abs_sub_abs_le_abs_sub (g y) (g 0)]
    set M := |g 0| + C
    have hM : 0 ≤ M := (abs_nonneg _).trans (hgM 0)
    rw [integral_dirac]
    set φ : ℝ → Ω → ℝ := fun x ω => min (2 * M) (K * |X t ω| / x)
    have hXt : Measurable fun ω => |X t ω| := continuous_abs.measurable.comp (hX t)
    have hφm : ∀ x, Measurable (φ x) := fun x =>
      measurable_const.min ((measurable_const.mul hXt).div_const x)
    have hφb : ∀ x, 0 < x → ∀ ω, |φ x ω| ≤ 2 * M := fun x hx ω => by
      rw [abs_of_nonneg (le_min (by linarith) (by positivity))]
      exact min_le_left _ _
    have hφ : Tendsto (fun x => ∫ ω, φ x ω ∂P) atTop (𝓝 0) := by
      have := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := atTop)
        (fun _ => 2 * M) (Eventually.of_forall fun x => (hφm x).aestronglyMeasurable)
        ((eventually_gt_atTop 0).mono fun x hx => ae_of_all _ fun ω => by
          simpa [Real.norm_eq_abs] using hφb x hx ω)
        (integrable_const _)
        (ae_of_all _ fun ω => (show Tendsto (fun x => φ x ω) atTop
          (𝓝 (min (2 * M) 0)) from tendsto_const_nhds.min
            (tendsto_const_nhds.div_atTop tendsto_id)))
      simpa [min_eq_right (show (0 : ℝ) ≤ 2 * M by linarith)] using this
    have hcond : ∀ᶠ x in atTop, ∫ ω, φ x ω ∂P[|s x] = ∫ ω, φ x ω ∂P := by
      filter_upwards [hpos, eventually_gt_atTop 0] with x hx hx0
      rw [integral_cond_eq, smul_eq_mul, ← integral_indicator (hs x)]
      have hind' : IndepFun (φ x) ((s x).indicator fun _ => (1 : ℝ)) P := by
        have := hind.comp (φ := fun y : ℝ => min (2 * M) (K * |y| / x))
          (ψ := fun y : ℝ => (Ioi x).indicator (fun _ => (1 : ℝ)) |y|)
          (measurable_const.min ((measurable_const.mul continuous_abs.measurable).div_const x))
          ((measurable_const.indicator measurableSet_Ioi :
            Measurable ((Ioi x).indicator fun _ : ℝ => (1 : ℝ))).comp continuous_abs.measurable)
        convert this using 1 <;> funext ω <;> simp [φ, s, Set.indicator_apply]
      have heq : (s x).indicator (φ x) = fun ω => φ x ω * (s x).indicator (fun _ => (1 : ℝ)) ω := by
        funext ω; by_cases hω : ω ∈ s x <;> simp [hω]
      rw [heq, hind'.integral_fun_mul_eq_mul_integral (hφm x).aestronglyMeasurable
        ((measurable_const.indicator (hs x)).aestronglyMeasurable),
        integral_indicator_const _ (hs x), smul_eq_mul, mul_one]
      field_simp
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (hφ.congr' (hcond.mono fun x hx => hx.symm))
    filter_upwards [eventually_gt_atTop 0, hpos] with x hx0 hx
    have : P (s x) ≠ 0 := fun h0 => by simp [measureReal_def, h0] at hx
    have := cond_isProbabilityMeasure (μ := P) this
    have hgw : Integrable (fun ω => g (w x ω)) (P[|s x]) :=
      integrable_of_abs_le (hK.continuous.measurable.comp (hw x)) fun ω => hgM _
    rw [integral_map (hw x).aemeasurable hK.continuous.aestronglyMeasurable,
      Real.norm_eq_abs, show g 0 = ∫ _, g 0 ∂P[|s x] by simp,
      ← integral_sub hgw (integrable_const _)]
    refine (abs_integral_le_integral_abs).trans (integral_mono_ae (hgw.sub
      (integrable_const _)).abs (integrable_of_abs_le (hφm x) (hφb x hx0)) ?_)
    filter_upwards [ae_cond_mem (hs x)] with ω hω
    have hω' : x < |X 0 ω| := hω
    have hnorm : ‖w x ω‖ ≤ |X t ω| / x := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun u => ?_
      have hu : (u : ℤ) = t := Finset.mem_singleton.1 u.2
      simp only [w, hu, Real.norm_eq_abs, abs_div, abs_abs]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hx0 hω'.le
    refine le_min ?_ ?_
    · linarith [abs_sub (g (w x ω)) (g 0), hgM (w x ω), hgM 0]
    · have := hK.dist_le_mul (w x ω) 0
      rw [Real.dist_eq, dist_zero_right] at this
      calc _ ≤ K * ‖w x ω‖ := this
        _ ≤ K * (|X t ω| / x) := by gcongr
        _ = _ := by ring
  have heq := (h.2 S).unique hconv0
  have hae : ∀ᵐ y ∂(Q.map fun ω' (u : S) => Θ u ω'), y ⟨t, ht⟩ = 0 := by
    rw [heq, ae_dirac_iff (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)]
    rfl
  exact ae_of_ae_map (measurable_window hΘm S).aemeasurable hae

end TimeSeries

/-! ### The candidate extremal index -/

section CandidateExtremalIndex

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'} {Θ : ℤ → Ω' → ℝ} {α : ℝ}

/-- The *candidate extremal index* of a spectral tail process ([KS20, §7.5], [Planinić–Soulier,
*The tail process revisited*, Extremes 21 (2018)]):
`ϑ = E[sup_{k ≥ 0} |Θ_k|^α - sup_{k ≥ 1} |Θ_k|^α]`.
The suprema are taken in `[0, ∞]` (where `sup_k |Θ_k|^α = (sup_k |Θ_k|)^α`), with the truncated
subtraction of `ℝ≥0∞`; in particular the integrand is `0` when `sup_{k ≥ 1} |Θ_k| = ∞`. When
`sup_{k ≥ 1} |Θ_k| < ∞` almost surely (for instance when `|Θ_t| → 0`), this is the usual
real-valued expectation. -/
noncomputable def candidateExtremalIndex (Q : Measure Ω') (Θ : ℤ → Ω' → ℝ) (α : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω', (⨆ k : ℕ, ENNReal.ofReal |Θ k ω'|) ^ α - (⨆ k : ℕ, ENNReal.ofReal |Θ (k + 1) ω'|) ^ α ∂Q

/-- Splitting off the first term of a supremum over `ℕ`. -/
theorem iSup_nat_eq_sup_iSup_succ {L : Type*} [CompleteLattice L] (f : ℕ → L) :
    ⨆ k, f k = f 0 ⊔ ⨆ k, f (k + 1) := by
  refine le_antisymm (iSup_le fun k => ?_) (sup_le (le_iSup f 0) (iSup_le fun k => le_iSup f _))
  rcases k with _ | k
  · exact le_sup_left
  · exact le_sup_of_le_right (le_iSup (fun k => f (k + 1)) k)

theorem ENNReal.sup_rpow_of_nonneg {a b : ℝ≥0∞} {z : ℝ} (hz : 0 ≤ z) :
    (a ⊔ b) ^ z = a ^ z ⊔ b ^ z := by
  rcases le_total a b with h | h
  · rw [sup_eq_right.2 h, sup_eq_right.2 (ENNReal.rpow_le_rpow h hz)]
  · rw [sup_eq_left.2 h, sup_eq_left.2 (ENNReal.rpow_le_rpow h hz)]

/-- Pointwise, the integrand of `ϑ` is at most `|Θ_0|^α`. -/
theorem iSup_rpow_sub_iSup_succ_rpow_le (hα : 0 ≤ α) (ω' : Ω') :
    (⨆ k : ℕ, ENNReal.ofReal |Θ k ω'|) ^ α - (⨆ k : ℕ, ENNReal.ofReal |Θ (k + 1) ω'|) ^ α ≤
      ENNReal.ofReal |Θ 0 ω'| ^ α := by
  rw [iSup_nat_eq_sup_iSup_succ (fun k : ℕ => ENNReal.ofReal |Θ k ω'|),
    ENNReal.sup_rpow_of_nonneg hα, tsub_le_iff_right]
  exact sup_le le_self_add le_add_self

/-- `ϑ ≤ 1` for a spectral tail process, using only `|Θ_0| = 1` almost surely
([KS20, §7.5]). -/
theorem candidateExtremalIndex_le_one [IsProbabilityMeasure Q] (hα : 0 ≤ α)
    (h0 : ∀ᵐ ω' ∂Q, |Θ 0 ω'| = 1) : candidateExtremalIndex Q Θ α ≤ 1 := by
  calc candidateExtremalIndex Q Θ α ≤ ∫⁻ _, 1 ∂Q := by
        refine lintegral_mono_ae ?_
        filter_upwards [h0] with ω' hω'
        refine (iSup_rpow_sub_iSup_succ_rpow_le hα ω').trans ?_
        simp [hω']
    _ = 1 := by simp

/-- If `Θ_k = 0` almost surely for every `k ≥ 1` (as for an iid sequence, see
`HasSpectralTailProcess.ae_eq_zero_of_indepFun`), then `ϑ = 1`. Uses `α > 0` and
`|Θ_0| = 1` almost surely. -/
theorem candidateExtremalIndex_eq_one [IsProbabilityMeasure Q] (hα : 0 < α)
    (h0 : ∀ᵐ ω' ∂Q, |Θ 0 ω'| = 1) (hk : ∀ k : ℕ, ∀ᵐ ω' ∂Q, Θ (k + 1) ω' = 0) :
    candidateExtremalIndex Q Θ α = 1 := by
  have hk' : ∀ᵐ ω' ∂Q, ∀ k : ℕ, Θ (k + 1) ω' = 0 := ae_all_iff.2 hk
  calc candidateExtremalIndex Q Θ α = ∫⁻ _, 1 ∂Q := by
        refine lintegral_congr_ae ?_
        filter_upwards [h0, hk'] with ω' h0' hk''
        rw [iSup_nat_eq_sup_iSup_succ (fun k : ℕ => ENNReal.ofReal |Θ k ω'|)]
        simp [hk'', h0', ENNReal.zero_rpow_of_pos hα]
    _ = 1 := by simp

/-- The Pareto probability of `{r : r b ≤ 1}`, `b ∈ [0, ∞]`, is `1 - min(1, b^α)`. -/
theorem paretoMeasure_setOf_mul_le (hα : 0 < α) (b : ℝ≥0∞) :
    paretoMeasure 1 α {r | ENNReal.ofReal r * b ≤ 1} = (1 ⊔ b ^ α) - b ^ α := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hIoi : paretoMeasure 1 α (Ioi 1)ᶜ = 0 := by rw [compl_Ioi]; exact paretoMeasure_one_Iic_one
  rw [← measure_inter_conull hIoi]
  rcases eq_or_ne b ⊤ with rfl | hb
  · have : {r : ℝ | ENNReal.ofReal r * ⊤ ≤ 1} ∩ Ioi 1 = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun r ⟨h1, h2⟩ => ?_
      have h2 : (1 : ℝ) < r := h2
      rw [mem_setOf_eq, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by linarith)).ne'] at h1
      exact absurd h1 (by simp)
    rw [this, measure_empty, ENNReal.top_rpow_of_pos hα]
    simp
  · set β := b.toReal
    have hβ : 0 ≤ β := ENNReal.toReal_nonneg
    have hbβ : b = ENNReal.ofReal β := (ENNReal.ofReal_toReal hb).symm
    have hset : {r : ℝ | ENNReal.ofReal r * b ≤ 1} ∩ Ioi 1 = {r | r * β ≤ 1} ∩ Ioi 1 := by
      ext r
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, and_congr_left_iff]
      intro hr
      rw [hbβ, ← ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_le_one]
    rw [hset, hbβ, ENNReal.ofReal_rpow_of_nonneg hβ hα.le]
    rcases hβ.eq_or_lt with h0 | hpos
    · rw [← h0]
      have : {r : ℝ | r * 0 ≤ 1} ∩ Ioi 1 = Ioi 1 := by ext r; simp
      rw [this, paretoMeasure_one_Ioi hα le_rfl, Real.zero_rpow hα.ne']
      simp
    · rcases le_or_gt β 1 with hβ1 | hβ1
      · have hc : 1 ≤ β⁻¹ := one_le_inv₀ hpos |>.2 hβ1
        have : {r : ℝ | r * β ≤ 1} ∩ Ioi 1 = Ioi 1 \ Ioi β⁻¹ := by
          ext r
          simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_diff, not_lt]
          rw [← le_div_iff₀ hpos, one_div, and_comm]
        rw [this, measure_diff (Ioi_subset_Ioi hc) measurableSet_Ioi.nullMeasurableSet
          (measure_ne_top _ _), paretoMeasure_one_Ioi hα le_rfl, paretoMeasure_one_Ioi hα hc,
          Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv, Real.one_rpow, ENNReal.ofReal_one,
          sup_eq_left.2 (ENNReal.ofReal_le_one.2 (Real.rpow_le_one hpos.le hβ1 hα.le))]
      · have : {r : ℝ | r * β ≤ 1} ∩ Ioi 1 = ∅ := by
          ext r
          simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_empty_iff_false, iff_false,
            not_and, not_le]
          intro hr; nlinarith
        rw [this, measure_empty, sup_eq_right.2 (ENNReal.one_le_ofReal.2
          (Real.one_le_rpow hβ1.le hα.le)), tsub_self]

/-- **The candidate extremal index as a probability** ([Planinić–Soulier 2018,
Lemma 4.1], [KS20, §7.5]). Let `Y_t = R Θ_t` with `R` Pareto(`α`) independent of `(Θ_t)` (the
tail process, see `HasSpectralTailProcess.hasTailProcess`). Then
`ϑ = P(sup_{k ≥ 1} |Y_k| ≤ 1)`.
Only `α > 0`, measurability, and `|Θ_0| = 1` almost surely are used; thanks to the convention
`∞ - ∞ = 0` in the definition of `ϑ`, no condition such as `|Y_t| → 0` is needed. (Under
`|Y_t| → 0`, `sup_{k ≥ 1} |Θ_k|` is finite and `ϑ` is the usual real expectation.) -/
theorem candidateExtremalIndex_eq_measure [IsProbabilityMeasure Q] (hα : 0 < α)
    (hΘm : ∀ t, Measurable (Θ t)) (h0 : ∀ᵐ ω' ∂Q, |Θ 0 ω'| = 1) :
    candidateExtremalIndex Q Θ α =
      ((paretoMeasure 1 α).prod Q) {p | ∀ k : ℕ, p.1 * |Θ (k + 1) p.2| ≤ 1} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hmeas : MeasurableSet {p : ℝ × Ω' | ∀ k : ℕ, p.1 * |Θ (k + 1) p.2| ≤ 1} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun k => measurableSet_le
      (measurable_fst.mul (continuous_abs.measurable.comp ((hΘm _).comp measurable_snd)))
      measurable_const
  rw [Measure.prod_apply_symm hmeas, candidateExtremalIndex]
  refine lintegral_congr_ae ?_
  filter_upwards [h0] with ω' hω'
  set b := ⨆ k : ℕ, ENNReal.ofReal |Θ (k + 1) ω'|
  have hset : (fun r : ℝ => (r, ω')) ⁻¹' {p : ℝ × Ω' | ∀ k : ℕ, p.1 * |Θ (k + 1) p.2| ≤ 1} =
      {r | ENNReal.ofReal r * b ≤ 1} := by
    ext r
    simp only [mem_preimage, mem_setOf_eq, b, ENNReal.mul_iSup, iSup_le_iff]
    refine forall_congr' fun k => ?_
    rcases le_or_gt r 0 with hr | hr
    · rw [ENNReal.ofReal_of_nonpos hr, zero_mul]
      simp only [zero_le, iff_true]
      nlinarith [abs_nonneg (Θ (k + 1) ω')]
    · rw [← ENNReal.ofReal_mul hr.le, ENNReal.ofReal_le_one]
  rw [hset, paretoMeasure_setOf_mul_le hα,
    iSup_nat_eq_sup_iSup_succ (fun k : ℕ => ENNReal.ofReal |Θ k ω'|),
    ENNReal.sup_rpow_of_nonneg hα.le]
  simp [hω', b]

/-- **The iid case** ([KS20, §7.5]): if `X_t` is independent of `X_0` for every `t ≠ 0` (for
instance for an iid sequence), then every spectral tail process has candidate extremal index
`ϑ = 1`. Only pairwise independence of each `X_t` with `X_0` is used. -/
theorem HasSpectralTailProcess.candidateExtremalIndex_eq_one_of_indepFun {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ}
    [IsProbabilityMeasure Q] (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (h : HasSpectralTailProcess P X α Q Θ)
    (hind : ∀ t : ℤ, t ≠ 0 → IndepFun (X t) (X 0) P) :
    candidateExtremalIndex Q Θ α = 1 :=
  candidateExtremalIndex_eq_one hα (h.ae_abs_eq_one hΘm (hX 0)) fun k =>
    h.ae_eq_zero_of_indepFun hX hΘm (hind _ (by omega))

end CandidateExtremalIndex

end ExtremeValueTheory
