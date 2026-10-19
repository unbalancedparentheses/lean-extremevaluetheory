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
import ExtremeValueTheory.Dependence.TailProcess.Polar

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
  varying with index `α`, with spectral tail process `(Θ_t)` ([BS09, Theorem 2.1 and §3],
  [KS20, Chapter 5]).
* `ExtremeValueTheory.HasTailProcess`: the tail process `(Y_t)` ([BS09, Theorem 2.1 and §3]).
* `ExtremeValueTheory.candidateExtremalIndex`: `ϑ = E[sup_{k ≥ 0} |Θ_k|^α - sup_{k ≥ 1} |Θ_k|^α]`
  ([KS20, §5.6]).

## Main results

* `ExtremeValueTheory.tendstoLawCond_polar`: spectral convergence and regular variation imply
  convergence of `(Z / x, V / x)` to the law of `(R, R • Θ)` with `R` Pareto independent of `Θ`.
* `ExtremeValueTheory.isRegularlyVarying_of_tendstoLawCond`,
  `ExtremeValueTheory.tendstoLawCond_spectral_of_tendstoLawCond`,
  `ExtremeValueTheory.eq_map_prod_of_tendstoLawCond`: the converse, and independence of the
  radial and spectral parts; `ExtremeValueTheory.polar_iff` is the equivalence.
* `ExtremeValueTheory.HasSpectralTailProcess.hasTailProcess`,
  `ExtremeValueTheory.HasTailProcess.hasSpectralTailProcess`,
  `ExtremeValueTheory.HasTailProcess.map_window_eq`: the Basrak–Segers equivalence
  [BS09, Theorem 2.1] for windows of a time series, with `Y = R Θ`.
* `ExtremeValueTheory.HasSpectralTailProcess.ae_abs_eq_one`: `|Θ_0| = 1`.
* `ExtremeValueTheory.HasSpectralTailProcess.ae_eq_zero_of_indepFun`: `Θ_t = 0` when `X_t` is
  independent of `X_0` (the iid case).
* `ExtremeValueTheory.candidateExtremalIndex_le_one`,
  `ExtremeValueTheory.HasSpectralTailProcess.candidateExtremalIndex_eq_one_of_indepFun`,
  `ExtremeValueTheory.candidateExtremalIndex_eq_measure`,
  `ExtremeValueTheory.HasTailProcess.candidateExtremalIndex_eq`: `ϑ ≤ 1`, `ϑ = 1` in the iid
  case, and `ϑ = P(|Y_k| ≤ 1 for all k ≥ 1)`.

## File layout

This file holds the final part of the development and imports the others:

* `ExtremeValueTheory.Dependence.TailProcess.Polar`: the Pareto law, weak convergence of conditional
  laws (`TendstoLawCond`) and the single-vector polar decomposition and its converse.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Regularly varying time series -/

section TimeSeries

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q]

/-- A time series `(X_t)_{t ∈ ℤ}` is *jointly regularly varying with index `α`* and *spectral tail
process* `(Θ_t)_{t ∈ ℤ}` (defined on `(Ω', Q)`) if `P(|X_0| > x)` is regularly varying with index
`-α` and, for every finite window `S ⊆ ℤ`, the law of `(X_t / |X_0|)_{t ∈ S}` given `|X_0| > x`
converges weakly to the law of `(Θ_t)_{t ∈ S}` ([BS09, Theorem 2.1 and §3], [KS20,
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
`(Y_t)_{t ∈ S}` ([BS09, Theorem 2.1 and §3], [KS20, Chapter 5]). -/
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
    filter_upwards [ae_cond_mem (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp hX))] with ω hω
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

/-- **From the spectral tail process to the tail process** ([BS09, Theorem 2.1 and §3],
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

omit [IsProbabilityMeasure P] [IsProbabilityMeasure Q] in
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

/-- **From the tail process to the spectral tail process** ([BS09, Theorem 2.1 and §3]):
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

/-- The *candidate extremal index* of a spectral tail process ([KS20, §5.6, (5.6.5)], [Planinić–Soulier,
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
([KS20, §5.6]). -/
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
      rw [mem_ofPred_eq, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by linarith)).ne'] at h1
      exact absurd h1 (by simp)
    rw [this, measure_empty, ENNReal.top_rpow_of_pos hα]
    simp
  · set β := b.toReal
    have hβ : 0 ≤ β := ENNReal.toReal_nonneg
    have hbβ : b = ENNReal.ofReal β := (ENNReal.ofReal_toReal hb).symm
    have hset : {r : ℝ | ENNReal.ofReal r * b ≤ 1} ∩ Ioi 1 = {r | r * β ≤ 1} ∩ Ioi 1 := by
      ext r
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, and_congr_left_iff]
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
          simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, Set.mem_sdiff, not_lt]
          rw [← le_div_iff₀ hpos, one_div, and_comm]
        rw [this, measure_sdiff (Ioi_subset_Ioi hc) measurableSet_Ioi.nullMeasurableSet
          (measure_ne_top _ _), paretoMeasure_one_Ioi hα le_rfl, paretoMeasure_one_Ioi hα hc,
          Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv, Real.one_rpow, ENNReal.ofReal_one,
          sup_eq_left.2 (ENNReal.ofReal_le_one.2 (Real.rpow_le_one hpos.le hβ1 hα.le))]
      · have : {r : ℝ | r * β ≤ 1} ∩ Ioi 1 = ∅ := by
          ext r
          simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_empty_iff_false, iff_false,
            not_and]
          intro hr; nlinarith
        rw [this, measure_empty, sup_eq_right.2 (ENNReal.one_le_ofReal.2
          (Real.one_le_rpow hβ1.le hα.le)), tsub_self]

/-- **The candidate extremal index as a probability** ([Planinić–Soulier 2018,
Lemma 4.1], [KS20, §5.6]). Let `Y_t = R Θ_t` with `R` Pareto(`α`) independent of `(Θ_t)` (the
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
    simp only [ofPred_forall]
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
    simp only [mem_preimage, mem_ofPred_eq, b, ENNReal.mul_iSup, iSup_le_iff]
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

/-- **The iid case** ([KS20, §5.6]): if `X_t` is independent of `X_0` for every `t ≠ 0` (for
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

/-- **The candidate extremal index in terms of the tail process** ([Planinić–Soulier 2018,
Lemma 4.1], [KS20, §5.6]): if `(X_t)` has tail process `(Y_t)`, then the candidate extremal index
of the spectral tail process `Θ_t = Y_t / |Y_0|` is `ϑ = P(|Y_k| ≤ 1 for all k ≥ 1)`. The event
involves infinitely many coordinates; it is reached from the finite windows by continuity from
above, using the structure `Y = R Θ` of the finite-dimensional laws
(`HasTailProcess.map_window_eq`). No condition such as `|Y_t| → 0` is needed with the convention
of `candidateExtremalIndex`. -/
theorem HasTailProcess.candidateExtremalIndex_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} [IsProbabilityMeasure Q]
    {Y : ℤ → Ω' → ℝ} (hα : 0 < α) (hX : ∀ t, Measurable (X t)) (hYm : ∀ t, Measurable (Y t))
    (h : HasTailProcess P X α Q Y) :
    candidateExtremalIndex Q (fun t ω' => Y t ω' / |Y 0 ω'|) α =
      Q {ω' | ∀ k : ℕ, |Y (k + 1) ω'| ≤ 1} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set Θ : ℤ → Ω' → ℝ := fun t ω' => Y t ω' / |Y 0 ω'|
  have hΘm : ∀ t, Measurable (Θ t) := fun t =>
    (hYm t).div (continuous_abs.measurable.comp (hYm 0))
  have hspec := h.hasSpectralTailProcess hα hX hYm
  have h0 := hspec.ae_abs_eq_one hΘm (hX 0)
  set π := (paretoMeasure 1 α).prod Q
  rw [candidateExtremalIndex_eq_measure hα hΘm h0]
  have hπ1 : ∀ᵐ p ∂π, 1 < p.1 := Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure
  have heq : π {p | ∀ k : ℕ, p.1 * |Θ (k + 1) p.2| ≤ 1} =
      π {p | ∀ k : ℕ, |p.1 * Θ (k + 1) p.2| ≤ 1} := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hπ1] with p hp
    simp only [abs_mul, abs_of_pos (one_pos.trans hp)]
  rw [heq]
  -- finite windows
  set S : ℕ → Finset ℤ := fun n => Finset.Icc (1 : ℤ) n
  set B : (n : ℕ) → Set (S n → ℝ) := fun n => {y | ∀ t, |y t| ≤ 1}
  have hB : ∀ n, MeasurableSet (B n) := fun n => by
    simp only [B, ofPred_forall]
    exact MeasurableSet.iInter fun t =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply t)) measurable_const
  set a : ℕ → Set Ω' := fun n => {ω' | ∀ t ∈ S n, |Y t ω'| ≤ 1}
  set b : ℕ → Set (ℝ × Ω') := fun n => {p | ∀ t ∈ S n, |p.1 * Θ t p.2| ≤ 1}
  have hab : ∀ n, Q (a n) = π (b n) := by
    intro n
    have key := congrArg (fun m : Measure (S n → ℝ) => m (B n)) (h.map_window_eq hα hX hYm (S n))
    have hm1 : Measurable fun ω' (t : S n) => Y t ω' := measurable_pi_iff.2 fun t => hYm _
    have hm2 : Measurable fun p : ℝ × Ω' => fun t : S n => p.1 * (Y t p.2 / |Y 0 p.2|) :=
      measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
    rw [Measure.map_apply hm1 (hB n), Measure.map_apply hm2 (hB n)] at key
    convert key using 2 <;> ext <;> simp [a, b, B, Θ]
  have hfa : ∀ t : ℤ, Measurable fun ω' => |Y t ω'| := fun t =>
    continuous_abs.measurable.comp (hYm t)
  have hfb : ∀ t : ℤ, Measurable fun p : ℝ × Ω' => |p.1 * Θ t p.2| := fun t =>
    continuous_abs.measurable.comp (measurable_fst.mul ((hΘm t).comp measurable_snd))
  have hanti_a : Antitone a := fun m n hmn ω' hω' t ht =>
    hω' t (Finset.Icc_subset_Icc le_rfl (by exact_mod_cast hmn) ht)
  have hanti_b : Antitone b := fun m n hmn p hp t ht =>
    hp t (Finset.Icc_subset_Icc le_rfl (by exact_mod_cast hmn) ht)
  have hma : ∀ n, MeasurableSet (a n) := fun n => by
    simp only [a, ofPred_forall]
    exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
      measurableSet_le (hfa t) measurable_const
  have hmb : ∀ n, MeasurableSet (b n) := fun n => by
    simp only [b, ofPred_forall]
    exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
      measurableSet_le (hfb t) measurable_const
  have hla := tendsto_measure_iInter_atTop (μ := Q) (fun n => (hma n).nullMeasurableSet)
    hanti_a ⟨0, measure_ne_top _ _⟩
  have hlb := tendsto_measure_iInter_atTop (μ := π) (fun n => (hmb n).nullMeasurableSet)
    hanti_b ⟨0, measure_ne_top _ _⟩
  have hia : (⋂ n, a n) = {ω' | ∀ k : ℕ, |Y (k + 1) ω'| ≤ 1} := by
    ext ω'
    simp only [mem_ofPred_eq, mem_iInter, a, S, Finset.mem_Icc]
    constructor
    · intro hω k
      exact_mod_cast hω (k + 1) ((k : ℤ) + 1) ⟨by omega, by push_cast; omega⟩
    · intro hω n t ht
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = (k : ℤ) + 1 := ⟨(t - 1).toNat, by omega⟩
      exact_mod_cast hω k
  have hib : (⋂ n, b n) = {p | ∀ k : ℕ, |p.1 * Θ (k + 1) p.2| ≤ 1} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, b, S, Finset.mem_Icc]
    constructor
    · intro hp k
      exact_mod_cast hp (k + 1) ((k : ℤ) + 1) ⟨by omega, by push_cast; omega⟩
    · intro hp n t ht
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = (k : ℤ) + 1 := ⟨(t - 1).toNat, by omega⟩
      exact_mod_cast hp k
  rw [hia] at hla
  rw [hib] at hlb
  exact tendsto_nhds_unique hlb (hla.congr hab)

end CandidateExtremalIndex

end ExtremeValueTheory
