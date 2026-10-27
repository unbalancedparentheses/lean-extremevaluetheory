/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Asymptotic coverage of Wald confidence intervals

Let `θ̂ᵢ` estimate a real parameter `θ` with `rᵢ (θ̂ᵢ - θ) ⇒ Z` for positive rates `rᵢ`, and let
`Ŝᵢ → s` in probability be a consistent estimator of the asymptotic standard deviation. The
**Wald interval** at level `z` is `θ̂ᵢ ± z Ŝᵢ / rᵢ`. By Slutsky's theorem and the portmanteau
theorem, its coverage probability converges:

  `P(θ ∈ [θ̂ᵢ - z Ŝᵢ / rᵢ, θ̂ᵢ + z Ŝᵢ / rᵢ]) → P(|Z| ≤ z s)`,

provided `P(|Z| = z s) = 0`. For a Gaussian limit `Z ~ N(0, s²)`, `s > 0`, the limit is
`N(0, 1)([-z, z])`, which equals `1 - α` for the two-sided standard normal quantile
`z = z_{α/2}` (`exists_gaussianReal_Icc_eq`).

## Main results

* `MeasureTheory.TendstoInDistribution.tendsto_measure_abs_le_mul`: the probability of the event
  `|Yᵢ| ≤ z Ŝᵢ` converges when `Yᵢ ⇒ Z` and `Ŝᵢ → s` in probability.
* `MeasureTheory.TendstoInDistribution.tendsto_measure_mem_waldInterval`: asymptotic coverage of
  the Wald interval, for an arbitrary limit law.
* `MeasureTheory.TendstoInDistribution.tendsto_measure_mem_waldInterval_gaussian`: asymptotic
  coverage `N(0, 1)([-z, z])` for a Gaussian limit.
* `ProbabilityTheory.exists_gaussianReal_Icc_eq`: for every `α ∈ (0, 1)` there is `z > 0` with
  `N(0, 1)([-z, z]) = 1 - α`.

## References

* [A. W. van der Vaart, *Asymptotic Statistics*, §2.3, Example 3.2][vandervaart1998]
-/

public section

open Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

open MeasureTheory

/-- A centered Gaussian with positive variance gives no mass to the boundary of a symmetric
interval: `N(0, v)({y | |y| = c}) = 0`. -/
lemma gaussianReal_abs_eq {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    gaussianReal 0 v {y | |y| = c} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  refine measure_mono_null (t := {c, -c}) (fun y hy ↦ ?_) ((Set.toFinite _).measure_zero _)
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff] at hy ⊢
  rcases abs_choice y with h | h
  · left; rw [← hy, h]
  · right; rw [← hy, h, neg_neg]

/-- The scaling identity `N(0, s²)({|y| ≤ z s}) = N(0, 1)([-z, z])` for `s > 0`. -/
lemma gaussianReal_abs_le_mul {s : ℝ} (hs : 0 < s) (z : ℝ) :
    gaussianReal 0 (s ^ 2).toNNReal {y | |y| ≤ z * s} = gaussianReal 0 1 (Icc (-z) z) := by
  have hmap : (gaussianReal 0 1).map (s * ·) = gaussianReal 0 (s ^ 2).toNNReal := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [sq_nonneg]
  rw [← hmap, Measure.map_apply (measurable_const_mul s)
    (measurableSet_le continuous_abs.measurable measurable_const)]
  congr 1
  ext y
  simp only [mem_preimage, mem_ofPred_eq, mem_Icc, abs_mul, abs_of_pos hs]
  rw [mul_comm z s, mul_le_mul_iff_right₀ hs, abs_le]

/-- **Two-sided standard normal quantiles exist**: for every `α ∈ (0, 1)` there is `z > 0` with
`N(0, 1)([-z, z]) = 1 - α`. -/
lemma exists_gaussianReal_Icc_eq {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ z : ℝ, 0 < z ∧ (gaussianReal 0 1).real (Icc (-z) z) = 1 - α := by
  set f : ℝ → ℝ := fun z ↦ (gaussianReal 0 1).real (Icc (-z) z) with hf
  set g : ℝ → ℝ := fun z ↦ ∫ x in (-z)..z, gaussianPDFReal 0 1 x with hg
  -- `f z = ∫_{-z}^{z} φ` for `z ≥ 0`
  have hfg : ∀ z, 0 ≤ z → f z = g z := by
    intro z hz
    change (gaussianReal 0 1).real (Icc (-z) z) = ∫ x in (-z)..z, gaussianPDFReal 0 1 x
    rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
      ENNReal.toReal_ofReal (integral_nonneg fun x ↦ gaussianPDFReal_nonneg _ _ x),
      intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have hii : ∀ a b : ℝ, IntervalIntegrable (gaussianPDFReal 0 1) volume a b :=
    fun a b ↦ (integrable_gaussianPDFReal 0 1).intervalIntegrable
  have hgc : Continuous g := by
    have hG := intervalIntegral.continuous_primitive hii 0
    have : g = fun z ↦ (∫ x in (0 : ℝ)..z, gaussianPDFReal 0 1 x) -
        ∫ x in (0 : ℝ)..(-z), gaussianPDFReal 0 1 x := by
      ext z
      rw [hg, intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
    rw [this]
    exact hG.sub (hG.comp continuous_neg)
  -- `f n → 1`
  have hlim : Tendsto (fun n : ℕ ↦ f n) atTop (𝓝 1) := by
    have hmono : Monotone (fun n : ℕ ↦ Icc (-(n : ℝ)) n) := fun m n hmn ↦
      Icc_subset_Icc (by simpa using hmn) (by simpa using hmn)
    have hU : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
      refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact ⟨n, abs_le.1 hn⟩
    have ht := tendsto_measure_iUnion_atTop (μ := gaussianReal 0 1) hmono
    rw [hU, measure_univ] at ht
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht
    simpa [hf, Function.comp_def, measureReal_def] using this
  obtain ⟨N, hN⟩ := (hlim.eventually (lt_mem_nhds (by linarith : 1 - α < 1))).exists
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have hg0 : g 0 = 0 := by simp [hg]
  have hmem : 1 - α ∈ Icc (g 0) (g N) := ⟨by rw [hg0]; linarith, by rw [← hfg _ hN0]; exact hN.le⟩
  obtain ⟨z, hz, hgz⟩ := intermediate_value_Icc hN0 hgc.continuousOn hmem
  refine ⟨z, lt_of_le_of_ne hz.1 fun h ↦ ?_, (hfg z hz.1).trans hgz⟩
  rw [← h, hg0] at hgz
  linarith

end ProbabilityTheory

namespace MeasureTheory

variable {ι Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {l : Filter ι}

/-- **Slutsky and portmanteau for a studentized event.** If `Yᵢ ⇒ Z` and `Ŝᵢ → s` in probability,
and the limit gives no mass to `{|Z| = z s}`, then `P(|Yᵢ| ≤ z Ŝᵢ) → P(|Z| ≤ z s)`. -/
theorem TendstoInDistribution.tendsto_measure_abs_le_mul [l.IsCountablyGenerated]
    {Y S : ι → Ω → ℝ} {Z : Ω' → ℝ} {s z : ℝ}
    (hY : TendstoInDistribution Y l Z (fun _ ↦ P) P') (hS : TendstoInMeasure P S l (fun _ ↦ s))
    (hSm : ∀ i, AEMeasurable (S i) P) (hnull : P' {ω | |Z ω| = z * s} = 0) :
    Tendsto (fun i ↦ P {ω | |Y i ω| ≤ z * S i ω}) l (𝓝 (P' {ω | |Z ω| ≤ z * s})) := by
  have hYS := hY.prodMk_of_tendstoInMeasure_const Y S Z hS hSm
  set A : Set (ℝ × ℝ) := {p | |p.1| ≤ z * p.2} with hA
  have hAm : MeasurableSet A :=
    measurableSet_le (continuous_abs.comp continuous_fst).measurable
      (continuous_const.mul continuous_snd).measurable
  have hfr : frontier A ⊆ {p | |p.1| = z * p.2} := by
    intro p hp
    have hcl : IsClosed A := isClosed_le (continuous_abs.comp continuous_fst)
      (continuous_const.mul continuous_snd)
    have h1 : p ∈ A := hcl.frontier_subset hp
    have h2 : p ∉ interior A := hp.2
    have hopen : IsOpen {p : ℝ × ℝ | |p.1| < z * p.2} :=
      isOpen_lt (continuous_abs.comp continuous_fst) (continuous_const.mul continuous_snd)
    have h3 : p ∉ {p : ℝ × ℝ | |p.1| < z * p.2} := fun h ↦
      h2 (interior_maximal (s := A) (t := {p : ℝ × ℝ | |p.1| < z * p.2})
        (fun q (hq : |q.1| < z * q.2) ↦ show |q.1| ≤ z * q.2 from
        le_of_lt hq) hopen h)
    simp only [hA, mem_ofPred_eq, not_lt] at h1 h3 ⊢
    exact le_antisymm h1 h3
  have hZs : AEMeasurable (fun ω ↦ (Z ω, s)) P' := hYS.aemeasurable_limit
  have hnull' : (P'.map (fun ω ↦ (Z ω, s))) (frontier A) = 0 := by
    refine measure_mono_null hfr ?_
    have hEm : MeasurableSet {p : ℝ × ℝ | |p.1| = z * p.2} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    rw [Measure.map_apply_of_aemeasurable hZs hEm]
    exact hnull
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hYS.tendsto
    (E := A) hnull'
  simp only [ProbabilityMeasure.coe_mk] at key
  rw [Measure.map_apply_of_aemeasurable hZs hAm] at key
  refine key.congr fun i ↦ ?_
  rw [Measure.map_apply_of_aemeasurable (hYS.forall_aemeasurable i) hAm]
  rfl

/-- **Asymptotic coverage of the Wald interval.** If `rᵢ (θ̂ᵢ - θ) ⇒ Z` with `rᵢ > 0` eventually,
`Ŝᵢ → s` in probability and `P(|Z| = z s) = 0`, then the coverage probability of the interval
`θ̂ᵢ ± z Ŝᵢ / rᵢ` converges to `P(|Z| ≤ z s)`. -/
theorem TendstoInDistribution.tendsto_measure_mem_waldInterval [l.IsCountablyGenerated]
    {θh S : ι → Ω → ℝ} {θ : ℝ} {r : ι → ℝ} {Z : Ω' → ℝ} {s z : ℝ}
    (h : TendstoInDistribution (fun i ω ↦ r i * (θh i ω - θ)) l Z (fun _ ↦ P) P')
    (hr : ∀ᶠ i in l, 0 < r i) (hS : TendstoInMeasure P S l (fun _ ↦ s))
    (hSm : ∀ i, AEMeasurable (S i) P) (hnull : P' {ω | |Z ω| = z * s} = 0) :
    Tendsto (fun i ↦ P {ω | θ ∈ Icc (θh i ω - z * S i ω / r i) (θh i ω + z * S i ω / r i)}) l
      (𝓝 (P' {ω | |Z ω| ≤ z * s})) := by
  refine (h.tendsto_measure_abs_le_mul hS hSm hnull).congr' ?_
  filter_upwards [hr] with i hi
  congr 1
  ext ω
  simp only [mem_ofPred_eq, mem_Icc, abs_mul, abs_of_pos hi]
  rw [← le_div_iff₀' hi, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Asymptotic coverage of the Wald interval, Gaussian limit.** If
`rᵢ (θ̂ᵢ - θ) ⇒ N(0, s²)` with `s > 0`, `rᵢ > 0` eventually, and `Ŝᵢ → s` in probability, then
`P(θ ∈ θ̂ᵢ ± z Ŝᵢ / rᵢ) → N(0, 1)([-z, z])`; with `z` the two-sided standard normal quantile
(`exists_gaussianReal_Icc_eq`) the limit is `1 - α`. -/
theorem TendstoInDistribution.tendsto_measure_mem_waldInterval_gaussian [l.IsCountablyGenerated]
    {θh S : ι → Ω → ℝ} {θ : ℝ} {r : ι → ℝ} {Z : Ω' → ℝ} {s : ℝ} (hs : 0 < s) (z : ℝ)
    (h : TendstoInDistribution (fun i ω ↦ r i * (θh i ω - θ)) l Z (fun _ ↦ P) P')
    (hZ : HasLaw Z (gaussianReal 0 (s ^ 2).toNNReal) P')
    (hr : ∀ᶠ i in l, 0 < r i) (hS : TendstoInMeasure P S l (fun _ ↦ s))
    (hSm : ∀ i, AEMeasurable (S i) P) :
    Tendsto (fun i ↦ P {ω | θ ∈ Icc (θh i ω - z * S i ω / r i) (θh i ω + z * S i ω / r i)}) l
      (𝓝 (gaussianReal 0 1 (Icc (-z) z))) := by
  have hv : (s ^ 2).toNNReal ≠ 0 := by simp [hs.ne']
  have hpre : ∀ t : Set ℝ, MeasurableSet t → P' (Z ⁻¹' t) = gaussianReal 0 (s ^ 2).toNNReal t :=
    fun t ht ↦ by rw [← hZ.map_eq, Measure.map_apply_of_aemeasurable hZ.aemeasurable ht]
  have hnull : P' {ω | |Z ω| = z * s} = 0 := by
    rw [show {ω | |Z ω| = z * s} = Z ⁻¹' {y | |y| = z * s} from rfl,
      hpre _ (measurableSet_eq_fun continuous_abs.measurable measurable_const)]
    exact gaussianReal_abs_eq hv _
  have hlim : P' {ω | |Z ω| ≤ z * s} = gaussianReal 0 1 (Icc (-z) z) := by
    rw [show {ω | |Z ω| ≤ z * s} = Z ⁻¹' {y | |y| ≤ z * s} from rfl,
      hpre _ (measurableSet_le continuous_abs.measurable measurable_const)]
    exact gaussianReal_abs_le_mul hs z
  rw [← hlim]
  exact h.tendsto_measure_mem_waldInterval hr hS hSm hnull

end MeasureTheory
