/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Topology.UrysohnsLemma

/-!
# Vague convergence of measures

Let `X` be a locally compact topological space. A family of measures `μs i` converges *vaguely*
to a measure `μ` along a filter `l` if `∫ f ∂μs i → ∫ f ∂μ` for every continuous compactly
supported function `f : X → ℝ`. This is the natural mode of convergence for locally finite
(Radon) measures which are not finite, e.g. intensity measures of point processes.

## Main definitions

* `MeasureTheory.Measure.TendstoVaguely μs l μ`: the measures `μs i` converge vaguely to `μ`
  along the filter `l`.

## Main statements

* `MeasureTheory.Measure.ext_of_forall_integral_eq_of_hasCompactSupport`: two regular measures
  which have the same integrals against all continuous compactly supported functions are equal.
* `MeasureTheory.Measure.TendstoVaguely.unique`: vague limits of regular measures are unique.
* `MeasureTheory.Measure.TendstoVaguely.limsup_measure_le_of_isCompact`: if `μs i → μ` vaguely,
  then `limsup μs i K ≤ μ K` for every compact set `K`.
* `MeasureTheory.Measure.TendstoVaguely.le_liminf_measure_of_isOpen`: if `μs i → μ` vaguely,
  then `μ U ≤ liminf μs i U` for every open set `U`.
* `MeasureTheory.Measure.TendstoVaguely.tendsto_measure_of_null_frontier`: if `μs i → μ`
  vaguely, then `μs i B → μ B` for every relatively compact set `B` with `μ (frontier B) = 0`.
* `MeasureTheory.FiniteMeasure.tendstoVaguely_of_tendsto`: weak convergence of finite measures
  implies vague convergence.

## Implementation notes

We define vague convergence as a predicate rather than through a topology on `Measure X`.
-/

open Filter Set Topology ENNReal

namespace MeasureTheory

namespace Measure

variable {X : Type*} [MeasurableSpace X]

/-- The measures `μs i` converge *vaguely* to `μ` along the filter `l` if
`∫ x, f x ∂μs i` tends to `∫ x, f x ∂μ` for every continuous compactly supported
function `f : X → ℝ`. -/
def TendstoVaguely [TopologicalSpace X] {ι : Type*} (μs : ι → Measure X) (l : Filter ι)
    (μ : Measure X) : Prop :=
  ∀ f : X → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun i ↦ ∫ x, f x ∂μs i) l (𝓝 (∫ x, f x ∂μ))

section Auxiliary

variable {μ : Measure X}

/-- If `f` is integrable, nonnegative, and at least `1` on a measurable set `K`, then
`μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ)`. -/
lemma measure_le_ofReal_integral {f : X → ℝ} {K : Set X} (hK : MeasurableSet K)
    (hf : Integrable f μ) (hf0 : 0 ≤ f) (hfK : ∀ x ∈ K, 1 ≤ f x) :
    μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0),
    ← lintegral_indicator_one hK]
  refine lintegral_mono fun x ↦ ?_
  by_cases hx : x ∈ K
  · simpa [hx] using hfK x hx
  · simp [hx]

/-- If `f` is integrable, nonnegative, at most `1`, and vanishes outside a measurable set `U`,
then `ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ U`. -/
lemma ofReal_integral_le_measure {f : X → ℝ} {U : Set X} (hU : MeasurableSet U)
    (hf : Integrable f μ) (hf0 : 0 ≤ f) (hf1 : ∀ x, f x ≤ 1) (hfU : ∀ x ∉ U, f x = 0) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ U := by
  rw [ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0),
    ← lintegral_indicator_one hU]
  refine lintegral_mono fun x ↦ ?_
  by_cases hx : x ∈ U
  · simpa [hx] using hf1 x
  · simp [hx, hfU x hx]

end Auxiliary

omit [MeasurableSpace X] in
/-- Urysohn-type function: for a compact set `K` contained in an open set `U`, there is a
continuous compactly supported function with values in `[0, 1]`, equal to `1` on `K` and
vanishing outside `U`. -/
lemma exists_continuous_hasCompactSupport_one_on_zero_off [TopologicalSpace X]
    [LocallyCompactSpace X] [RegularSpace X] {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : X → ℝ, Continuous f ∧ HasCompactSupport f ∧ 0 ≤ f ∧ (∀ x, f x ≤ 1) ∧
      (∀ x ∈ K, f x = 1) ∧ ∀ x ∉ U, f x = 0 := by
  obtain ⟨f, hfK, hfU, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.2 hKU)
  exact ⟨f, f.continuous, hfc, fun x ↦ (hf01 x).1, fun x ↦ (hf01 x).2, fun x hx ↦ hfK hx,
    fun x hx ↦ hfU hx⟩

variable [TopologicalSpace X] [LocallyCompactSpace X] [RegularSpace X] [OpensMeasurableSpace X]

/-- If two measures have the same integrals against a continuous compactly supported function
`f`, which is `≥ 1` on a compact set `K` and vanishes outside an open set `U`, then
`μ K ≤ ν U`. -/
lemma measure_isCompact_le_of_forall_integral_eq [T2Space X] {μ ν : Measure X}
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x ∂μ = ∫ x, f x ∂ν)
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) : μ K ≤ ν U := by
  obtain ⟨f, hfc, hfs, hf0, hf1, hfK, hfU⟩ :=
    exists_continuous_hasCompactSupport_one_on_zero_off hK hU hKU
  calc μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ) :=
        measure_le_ofReal_integral hK.measurableSet (hfc.integrable_of_hasCompactSupport hfs) hf0
          fun x hx ↦ (hfK x hx).ge
    _ = ENNReal.ofReal (∫ x, f x ∂ν) := by rw [h f hfc hfs]
    _ ≤ ν U := ofReal_integral_le_measure hU.measurableSet
          (hfc.integrable_of_hasCompactSupport hfs) hf0 hf1 hfU

/-- Two regular measures on a locally compact Hausdorff space which have the same integrals
against all continuous compactly supported real functions are equal. -/
theorem ext_of_forall_integral_eq_of_hasCompactSupport [T2Space X] [BorelSpace X]
    {μ ν : Measure X} [μ.Regular] [ν.Regular]
    (h : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  -- First, the two measures agree on compact sets.
  have hcomp : ∀ ⦃μ ν : Measure X⦄ [μ.Regular] [ν.Regular],
      (∀ f : X → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x ∂μ = ∫ x, f x ∂ν) →
      ∀ K, IsCompact K → μ K ≤ ν K := by
    intro μ ν _ _ h K hK
    refine le_of_forall_gt fun r hr ↦ ?_
    obtain ⟨U, hKU, hU, hUr⟩ := Set.exists_isOpen_lt_of_lt K r hr
    exact (measure_isCompact_le_of_forall_integral_eq h hK hU hKU).trans_lt hUr
  have hK : ∀ K, IsCompact K → μ K = ν K := fun K hK ↦
    le_antisymm (hcomp h K hK) (hcomp (fun f hf hfs ↦ (h f hf hfs).symm) K hK)
  -- Hence on open sets, by inner regularity.
  have hO : ∀ U, IsOpen U → μ U = ν U := by
    intro U hU
    rw [hU.measure_eq_iSup_isCompact μ, hU.measure_eq_iSup_isCompact ν]
    exact iSup_congr fun K ↦ iSup_congr fun _ ↦ iSup_congr fun hK' ↦ hK K hK'
  -- Hence everywhere, by outer regularity.
  ext s hs
  rw [Set.measure_eq_iInf_isOpen s μ, Set.measure_eq_iInf_isOpen s ν]
  exact iInf_congr fun U ↦ iInf_congr fun _ ↦ iInf_congr fun hU ↦ hO U hU

namespace TendstoVaguely

variable {ι : Type*} {μs : ι → Measure X} {l : Filter ι} {μ : Measure X}

/-- Vague limits of regular measures are unique. -/
theorem unique [T2Space X] [BorelSpace X] [l.NeBot] {ν : Measure X} [μ.Regular] [ν.Regular]
    (hμ : TendstoVaguely μs l μ) (hν : TendstoVaguely μs l ν) : μ = ν :=
  ext_of_forall_integral_eq_of_hasCompactSupport fun f hf hfs ↦
    tendsto_nhds_unique (hμ f hf hfs) (hν f hf hfs)

/-- Portmanteau-type inequality for vague convergence: if `μs i → μ` vaguely, then
`limsup μs i K ≤ μ K` for every compact set `K`. -/
theorem limsup_measure_le_of_isCompact [T2Space X] [∀ i, IsFiniteMeasureOnCompacts (μs i)]
    [IsFiniteMeasureOnCompacts μ] [μ.OuterRegular] (h : TendstoVaguely μs l μ) {K : Set X}
    (hK : IsCompact K) : limsup (fun i ↦ μs i K) l ≤ μ K := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
  obtain ⟨U, hKU, hU, hUr⟩ := Set.exists_isOpen_lt_of_lt K r hr
  obtain ⟨f, hfc, hfs, hf0, hf1, hfK, hfU⟩ :=
    exists_continuous_hasCompactSupport_one_on_zero_off hK hU hKU
  have hlim : Tendsto (fun i ↦ ENNReal.ofReal (∫ x, f x ∂μs i)) l
      (𝓝 (ENNReal.ofReal (∫ x, f x ∂μ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (h f hfc hfs)
  have hfμ : ENNReal.ofReal (∫ x, f x ∂μ) < r :=
    (ofReal_integral_le_measure hU.measurableSet (hfc.integrable_of_hasCompactSupport hfs) hf0
      hf1 hfU).trans_lt hUr
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hlim.eventually (gt_mem_nhds hfμ)] with i hi
  exact ((measure_le_ofReal_integral hK.measurableSet (hfc.integrable_of_hasCompactSupport hfs)
    hf0 fun x hx ↦ (hfK x hx).ge).trans hi.le)

/-- Portmanteau-type inequality for vague convergence: if `μs i → μ` vaguely, then
`μ U ≤ liminf μs i U` for every open set `U`. -/
theorem le_liminf_measure_of_isOpen [T2Space X] [∀ i, IsFiniteMeasureOnCompacts (μs i)]
    [μ.Regular] (h : TendstoVaguely μs l μ) {U : Set X} (hU : IsOpen U) :
    μ U ≤ liminf (fun i ↦ μs i U) l := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
  obtain ⟨f, hfc, hfs, hf0, hf1, hfK, hfU⟩ :=
    exists_continuous_hasCompactSupport_one_on_zero_off hK hU hKU
  have hlim : Tendsto (fun i ↦ ENNReal.ofReal (∫ x, f x ∂μs i)) l
      (𝓝 (ENNReal.ofReal (∫ x, f x ∂μ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (h f hfc hfs)
  have hfμ : r < ENNReal.ofReal (∫ x, f x ∂μ) :=
    hrK.trans_le (measure_le_ofReal_integral hK.measurableSet
      (hfc.integrable_of_hasCompactSupport hfs) hf0 fun x hx ↦ (hfK x hx).ge)
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hlim.eventually (lt_mem_nhds hfμ)] with i hi
  exact hi.le.trans (ofReal_integral_le_measure hU.measurableSet
    (hfc.integrable_of_hasCompactSupport hfs) hf0 hf1 hfU)

/-- If `μs i → μ` vaguely, then `μs i B → μ B` for every relatively compact set `B` whose
frontier is `μ`-null. -/
theorem tendsto_measure_of_null_frontier [T2Space X] [∀ i, IsFiniteMeasureOnCompacts (μs i)]
    [μ.Regular] (h : TendstoVaguely μs l μ) {B : Set X} (hB : IsCompact (closure B))
    (hBμ : μ (frontier B) = 0) : Tendsto (fun i ↦ μs i B) l (𝓝 (μ B)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · calc μ B = μ (interior B) := (measure_interior_of_null_frontier hBμ).symm
      _ ≤ liminf (fun i ↦ μs i (interior B)) l := h.le_liminf_measure_of_isOpen isOpen_interior
      _ ≤ liminf (fun i ↦ μs i B) l :=
        liminf_le_liminf (Eventually.of_forall fun i ↦ measure_mono interior_subset)
  · calc limsup (fun i ↦ μs i B) l ≤ limsup (fun i ↦ μs i (closure B)) l :=
        limsup_le_limsup (Eventually.of_forall fun i ↦ measure_mono subset_closure)
      _ ≤ μ (closure B) := h.limsup_measure_le_of_isCompact hB
      _ = μ B := measure_closure_of_null_frontier hBμ

end TendstoVaguely

end Measure

namespace FiniteMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Weak convergence of finite measures implies vague convergence. -/
theorem tendstoVaguely_of_tendsto {ι : Type*} {μs : ι → FiniteMeasure X} {l : Filter ι}
    {μ : FiniteMeasure X} (h : Tendsto μs l (𝓝 μ)) :
    Measure.TendstoVaguely (fun i ↦ (μs i : Measure X)) l μ := by
  intro f hf hfs
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  exact tendsto_iff_forall_integral_tendsto.1 h
    (BoundedContinuousFunction.ofNormedAddCommGroup f hf C hC)

end FiniteMeasure

namespace ProbabilityMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Weak convergence of probability measures implies vague convergence. -/
theorem tendstoVaguely_of_tendsto {ι : Type*} {μs : ι → ProbabilityMeasure X} {l : Filter ι}
    {μ : ProbabilityMeasure X} (h : Tendsto μs l (𝓝 μ)) :
    Measure.TendstoVaguely (fun i ↦ (μs i : Measure X)) l μ :=
  FiniteMeasure.tendstoVaguely_of_tendsto
    ((toFiniteMeasure_isEmbedding X).tendsto_nhds_iff.1 h)

end ProbabilityMeasure

end MeasureTheory
