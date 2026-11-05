/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.Examples
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The expected payout of a reinsurance layer

A layer `l xs d` pays the part of a loss `x` above the retention `d`, up to the limit `l`:
`min (max (x - d) 0) l`. Its expected payout is the integral of the tail over `[d, d + l]`. The
payout is bounded, so this needs no moment assumption on the loss.

## Main definitions

* `ExtremeValueTheory.layerPayout d l x`: the payout of the layer `l xs d` on a loss `x`.

## Main results

* `integral_layerPayout`: `E[layerPayout d l X] = ∫_d^{d+l} P(X > t) dt`, for every finite measure.
* `integral_layerPayout_paretoMeasure`: its closed form for a Pareto loss.

## References

* T. Mikosch, *Non-Life Insurance Mathematics*, Springer (2009), §3.4.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-- The payout of the reinsurance layer with retention `d` and limit `l` on a loss `x`. -/
noncomputable def layerPayout (d l x : ℝ) : ℝ := min (max (x - d) 0) l

lemma layerPayout_nonneg {d l : ℝ} (hl : 0 ≤ l) (x : ℝ) : 0 ≤ layerPayout d l x :=
  le_min (le_max_right _ _) hl

lemma layerPayout_le {d l : ℝ} (x : ℝ) : layerPayout d l x ≤ l := min_le_right _ _

lemma measurable_layerPayout (d l : ℝ) : Measurable (layerPayout d l) := by
  unfold layerPayout
  fun_prop

/-- **The expected payout of a layer is the integral of the tail over the layer**:
`E[min ((X - d)⁺, l)] = ∫_d^{d+l} P(X > t) dt`. -/
theorem integral_layerPayout (μ : Measure ℝ) [IsFiniteMeasure μ] (d : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    ∫ x, layerPayout d l x ∂μ = ∫ t in d..(d + l), μ.real (Ioi t) := by
  have hint : Integrable (layerPayout d l) μ := by
    refine Integrable.of_bound (measurable_layerPayout d l).aestronglyMeasurable l
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (layerPayout_nonneg hl x)]
    exact layerPayout_le x
  rw [hint.integral_eq_integral_meas_lt (Eventually.of_forall (layerPayout_nonneg hl))]
  have hG : ∀ t ∈ Ioi (0 : ℝ), μ.real {a | t < layerPayout d l a} =
      (Ioo 0 l).indicator (fun s => μ.real (Ioi (d + s))) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    by_cases htl : t < l
    · rw [indicator_of_mem (show t ∈ Ioo 0 l from ⟨ht0, htl⟩)]
      congr 1
      ext a
      simp only [layerPayout, mem_ofPred_eq, mem_Ioi, lt_min_iff, lt_max_iff]
      constructor
      · rintro ⟨h | h, -⟩
        · linarith
        · linarith
      · intro h
        exact ⟨Or.inl (by linarith), htl⟩
    · rw [indicator_of_notMem (fun h : t ∈ Ioo 0 l => htl h.2)]
      have : {a | t < layerPayout d l a} = ∅ := by
        ext a
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (layerPayout_le a).trans (not_lt.1 htl)
      rw [this, measureReal_empty]
  rw [setIntegral_congr_fun measurableSet_Ioi hG, setIntegral_indicator measurableSet_Ioo,
    show Ioi (0 : ℝ) ∩ Ioo 0 l = Ioo 0 l from inter_eq_right.2 fun t ht => ht.1,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hl,
    intervalIntegral.integral_comp_add_left (fun t => μ.real (Ioi t)) d, add_zero]

/-- **The expected payout of a layer on a Pareto loss**: for `X ∼ Pareto(t, r)`, `r ≠ 1`, and a
retention `d ≥ t`, `E[min ((X - d)⁺, l)] = t^r ((d + l)^{1-r} - d^{1-r}) / (1 - r)`. -/
theorem integral_layerPayout_paretoMeasure {t r d l : ℝ} (ht : 0 < t) (hr : 0 < r) (hr1 : r ≠ 1)
    (hd : t ≤ d) (hl : 0 ≤ l) :
    ∫ x, layerPayout d l x ∂paretoMeasure t r =
      t ^ r * (((d + l) ^ (1 - r) - d ^ (1 - r)) / (1 - r)) := by
  have := isProbabilityMeasure_paretoMeasure ht hr
  have hd0 : 0 < d := ht.trans_le hd
  have hle : d ≤ d + l := by linarith
  rw [integral_layerPayout _ d hl]
  have hcongr : ∀ x ∈ uIcc d (d + l), (paretoMeasure t r).real (Ioi x) = t ^ r * x ^ (-r) := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    have := tail_paretoMeasure ht hr (hd.trans hx.1)
    rw [tail] at this
    exact this
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by
      intro h
      exact hr1 (by linarith), by
      rw [uIcc_of_le hle]
      exact fun h => absurd h.1 (not_le.2 hd0)⟩),
    show -r + 1 = 1 - r by ring]

end ExtremeValueTheory
