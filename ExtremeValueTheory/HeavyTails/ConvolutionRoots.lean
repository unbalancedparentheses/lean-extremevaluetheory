/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.RandomSums

/-!
# Closure of the subexponential class under convolution roots

If `μ` is a probability measure on `[0, ∞)` and some convolution power `μ^{*n}`, `n ≥ 1`, is
subexponential, then `μ` itself is subexponential, and `F̄^{*n}(x) ~ n F̄(x)`
(Embrechts, Goldie and Veraverbeke, *Subexponentiality and infinite divisibility*,
Z. Wahrsch. Verw. Gebiete 49 (1979), 335–347 [EGV]; see also [EKM, Appendix A3] and
Foss, Korshunov and Zachary, *An Introduction to Heavy-Tailed and Subexponential
Distributions* (2nd ed., Springer, 2013) [FKZ], Chapter 3).

## Main results

* `IsSubexponential.tendsto_tail_div_tail_convPow`: if `μ^{*n} ∈ 𝒮`, then
  `F̄(x) / F̄^{*n}(x) → 1 / n`.
* `IsSubexponential.of_convPow`: if `μ^{*n} ∈ 𝒮` for some `n ≥ 1`, then `μ ∈ 𝒮`.

## Proof outline

Write `G = μ^{*n} = μ ∗ H` with `H = μ^{*(n-1)}`, fix `h ≥ 0` with `d = H[0, h] > 1/2`, and let
`P = μ|_{(-∞, x - h]}` (so `P^{*n}(x, ∞)` is the probability that `X₁ + ⋯ + Xₙ > x` while every
`Xᵢ ≤ x - h`). Then

* `Ḡ(x) ≤ P^{*n}(x, ∞) + n F̄(x - h)` (union bound, by induction on `n`);
* `Q = P ∗ H|_{[0, h]}` is a sub-measure of `G` living on `[0, x]`, hence
  `d^n P^{*n}(x, ∞) ≤ Q^{*n}(x, ∞) ≤ (G|_{[0,x]})^{*n}(x, ∞) ≤ G(x)^n - G^{*n}[0, x]`,
  which is `Ḡ^{*n}(x) - n Ḡ(x) + O(Ḡ(x)²) = o(Ḡ(x))` since `G ∈ 𝒮` (this is the regrouping of
  `n²` independent copies into `n` blocks distributed as `G`);
* `d (F̄(x - h) - F̄(x)) ≤ Ḡ(x - h) - Ḡ(x + h) = o(Ḡ(x))` since `G` is long-tailed;
* `Ḡ(x) ≥ 1 - F(x)^n ≥ n F̄(x) - n² F̄(x)²`.

Hence `n F̄(x) / Ḡ(x) → 1`, and `μ ∈ 𝒮` because `𝒮` is closed under tail equivalence
(`IsSubexponential.of_tendsto_tail_div`).
-/

open Filter Topology Set Real MeasureTheory
open scoped ENNReal NNReal

namespace ExtremeValueTheory

namespace Subexp

variable {μ ν : Measure ℝ}

instance isFiniteMeasure_convPow (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ) :
    IsFiniteMeasure (convPow μ n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; infer_instance

theorem conv_univ [SFinite μ] [SFinite ν] : (μ ∗ ν) univ = μ univ * ν univ := by
  rw [Measure.conv, Measure.map_apply measurable_add MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, Measure.prod_prod]

theorem convPow_univ [IsFiniteMeasure μ] (n : ℕ) : convPow μ n univ = μ univ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [convPow_succ, conv_univ, ih, pow_succ, mul_comm]

theorem convPow_Iio_zero' [IsFiniteMeasure μ] (h0 : μ (Iio 0) = 0) (n : ℕ) :
    convPow μ n (Iio 0) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [convPow_succ]; exact conv_Iio_zero h0 ih

/-- Convolution is monotone in both arguments. -/
theorem conv_mono {μ₁ μ₂ ν₁ ν₂ : Measure ℝ} [SFinite ν₁] [SFinite ν₂] (hμ : μ₁ ≤ μ₂)
    (hν : ν₁ ≤ ν₂) : μ₁ ∗ ν₁ ≤ μ₂ ∗ ν₂ := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [conv_apply hs, conv_apply hs]
  exact (lintegral_mono fun a => Measure.le_iff'.1 hν _).trans (lintegral_mono' hμ le_rfl)

theorem convPow_mono {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : μ₁ ≤ μ₂) (n : ℕ) : convPow μ₁ n ≤ convPow μ₂ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [convPow_succ, convPow_succ]; exact conv_mono h ih

/-- `(μ ∗ ν)^{*n} = μ^{*n} ∗ ν^{*n}`. -/
theorem convPow_conv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ) :
    convPow (μ ∗ ν) n = convPow μ n ∗ convPow ν n := by
  induction n with
  | zero => simp only [convPow_zero, Measure.conv_dirac_zero]
  | succ n ih =>
    rw [convPow_succ, convPow_succ, convPow_succ, ih, Measure.conv_assoc,
      ← Measure.conv_assoc ν, Measure.conv_comm ν (convPow μ n),
      Measure.conv_assoc (convPow μ n) ν, ← Measure.conv_assoc μ (convPow μ n)]

/-- Adding a nonnegative independent summand can only increase tails:
`μ(x, ∞) ν(ℝ) ≤ (μ ∗ ν)(x, ∞)` for `ν` on `[0, ∞)`. -/
theorem conv_Ioi_ge [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) (x : ℝ) :
    μ (Ioi x) * ν univ ≤ (μ ∗ ν) (Ioi x) := by
  rw [Measure.conv_comm, conv_apply measurableSet_Ioi, ← lintegral_const]
  have hae : ∀ᵐ b ∂ν, 0 ≤ b := by
    rw [ae_iff]; simp only [not_le]; exact hν
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with b hb
  exact measure_mono fun y hy => by
    simp only [mem_preimage, mem_Ioi] at hy ⊢; linarith

/-- For laws on `[0, ∞)` and `s ⊆ (-∞, x]`, only the parts on `(-∞, x]` contribute to
`(μ ∗ ν)(s)`. -/
theorem conv_le_conv_restrict [SFinite ν] (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0) {x : ℝ}
    {s : Set ℝ} (hs : MeasurableSet s) (hsx : s ⊆ Iic x) :
    (μ ∗ ν) s ≤ (μ.restrict (Iic x) ∗ ν.restrict (Iic x)) s := by
  rw [conv_apply hs, conv_apply hs, ← lintegral_indicator measurableSet_Iic]
  have hae : ∀ᵐ a ∂μ, 0 ≤ a := by
    rw [ae_iff]; simp only [not_le]; exact hμ
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with a ha
  have hpre : MeasurableSet ((fun b => a + b) ⁻¹' s) := hs.preimage (measurable_const_add a)
  by_cases hax : a ≤ x
  · rw [indicator_of_mem (show a ∈ Iic x from hax), Measure.restrict_apply hpre]
    refine measure_mono fun b hb => ⟨hb, ?_⟩
    have := hsx hb
    simp only [mem_Iic] at this ⊢; linarith
  · rw [indicator_of_notMem (show a ∉ Iic x from hax)]
    refine (measure_mono_null (fun b hb => ?_) hν).le
    have := hsx hb
    simp only [mem_Iic, mem_Iio, not_le] at this hax ⊢; linarith

theorem convPow_le_convPow_restrict [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0) {x : ℝ}
    (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s) (hsx : s ⊆ Iic x) :
    convPow μ n s ≤ convPow (μ.restrict (Iic x)) n s := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    rw [convPow_succ, convPow_succ]
    refine (conv_le_conv_restrict hμ (convPow_Iio_zero hμ n) hs hsx).trans ?_
    refine Measure.le_iff'.1 (conv_mono le_rfl ?_) s
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.restrict_apply ht]
    exact (ih (ht.inter measurableSet_Iic) inter_subset_right).trans
      (measure_mono inter_subset_left)

/-- Union bound: `μ^{*n}(s) ≤ (μ|_{(-∞, a]})^{*n}(s) + n μ(a, ∞)`. -/
theorem convPow_le_add [IsProbabilityMeasure μ] (a : ℝ) (n : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    convPow μ n s ≤ convPow (μ.restrict (Iic a)) n s + n * μ (Ioi a) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    have hsplit : μ = μ.restrict (Iic a) + μ.restrict (Ioi a) := by
      rw [← compl_Iic, Measure.restrict_add_restrict_compl measurableSet_Iic]
    rw [convPow_succ, convPow_succ, show μ ∗ convPow μ n =
      (μ.restrict (Iic a) + μ.restrict (Ioi a)) ∗ convPow μ n from
        congrArg (· ∗ convPow μ n) hsplit, Measure.add_conv, Measure.add_apply]
    have h1 : (μ.restrict (Iic a) ∗ convPow μ n) s ≤
        (μ.restrict (Iic a) ∗ convPow (μ.restrict (Iic a)) n) s + n * μ (Ioi a) := by
      rw [conv_apply hs, conv_apply hs]
      calc ∫⁻ y, convPow μ n ((fun b => y + b) ⁻¹' s) ∂μ.restrict (Iic a)
          ≤ ∫⁻ y, (convPow (μ.restrict (Iic a)) n ((fun b => y + b) ⁻¹' s) + n * μ (Ioi a))
              ∂μ.restrict (Iic a) :=
            lintegral_mono fun y => ih (hs.preimage (measurable_const_add y))
        _ = ∫⁻ y, convPow (μ.restrict (Iic a)) n ((fun b => y + b) ⁻¹' s) ∂μ.restrict (Iic a)
              + n * μ (Ioi a) * μ.restrict (Iic a) univ := by
            rw [lintegral_add_right _ measurable_const, lintegral_const]
        _ ≤ _ := by
            refine add_le_add le_rfl ?_
            calc n * μ (Ioi a) * μ.restrict (Iic a) univ ≤ n * μ (Ioi a) * 1 := by
                  gcongr; rw [Measure.restrict_apply_univ]; exact prob_le_one
              _ = _ := mul_one _
    have h2 : (μ.restrict (Ioi a) ∗ convPow μ n) s ≤ μ (Ioi a) :=
      calc _ ≤ (μ.restrict (Ioi a) ∗ convPow μ n) univ := measure_mono (subset_univ _)
        _ = μ (Ioi a) := by rw [conv_univ, measure_univ (μ := convPow μ n), mul_one,
          Measure.restrict_apply_univ]
    calc _ ≤ ((μ.restrict (Iic a) ∗ convPow (μ.restrict (Iic a)) n) s + n * μ (Ioi a))
          + μ (Ioi a) := add_le_add h1 h2
      _ = _ := by push_cast; ring

/-- `μ^{*n}[0, x] ≤ μ[0, x]^n` for laws on `[0, ∞)`. -/
theorem convPow_Iic_le [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0) (x : ℝ) (n : ℕ) :
    convPow μ n (Iic x) ≤ μ (Iic x) ^ n := by
  induction n with
  | zero => rw [convPow_zero, pow_zero]; exact prob_le_one
  | succ n ih =>
    rw [convPow_succ, conv_apply measurableSet_Iic, pow_succ]
    have hae : ∀ᵐ a ∂μ, 0 ≤ a := by
      rw [ae_iff]; simp only [not_le]; exact hμ
    calc ∫⁻ a, convPow μ n ((fun b => a + b) ⁻¹' Iic x) ∂μ
        ≤ ∫⁻ a, (Iic x).indicator (fun _ => convPow μ n (Iic x)) a ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with a ha
          by_cases hax : a ≤ x
          · rw [indicator_of_mem (show a ∈ Iic x from hax)]
            exact measure_mono fun b hb => by
              simp only [mem_preimage, mem_Iic] at hb ⊢; linarith
          · rw [indicator_of_notMem (show a ∉ Iic x from hax)]
            refine (measure_mono_null (fun b hb => ?_) (convPow_Iio_zero hμ n)).le
            simp only [mem_preimage, mem_Iic, mem_Iio, not_le] at hb hax ⊢; linarith
      _ = convPow μ n (Iic x) * μ (Iic x) := lintegral_indicator_const measurableSet_Iic _
      _ ≤ μ (Iic x) ^ n * μ (Iic x) := by gcongr

/-- `d (F̄(x - h) - F̄(x)) ≤ F̄_{μ∗ν}(x - h) - F̄_{μ∗ν}(x + h)` with `d = 1 - F̄_ν(h)`. -/
theorem tail_sub_le_of_conv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {h x : ℝ} (hh : 0 ≤ h) :
    (1 - tail ν h) * (tail μ (x - h) - tail μ x) ≤ tail (μ ∗ ν) (x - h) - tail (μ ∗ ν) (x + h) := by
  have hi := (integrable_tail_sub (μ := μ) (ν := ν) (x - h)).sub
    (integrable_tail_sub (μ := μ) (ν := ν) (x + h))
  rw [tail_conv, tail_conv, ← integral_sub (integrable_tail_sub _) (integrable_tail_sub _),
    ← measureReal_Ioc_eq (by linarith)]
  have key : ∫ _ in Ioc (x - h) x, (1 - tail ν h) ∂μ ≤
      ∫ a, (tail ν (x - h - a) - tail ν (x + h - a)) ∂μ := by
    refine (setIntegral_mono_on (integrableOn_const (C := 1 - tail ν h)) hi.integrableOn
      measurableSet_Ioc fun a ha => ?_).trans
      (setIntegral_le_integral hi (Eventually.of_forall fun a => ?_))
    · show 1 - tail ν h ≤ tail ν (x - h - a) - tail ν (x + h - a)
      rw [tail_of_neg hν (show x - h - a < 0 by linarith [ha.1])]
      have := tail_antitone (μ := ν) (show h ≤ x + h - a by linarith [ha.2])
      linarith
    · exact sub_nonneg.2 (tail_antitone (by linarith))
  rwa [setIntegral_const, smul_eq_mul, mul_comm] at key

theorem one_sub_pow_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    (1 - t) ^ n ≤ 1 - n * t + n ^ 2 * t ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h1 : 0 ≤ 1 - t := by linarith
    have h2 : 0 ≤ ((n : ℝ) + 1) * t ^ 2 + (n : ℝ) ^ 2 * t ^ 3 := by positivity
    calc (1 - t) ^ n * (1 - t) ≤ (1 - n * t + n ^ 2 * t ^ 2) * (1 - t) :=
          mul_le_mul_of_nonneg_right ih h1
      _ ≤ _ := by push_cast; nlinarith

end Subexp

open Subexp

namespace IsSubexponential

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- **Convolution roots: tail asymptotics ([EGV]).** If `μ` lives on `[0, ∞)` and
`μ^{*n}` is subexponential (`n ≥ 1`), then `F̄(x) / F̄^{*n}(x) → 1 / n`. -/
theorem tendsto_tail_div_tail_convPow (h0 : μ (Iio 0) = 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : IsSubexponential (Subexp.convPow μ n)) :
    Tendsto (fun x => tail μ x / tail (Subexp.convPow μ n) x) atTop (𝓝 (1 / n)) := by
  set G := Subexp.convPow μ n with hGdef
  set H := Subexp.convPow μ (n - 1) with hHdef
  have hGH : G = μ ∗ H := by rw [hGdef, hHdef, ← convPow_succ, Nat.sub_add_cancel hn]
  have hH0 : H (Iio 0) = 0 := convPow_Iio_zero h0 _
  set N : ℝ := (n : ℝ) with hNdef
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast hn
  obtain ⟨h, hh, hh0⟩ := (((tendsto_order.1 (tendsto_tail_atTop (μ := H))).2 (1 / 2)
    (by norm_num)).and (eventually_ge_atTop (0 : ℝ))).exists
  set d := 1 - tail H h with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hGpos := hG.tail_pos
  set E : ℝ → ℝ := fun x => (tail (Subexp.convPow G n) x - N * tail G x + N ^ 2 * tail G x ^ 2) / d ^ n
    + N * ((tail G (x - h) - tail G (x + h)) / d) with hE
  -- upper bound `Ḡ ≤ n F̄ + E`
  have hup : ∀ x, tail G x ≤ N * tail μ x + E x := by
    intro x
    set P := μ.restrict (Iic (x - h)) with hP
    set D := H.restrict (Iic h) with hD
    have hD0 : D (Iio 0) = 0 :=
      le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self _).trans hH0.le) bot_le
    -- (A) union bound
    have hA := convPow_le_add (μ := μ) (x - h) n (measurableSet_Ioi (a := x))
    have hA' : tail G x ≤ (Subexp.convPow P n).real (Ioi x) + N * tail μ (x - h) := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_ne_top _ _)⟩) hA
      rwa [ENNReal.toReal_add (measure_ne_top _ _)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_ne_top _ _)),
        ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
    -- (B) the regrouping bound
    have hQx : (P ∗ D) (Ioi x) = 0 := by
      rw [conv_apply measurableSet_Ioi]
      refine le_antisymm (le_trans (lintegral_mono_ae ?_) lintegral_zero.le) bot_le
      refine (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun a ha => ?_)
      rw [hD, Measure.restrict_apply (measurableSet_Ioi.preimage (measurable_const_add a))]
      refine (measure_mono_null (fun b hb => ?_) measure_empty).le
      obtain ⟨hb1, hb2⟩ := hb
      simp only [mem_preimage, mem_Ioi, mem_Iic] at hb1 hb2 ha
      linarith
    have hQ : P ∗ D ≤ G.restrict (Iic x) := by
      have hself : (P ∗ D).restrict (Iic x) = P ∗ D := by
        refine Measure.restrict_eq_self_of_ae_mem ?_
        rw [ae_iff]
        convert hQx using 2
        ext y; simp
      rw [← hself, hGH]
      exact Measure.restrict_mono subset_rfl
        (conv_mono Measure.restrict_le_self Measure.restrict_le_self)
    have hB : D univ ^ n * Subexp.convPow P n (Ioi x) + Subexp.convPow G n (Iic x) ≤ G (Iic x) ^ n := by
      have s1 : Subexp.convPow P n (Ioi x) * Subexp.convPow D n univ ≤ Subexp.convPow (P ∗ D) n (Ioi x) := by
        rw [convPow_conv]; exact conv_Ioi_ge (convPow_Iio_zero' hD0 n) x
      have s2 : Subexp.convPow (P ∗ D) n (Ioi x) ≤ Subexp.convPow (G.restrict (Iic x)) n (Ioi x) :=
        Measure.le_iff'.1 (convPow_mono hQ n) _
      have s3 : Subexp.convPow G n (Iic x) ≤ Subexp.convPow (G.restrict (Iic x)) n (Iic x) :=
        convPow_le_convPow_restrict (convPow_Iio_zero h0 n) n measurableSet_Iic subset_rfl
      have s4 : Subexp.convPow (G.restrict (Iic x)) n (Ioi x) + Subexp.convPow (G.restrict (Iic x)) n (Iic x)
          = G (Iic x) ^ n := by
        rw [add_comm, ← measure_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
          Iic_union_Ioi, convPow_univ, Measure.restrict_apply_univ]
      rw [convPow_univ] at s1
      rw [← s4, mul_comm]
      exact add_le_add (s1.trans s2) s3
    have hB' : d ^ n * (Subexp.convPow P n).real (Ioi x) + (1 - tail (Subexp.convPow G n) x) ≤
        (1 - tail G x) ^ n := by
      have := ENNReal.toReal_mono (ENNReal.pow_ne_top (measure_ne_top _ _)) hB
      have e1 : (D univ ^ n).toReal = d ^ n := by
        rw [ENNReal.toReal_pow, hD, Measure.restrict_apply_univ, ← measureReal_def,
          measureReal_Iic_eq]
      have e3 : (Subexp.convPow G n (Iic x)).toReal = 1 - tail (Subexp.convPow G n) x :=
        measureReal_Iic_eq x
      have e4 : (G (Iic x) ^ n).toReal = (1 - tail G x) ^ n := by
        rw [ENNReal.toReal_pow, ← measureReal_def, measureReal_Iic_eq]
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.pow_ne_top (measure_ne_top _ _))
          (measure_ne_top _ _)) (measure_ne_top _ _), ENNReal.toReal_mul, e1, e3, e4] at this
      exact this
    have hpow := one_sub_pow_le (tail_nonneg (μ := G) x) (tail_le_one x) n
    have hψ : (Subexp.convPow P n).real (Ioi x) ≤
        (tail (Subexp.convPow G n) x - N * tail G x + N ^ 2 * tail G x ^ 2) / d ^ n := by
      rw [le_div_iff₀ (pow_pos hdpos n)]
      nlinarith
    -- (C) long tail of `G`
    have hC := tail_sub_le_of_conv (μ := μ) (ν := H) hH0 (x := x) hh0
    rw [← hGH] at hC
    have hC' : tail μ (x - h) - tail μ x ≤ (tail G (x - h) - tail G (x + h)) / d := by
      rw [le_div_iff₀ hdpos]; linarith
    have := mul_le_mul_of_nonneg_left hC' hN.le
    simp only [hE]
    linarith
  -- lower bound `n F̄ - n² F̄² ≤ Ḡ`
  have hlow : ∀ x, N * tail μ x - N ^ 2 * tail μ x ^ 2 ≤ tail G x := by
    intro x
    have h1 := convPow_Iic_le h0 x n
    have := ENNReal.toReal_mono (ENNReal.pow_ne_top (measure_ne_top _ _)) h1
    rw [ENNReal.toReal_pow, ← measureReal_def, ← measureReal_def, measureReal_Iic_eq,
      measureReal_Iic_eq] at this
    have hpow := one_sub_pow_le (tail_nonneg (μ := μ) x) (tail_le_one x) n
    linarith
  -- `E / Ḡ → 0`
  have hEl : Tendsto (fun x => E x / tail G x) atTop (𝓝 0) := by
    have t1 := hG.tendsto_tail_convPow_div hn
    have t2 := tendsto_tail_atTop (μ := G)
    have t3 := hG.tendsto_tail_sub_div h
    have t4 : Tendsto (fun x => tail G (x + h) / tail G x) atTop (𝓝 1) :=
      (hG.tendsto_tail_sub_div (-h)).congr fun x => by rw [sub_neg_eq_add]
    have hlim : Tendsto (fun x => (tail (Subexp.convPow G n) x / tail G x - N + N ^ 2 * tail G x) / d ^ n
        + N * ((tail G (x - h) / tail G x - tail G (x + h) / tail G x) / d)) atTop
        (𝓝 (((n : ℝ) - N + N ^ 2 * 0) / d ^ n + N * ((1 - 1) / d))) :=
      ((((t1.sub_const N).add (t2.const_mul _)).div_const _)).add
        (((t3.sub t4).div_const _).const_mul _)
    rw [hNdef, sub_self, mul_zero, add_zero, zero_div, sub_self, zero_div, mul_zero,
      add_zero] at hlim
    refine hlim.congr fun x => ?_
    have := (hGpos x).ne'
    simp only [hE]
    field_simp
    rw [hNdef]; ring
  -- squeeze
  have hlo : Tendsto (fun x => (1 - E x / tail G x) / N) atTop (𝓝 ((1 - 0) / N)) :=
    (hEl.const_sub 1).div_const N
  have hhi : Tendsto (fun x => 1 / (N * (1 - N * tail μ x))) atTop
      (𝓝 (1 / (N * (1 - N * 0)))) :=
    tendsto_const_nhds.div ((((tendsto_tail_atTop (μ := μ)).const_mul N).const_sub 1).const_mul N)
      (by simp [hN.ne'])
  rw [sub_zero] at hlo
  rw [mul_zero, sub_zero, mul_one] at hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (Eventually.of_forall fun x => ?_) ?_
  · have hGx := hGpos x
    rw [div_le_div_iff₀ hN hGx, sub_mul, div_mul_cancel₀ _ hGx.ne', one_mul]
    have := hup x
    linarith
  · filter_upwards [(tendsto_order.1 ((tendsto_tail_atTop (μ := μ)).const_mul N)).2 1
      (by simp)] with x hx
    have hGx := hGpos x
    have hpos : 0 < N * (1 - N * tail μ x) := mul_pos hN (by linarith)
    rw [div_le_div_iff₀ hGx hpos, one_mul]
    have := hlow x
    nlinarith

/-- **Closure of `𝒮` under convolution roots ([EGV]; [EKM, Appendix A3]).** If `μ` is a
probability measure on `[0, ∞)` and `μ^{*n}` is subexponential for some `n ≥ 1`, then `μ` is
subexponential. -/
theorem of_convPow (h0 : μ (Iio 0) = 0) {n : ℕ} (hn : 1 ≤ n)
    (hG : IsSubexponential (Subexp.convPow μ n)) : IsSubexponential μ :=
  hG.of_tendsto_tail_div h0 (one_div_pos.2 (by exact_mod_cast hn))
    (tendsto_tail_div_tail_convPow h0 hn hG)

end IsSubexponential

end ExtremeValueTheory
