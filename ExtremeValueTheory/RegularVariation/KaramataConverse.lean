/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Karamata
import ExtremeValueTheory.RegularVariation.Representation
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Criteria for regular variation via logarithmic derivatives, and Karamata's theorem

Following Bingham, Goldie and Teugels, *Regular Variation* (Cambridge University Press, 1987),
henceforth [BGT], we give sufficient conditions for regular variation in terms of the
logarithmic derivative, and use them to prove the **converse half of Karamata's theorem**
([BGT, Theorem 1.6.1]).

## Main results

* `ExtremeValueTheory.IsRegularlyVarying.of_tendsto`: a function with a positive finite limit at
  `+∞` is slowly varying.
* `ExtremeValueTheory.IsRegularlyVarying.of_abs_log_sub_le`: if
  `log g y - log g x = ρ (log y - log x) + o(log y - log x)` uniformly in `y ≥ x → ∞`, then `g`
  is regularly varying with index `ρ`.
* `ExtremeValueTheory.IsRegularlyVarying.of_tendsto_mul_deriv_div`: if `g` is eventually positive
  and differentiable and `x g'(x) / g(x) → ρ`, then `g ∈ RV_ρ` (the "von Mises" criterion of
  [BGT, §1.8]).
* `ExtremeValueTheory.IsRegularlyVarying.of_log_sub_eq_integral`: if
  `log g x - log g a = ∫ t in a..x, φ t` with `t φ(t) → ρ`, then `g ∈ RV_ρ` (a form of the
  representation theorem, [BGT, Theorem 1.3.1]).
* `ExtremeValueTheory.IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi`: **Karamata's theorem,
  converse half** ([BGT, Theorem 1.6.1]): if `F` is antitone with `∫ t in Ioi a, F t < ∞` and
  `x F(x) / ∫ t in Ioi x, F t → α - 1 > 0`, then `F ∈ RV_{-α}`.
* `ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_zero_div`: **Karamata's theorem for
  `∫ t in 0..x`** ([BGT, Proposition 1.5.8]): if `f` is measurable, locally integrable on
  `[0, ∞)` and `f ∈ RV_ρ` with `ρ > -1`, then `(∫ t in 0..x, f t) / (x f x) → 1 / (ρ + 1)`.
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

namespace IsRegularlyVarying

/-- A function with a positive finite limit at `+∞` is regularly varying with index `0`. -/
theorem of_tendsto {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hf : Tendsto f atTop (𝓝 c)) :
    IsRegularlyVarying f 0 := by
  refine ⟨hf.eventually (lt_mem_nhds hc), fun l hl => ?_⟩
  have := (hf.comp (tendsto_id.const_mul_atTop hl)).div hf hc.ne'
  rw [div_self hc.ne'] at this
  rw [rpow_zero]
  exact this

/-- If `log g y - log g x - ρ (log y - log x) = o(log y - log x)` uniformly in `y ≥ x → ∞`, then
`g` is regularly varying with index `ρ`. -/
theorem of_abs_log_sub_le {g : ℝ → ℝ} {ρ : ℝ} (hpos : ∀ᶠ x in atTop, 0 < g x)
    (h : ∀ ε > 0, ∃ T, ∀ x ≥ T, ∀ y ≥ x,
      |log (g y) - log (g x) - ρ * (log y - log x)| ≤ ε * (log y - log x)) :
    IsRegularlyVarying g ρ := by
  refine ⟨hpos, fun c hc => ?_⟩
  have hlog : Tendsto (fun x => log (g (c * x)) - log (g x)) atTop (𝓝 (ρ * log c)) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    have hη' : 0 < η / (|log c| + 1) := by positivity
    obtain ⟨T, hT⟩ := h _ hη'
    set K := η / (|log c| + 1) with hK
    filter_upwards [eventually_ge_atTop T, (tendsto_id.const_mul_atTop hc).eventually
      (eventually_ge_atTop T), eventually_gt_atTop 0] with x hx hcx hx0
    have hcx' : T ≤ c * x := hcx
    have hlc : log (c * x) = log c + log x := log_mul hc.ne' hx0.ne'
    have key : |log (g (c * x)) - log (g x) - ρ * log c| ≤ K * |log c| := by
      rcases le_total 1 c with h1 | h1
      · have := hT x hx (c * x) (by nlinarith)
        rw [hlc, add_sub_cancel_right] at this
        rwa [abs_of_nonneg (log_nonneg h1)]
      · have := hT (c * x) hcx' x (by nlinarith)
        rw [hlc, show log x - (log c + log x) = -log c by ring] at this
        rw [abs_of_nonpos (log_nonpos hc.le h1), ← abs_neg]
        convert this using 2
        ring
    rw [Real.dist_eq]
    calc _ ≤ K * |log c| := key
      _ < K * (|log c| + 1) := by gcongr; linarith
      _ = η := by rw [hK]; field_simp
  have := (continuous_exp.tendsto _).comp hlog
  rw [rpow_def_of_pos hc, mul_comm]
  refine this.congr' ?_
  filter_upwards [hpos, (tendsto_id.const_mul_atTop hc).eventually hpos] with x h1 h2
  simp only [Function.comp_apply, id] at h2 ⊢
  rw [exp_sub, exp_log h1, exp_log h2]

/-- **A logarithmic-derivative criterion for regular variation** ([BGT, §1.8]): if `g` is
eventually positive and differentiable with derivative `g'`, and `x g'(x) / g(x) → ρ`, then `g`
is regularly varying with index `ρ`. -/
theorem of_tendsto_mul_deriv_div {g g' : ℝ → ℝ} {ρ : ℝ}
    (hd : ∀ᶠ x in atTop, HasDerivAt g (g' x) x) (hpos : ∀ᶠ x in atTop, 0 < g x)
    (h : Tendsto (fun x => x * g' x / g x) atTop (𝓝 ρ)) : IsRegularlyVarying g ρ := by
  refine of_abs_log_sub_le hpos fun ε hε => ?_
  have hr : ∀ᶠ x in atTop, |x * g' x / g x - ρ| ≤ ε := by
    filter_upwards [Metric.tendsto_nhds.1 h ε hε] with x hx
    exact (Real.dist_eq _ _ ▸ hx).le
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hd.and (hpos.and (hr.and (eventually_gt_atTop 0))))
  refine ⟨T, fun x hx y hy => ?_⟩
  -- the derivatives of `ε log t ∓ (log g t - ρ log t)`
  have hderiv : ∀ s : ℝ, ∀ t ≥ T, s = 1 ∨ s = -1 →
      HasDerivAt (fun u => ε * log u + s * (log (g u) - ρ * log u))
        (ε * t⁻¹ + s * (g' t / g t - ρ * t⁻¹)) t ∧ 0 ≤ ε * t⁻¹ + s * (g' t / g t - ρ * t⁻¹) := by
    intro s t ht hs
    obtain ⟨hdt, hgt, hrt, ht0⟩ := hT t ht
    refine ⟨((hasDerivAt_log ht0.ne').const_mul ε).add
      (((hdt.log hgt.ne').sub ((hasDerivAt_log ht0.ne').const_mul ρ)).const_mul s), ?_⟩
    have e : ε * t⁻¹ + s * (g' t / g t - ρ * t⁻¹) = (ε + s * (t * g' t / g t - ρ)) / t := by
      field_simp
    rw [e]
    refine div_nonneg ?_ ht0.le
    rcases hs with rfl | rfl
    · linarith [neg_abs_le (t * g' t / g t - ρ)]
    · linarith [le_abs_self (t * g' t / g t - ρ)]
  have hmono : ∀ s : ℝ, s = 1 ∨ s = -1 →
      MonotoneOn (fun u => ε * log u + s * (log (g u) - ρ * log u)) (Ici T) := by
    intro s hs
    refine monotoneOn_of_deriv_nonneg (convex_Ici T) ?_ ?_ ?_
    · exact fun t ht => (hderiv s t ht hs).1.continuousAt.continuousWithinAt
    · rw [interior_Ici]
      exact fun t ht => (hderiv s t (le_of_lt ht) hs).1.differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      rw [(hderiv s t (le_of_lt ht) hs).1.deriv]
      exact (hderiv s t (le_of_lt ht) hs).2
  have hxy : x ≤ y := hy
  have h1 := hmono 1 (Or.inl rfl) (mem_Ici.2 hx) (mem_Ici.2 (hx.trans hxy)) hxy
  have h2 := hmono (-1) (Or.inr rfl) (mem_Ici.2 hx) (mem_Ici.2 (hx.trans hxy)) hxy
  simp only at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **Regular variation from an integral representation of the logarithm** (compare
[BGT, Theorem 1.3.1]): if `g > 0` on `[a, ∞)` with `a > 0`,
`log g x - log g a = ∫ t in a..x, φ t` for `x ≥ a`, and `t φ(t) → ρ`, then `g` is regularly
varying with index `ρ`. -/
theorem of_log_sub_eq_integral {g φ : ℝ → ℝ} {ρ a : ℝ} (ha : 0 < a) (hpos : ∀ x ≥ a, 0 < g x)
    (hint : ∀ x ≥ a, IntervalIntegrable φ volume a x)
    (heq : ∀ x ≥ a, log (g x) - log (g a) = ∫ t in a..x, φ t)
    (hφ : Tendsto (fun t => t * φ t) atTop (𝓝 ρ)) : IsRegularlyVarying g ρ := by
  set ε : ℝ → ℝ := fun t => t * φ t - ρ with hε_def
  have hε : Tendsto ε atTop (𝓝 0) := by simpa using hφ.sub_const ρ
  have hinv : ∀ x ≥ a, IntervalIntegrable (fun t : ℝ => t⁻¹) volume a x := fun x hx =>
    intervalIntegral.intervalIntegrable_inv (fun t ht => (ha.trans_le (by
      rw [uIcc_of_le hx] at ht; exact ht.1)).ne') continuousOn_id
  have heqOn : ∀ x ≥ a, EqOn (fun t => ε t / t) (fun t => φ t - ρ * t⁻¹) (uIcc a x) := by
    intro x hx t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    simp only [hε_def]
    field_simp
  have hεint : ∀ x ≥ a, IntervalIntegrable (fun t => ε t / t) volume a x := fun x hx =>
    (((hint x hx).sub ((hinv x hx).const_mul ρ))).congr
      fun t ht => (heqOn x hx (uIoc_subset_uIcc ht)).symm
  have hrep : ∀ x ≥ a, g x * x ^ (-ρ) = (g a * a ^ (-ρ)) * exp (∫ t in a..x, ε t / t) := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx
    have hI : ∫ t in a..x, ε t / t = (log (g x) - log (g a)) - ρ * log (x / a) := by
      rw [intervalIntegral.integral_congr (heqOn x hx),
        intervalIntegral.integral_sub (hint x hx) ((hinv x hx).const_mul ρ),
        intervalIntegral.integral_const_mul, integral_inv_of_pos ha hx0, heq x hx]
    have hga := hpos a le_rfl
    have hgx := hpos x hx
    rw [hI, exp_sub, exp_sub, exp_log hgx, exp_log hga, mul_comm ρ, ← rpow_def_of_pos
      (div_pos hx0 ha), div_rpow hx0.le ha.le, rpow_neg hx0.le, rpow_neg ha.le]
    have := rpow_pos_of_pos hx0 ρ
    have := rpow_pos_of_pos ha ρ
    field_simp
  have hL : IsSlowlyVarying (fun x => g x * x ^ (-ρ)) :=
    IsSlowlyVarying.of_representation (c := fun _ => g a * a ^ (-ρ))
      (mul_pos (hpos a le_rfl) (rpow_pos_of_pos ha _)) tendsto_const_nhds hε hεint hrep
  have := hL.isRegularlyVarying.mul (rpow_id ρ)
  rw [zero_add] at this
  refine this.congr ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [mul_assoc, ← rpow_add hx, neg_add_cancel, rpow_zero, mul_one]

/-- **Karamata's theorem, converse half** ([BGT, Theorem 1.6.1]; compare
[BGT, Theorem 1.5.11]): let `F` be antitone and integrable on some half-line `Ioi a`. If
`x F(x) / ∫ t in Ioi x, F t → α - 1` with `α > 1`, then `F` is regularly varying with index
`-α`.

The proof: `I x = ∫ t in Ioi x, F t` is continuous, positive for large `x`, and has derivative
`-F x` wherever `F` is continuous, i.e. off a countable set. Hence
`log I x - log I b = -∫ t in b..x, F t / I t`, and since `t * (F t / I t) → α - 1`,
`I ∈ RV_{1-α}` (`IsRegularlyVarying.of_log_sub_eq_integral`). Finally
`F x = (x F x / I x) * I x * x⁻¹` is a product of regularly varying functions. -/
theorem of_tendsto_mul_div_integral_Ioi {F : ℝ → ℝ} {α a : ℝ} (hF : Antitone F)
    (hint : IntegrableOn F (Ioi a)) (hα : 1 < α)
    (h : Tendsto (fun x => x * F x / ∫ t in Ioi x, F t) atTop (𝓝 (α - 1))) :
    IsRegularlyVarying F (-α) := by
  set I : ℝ → ℝ := fun x => ∫ t in Ioi x, F t with hI_def
  -- `F` is integrable on every half-line
  have hIx : ∀ x, IntegrableOn F (Ioi x) := by
    intro x
    refine IntegrableOn.mono_set (IntegrableOn.union ((hF.antitoneOn _).integrableOn_isCompact
      (isCompact_Icc (a := x) (b := max x a))) hint) fun t ht => ?_
    rcases le_or_gt t (max x a) with h' | h'
    · exact Or.inl ⟨le_of_lt ht, h'⟩
    · exact Or.inr ((le_max_right _ _).trans_lt h')
  -- `F` is nonnegative, since otherwise it would not be integrable on a half-line
  have hF0 : ∀ x, 0 ≤ F x := by
    intro x
    by_contra hneg
    push Not at hneg
    have hc : IntegrableOn (fun _ => F x) (Ioi x) := by
      refine Integrable.mono (hIx x) aestronglyMeasurable_const
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
      have hFt : F t ≤ F x := hF (le_of_lt ht)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hneg, abs_of_neg (hFt.trans_lt hneg)]
      linarith
    rw [integrableOn_const_iff] at hc
    simp [hneg.ne] at hc
  have hI0 : ∀ x, 0 ≤ I x := fun x => setIntegral_nonneg measurableSet_Ioi fun t _ => hF0 t
  -- eventual positivity
  have hr : ∀ᶠ x in atTop, 0 < x * F x / I x := h.eventually (lt_mem_nhds (by linarith))
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 (hr.and (eventually_gt_atTop 0))
  set b := max b₀ 1 with hb_def
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hpos : ∀ x ≥ b, 0 < I x ∧ 0 < F x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hb₀ x (le_trans (le_max_left _ _) hx)
    have hIne : I x ≠ 0 := by
      intro h0
      rw [h0, div_zero] at h1
      exact lt_irrefl _ h1
    have hIpos := lt_of_le_of_ne (hI0 x) (Ne.symm hIne)
    exact ⟨hIpos, pos_of_mul_pos_right ((div_pos_iff_of_pos_right hIpos).1 h1) h2.le⟩
  -- continuity and differentiability of `I`
  have hFii : ∀ u v, IntervalIntegrable F volume u v := fun _ _ => hF.intervalIntegrable
  have hIeq : ∀ t, I t = I b - ∫ s in b..t, F s := fun t => by
    have := intervalIntegral.integral_interval_add_Ioi (hIx b) (hIx t)
    show (∫ s in Ioi t, F s) = (∫ s in Ioi b, F s) - _
    linarith
  have hIcont : Continuous I :=
    (continuous_const.sub (intervalIntegral.continuous_primitive hFii b)).congr
      fun t => (hIeq t).symm
  have hIderiv : ∀ t, ContinuousAt F t → HasDerivAt I (-F t) t := by
    intro t ht
    have := (intervalIntegral.integral_hasDerivAt_right (hFii b t)
      hF.measurable.stronglyMeasurable.stronglyMeasurableAtFilter ht).const_sub (I b)
    exact this.congr_of_eventuallyEq (Eventually.of_forall hIeq)
  have hφint : ∀ x ≥ b, IntervalIntegrable (fun t => -F t / I t) volume b x := by
    intro x hx
    have := (hFii b x).neg.mul_continuousOn (hIcont.continuousOn.inv₀ fun t ht => by
      rw [uIcc_of_le hx] at ht
      exact (hpos t ht.1).1.ne')
    simpa only [div_eq_mul_inv, Pi.neg_apply, Pi.inv_apply] using this
  -- the logarithm of `I` as an integral
  have hlog : ∀ x ≥ b, log (I x) - log (I b) = ∫ t in b..x, -F t / I t := by
    intro x hx
    symm
    refine integral_eq_of_hasDerivAt_off_countable_of_le (fun t => log (I t))
      (fun t => -F t / I t) hx hF.countable_not_continuousAt
      (hIcont.continuousOn.log fun t ht => (hpos t ht.1).1.ne') (fun t ht => ?_) (hφint x hx)
    have hc : ContinuousAt F t := by simpa using ht.2
    exact (hIderiv t hc).log (hpos t ht.1.1.le).1.ne'
  have hIRV : IsRegularlyVarying I (1 - α) := by
    refine of_log_sub_eq_integral hb (fun x hx => (hpos x hx).1) hφint hlog ?_
    have := h.neg
    rw [neg_sub] at this
    refine this.congr fun t => ?_
    ring
  have hrRV := of_tendsto (by linarith : (0 : ℝ) < α - 1) h
  have := (hrRV.mul hIRV).mul (rpow_id (-1))
  rw [show (0 : ℝ) + (1 - α) + -1 = -α by ring] at this
  refine this.congr ?_
  filter_upwards [eventually_ge_atTop b] with x hx
  have hx0 : 0 < x := hb.trans_le hx
  have := (hpos x hx).1
  change x * F x / I x * I x * x ^ (-1 : ℝ) = F x
  rw [rpow_neg_one]
  field_simp

/-- **Karamata's theorem for integrals over `[0, x]`** (the direct half, [BGT, Proposition 1.5.8]
and [BGT, Theorem 1.5.11 (i)]): if `f` is measurable, integrable on every `[0, x]` and regularly
varying with index `ρ > -1`, then `(∫ t in 0..x, f t) / (x * f x) → 1 / (ρ + 1)` as `x → ∞`.

After the substitution `t = x u`, the part of the integral over `[x₀, x]` becomes
`∫ u in Ioc 0 1, 1_{u > x₀ / x} f (x u) / f x`, which converges to `∫ u in 0..1, u ^ ρ` by
dominated convergence with the Potter bound `2 u ^ (ρ - δ)`, `δ = (ρ + 1) / 2`; the part over
`[0, x₀]` is negligible since `x f x → ∞`. -/
theorem tendsto_integral_zero_div {f : ℝ → ℝ} {ρ : ℝ} (hf : IsRegularlyVarying f ρ)
    (hm : Measurable f) (hρ : -1 < ρ) (hint : ∀ x, IntervalIntegrable f volume 0 x) :
    Tendsto (fun x => (∫ t in (0 : ℝ)..x, f t) / (x * f x)) atTop (𝓝 (1 / (ρ + 1))) := by
  set δ := (ρ + 1) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  have hexp : -1 < ρ - δ := by rw [hδ_def]; linarith
  obtain ⟨x₀, hx₀, hfpos, hP⟩ := hf.potter_bound_of_measurable hm hδ one_lt_two
  -- `x f x → ∞`
  have hxf : Tendsto (fun x => x * f x) atTop atTop := by
    have hfx₀ := hfpos x₀ le_rfl
    have hlow : ∀ x ≥ x₀, f x₀ / (2 * x₀ ^ (ρ - δ)) * x ^ (ρ - δ + 1) ≤ x * f x := by
      intro x hx
      have hx0 : 0 < x := hx₀.trans_le hx
      have hfx := hfpos x hx
      have h := hP x hx x₀ le_rfl
      have hu1 : x₀ / x ≤ 1 := (div_le_one hx0).2 hx
      have hu0 : 0 < x₀ / x := div_pos hx₀ hx0
      rw [max_eq_right (rpow_le_rpow_of_exponent_ge hu0 hu1 (by linarith)),
        div_rpow hx₀.le hx0.le, div_le_iff₀ hfx] at h
      have hA := rpow_pos_of_pos hx₀ (ρ - δ)
      have hB := rpow_pos_of_pos hx0 (ρ - δ)
      have key : f x₀ * x ^ (ρ - δ) ≤ 2 * x₀ ^ (ρ - δ) * f x := by
        calc f x₀ * x ^ (ρ - δ) ≤ 2 * (x₀ ^ (ρ - δ) / x ^ (ρ - δ)) * f x * x ^ (ρ - δ) := by
              gcongr
          _ = 2 * x₀ ^ (ρ - δ) * f x := by field_simp
      rw [rpow_add hx0, rpow_one, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    refine tendsto_atTop_mono' atTop ((eventually_ge_atTop x₀).mono hlow) ?_
    exact (tendsto_rpow_atTop (by linarith : 0 < ρ - δ + 1)).const_mul_atTop
      (div_pos hfx₀ (mul_pos two_pos (rpow_pos_of_pos hx₀ _)))
  -- the value of the limit
  have hlim : ∫ u in Ioc (0 : ℝ) 1, u ^ ρ = 1 / (ρ + 1) := by
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hρ), one_rpow,
      zero_rpow (by linarith : ρ + 1 ≠ 0), sub_zero]
  -- the main part, by dominated convergence
  set g : ℝ → ℝ → ℝ := fun x u => (Ioi (x₀ / x)).indicator (fun u => f (x * u) / f x) u
    with hg_def
  have hmain : Tendsto (fun x => ∫ u in Ioc (0 : ℝ) 1, g x u) atTop (𝓝 (1 / (ρ + 1))) := by
    rw [← hlim]
    refine tendsto_integral_filter_of_dominated_convergence (fun u => 2 * u ^ (ρ - δ)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x => (((hm.comp (measurable_id.const_mul x)).div_const
        _).indicator measurableSet_Ioi).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop x₀] with x hx
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
      have hx0 : 0 < x := hx₀.trans_le hx
      simp only [hg_def]
      by_cases hux : u ∈ Ioi (x₀ / x)
      · rw [indicator_of_mem hux]
        have hxu : x₀ ≤ x * u := by
          have := (div_lt_iff₀ hx0).1 (mem_Ioi.1 hux)
          linarith
        have h := hP x hx (x * u) hxu
        rw [mul_div_cancel_left₀ u hx0.ne',
          max_eq_right (rpow_le_rpow_of_exponent_ge hu.1 hu.2 (by linarith))] at h
        rw [Real.norm_eq_abs, abs_of_pos (div_pos (hfpos _ hxu) (hfpos _ hx))]
        exact h
      · rw [indicator_of_notMem hux, norm_zero]
        exact mul_nonneg zero_le_two (rpow_nonneg hu.1.le _)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        ((intervalIntegral.intervalIntegrable_rpow' hexp).const_mul 2)
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
      have hu0 : 0 < u := hu.1
      refine ((hf.2 u hu0).congr fun x => by rw [mul_comm]).congr' ?_
      filter_upwards [eventually_gt_atTop (x₀ / u)] with x hx
      have hx0 : 0 < x := lt_trans (div_pos hx₀ hu0) hx
      have hmem : u ∈ Ioi (x₀ / x) := by
        rw [mem_Ioi, div_lt_iff₀ hx0]
        rw [div_lt_iff₀ hu0] at hx
        linarith
      simp only [hg_def, indicator_of_mem hmem]
  -- the part over `[0, x₀]` is negligible
  have hconst : Tendsto (fun x => (∫ t in (0 : ℝ)..x₀, f t) / (x * f x)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hxf).const_mul (∫ t in (0 : ℝ)..x₀, f t)
    rw [mul_zero] at this
    exact this.congr fun x => (div_eq_mul_inv _ _).symm
  have := hconst.add hmain
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop x₀] with x hx
  have hx0 : 0 < x := hx₀.trans_le hx
  have hfx := hfpos x hx
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint x₀)
    ((hint x₀).symm.trans (hint x))
  have hset : Ioc (0 : ℝ) 1 ∩ Ioi (x₀ / x) = Ioc (x₀ / x) 1 := by
    ext u
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨(div_pos hx₀ hx0).trans h1, h2⟩, h1⟩
  have hsub : ∫ u in Ioc (0 : ℝ) 1, g x u = (∫ t in x₀..x, f t) / (x * f x) := by
    simp only [hg_def]
    rw [setIntegral_indicator measurableSet_Ioi, hset,
      ← intervalIntegral.integral_of_le ((div_le_one hx0).2 hx), intervalIntegral.integral_div,
      intervalIntegral.integral_comp_mul_left f hx0.ne', mul_div_cancel₀ _ hx0.ne', mul_one,
      smul_eq_mul]
    field_simp
  rw [hsub, ← hsplit, add_div]

end IsRegularlyVarying

end ExtremeValueTheory
