/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Karamata
import ExtremeValueTheory.RegularVariation.Representation
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

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
* `ExtremeValueTheory.IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi_of_pos`: **Karamata's
  theorem, converse half, tail integrals** ([BGT, Theorem 1.6.1]): if `F` is eventually positive and
  `x F(x) / ∫ t in Ioi x, F t → α - 1 > 0`, then `F ∈ RV_{-α}`. No monotonicity, measurability or
  integrability is assumed.
* `ExtremeValueTheory.IsRegularlyVarying.of_tendsto_mul_div_integral`: the case `ρ > -1`: if `f` is
  eventually positive and `x f(x) / ∫ t in a..x, f t → ρ + 1 > 0`, then `f ∈ RV_ρ`.
* `ExtremeValueTheory.IsRegularlyVarying.of_tendsto_rpow_mul_div_integral`,
  `..._integral_Ioi`: the same with the weights `t ^ σ`.
* `ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_interval_div`: **Karamata's theorem for
  `∫ t in a..x`** ([BGT, Proposition 1.5.8]): if `f` is measurable, integrable on `[a, x]` for
  `x ≥ a`, and `f ∈ RV_ρ` with `ρ > -1`, then `(∫ t in a..x, f t) / (x f x) → 1 / (ρ + 1)`.
* `ExtremeValueTheory.IsRegularlyVarying.exists_tendsto_integral_interval_div`: the same with no
  integrability hypothesis, for all large `a`.
* `ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_Ioi_div_of_measurable` and
  `ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_Ioi_div_of_antitoneOn`: Karamata's
  theorem for tail integrals ([BGT, Proposition 1.5.10]) for measurable, resp. eventually
  antitone, `F` (generalizing `IsRegularlyVarying.tendsto_integral_Ioi_div`).
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

/-- The fundamental theorem of calculus for `log ∘ G`, where `G` is positive and an indefinite
integral of `g`. Here `g` is only integrable: `G` is absolutely continuous, not differentiable. -/
private lemma log_sub_eq_integral_div {g G : ℝ → ℝ} {b x : ℝ} (hx : b ≤ x)
    (hg : IntervalIntegrable g volume b x)
    (hG : ∀ t ∈ Icc b x, G t = G b + ∫ s in b..t, g s) (hpos : ∀ t ∈ Icc b x, 0 < G t) :
    log (G x) - log (G b) = ∫ t in b..x, g t / G t := by
  have hb : b ∈ uIcc b x := left_mem_uIcc
  have hAC := hg.absolutelyContinuousOnInterval_intervalIntegral hb
  set P : ℝ → ℝ := fun t => ∫ s in b..t, g s with hP
  have hPc : ContinuousOn P (Icc b x) := by
    have := hAC.continuousOn
    rwa [uIcc_of_le hx] at this
  have hGc : ContinuousOn G (Icc b x) :=
    (continuousOn_const.add hPc).congr hG
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨b, left_mem_Icc.2 hx⟩ hGc
  set m := G t₀ with hm
  have hm0 : 0 < m := hpos t₀ ht₀
  -- `y ↦ log (G b + y)` is Lipschitz on `{y | m ≤ G b + y}`
  have hLip : LipschitzOnWith (Real.toNNReal m⁻¹) (fun y => log (G b + y)) (Ici (m - G b)) := by
    have hd : ∀ y ∈ Ici (m - G b), HasDerivWithinAt (fun y => log (G b + y)) (G b + y)⁻¹
        (Ici (m - G b)) y := fun y hy => by
      have hy' : m ≤ G b + y := by have : m - G b ≤ y := hy; linarith
      have h0 : G b + y ≠ 0 := (hm0.trans_le hy').ne'
      have := ((hasDerivAt_id y).const_add (G b)).log h0
      simpa [div_eq_mul_inv] using this.hasDerivWithinAt
    refine (convex_Ici _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hd fun y hy => ?_
    have hy' : m ≤ G b + y := by have : m - G b ≤ y := hy; linarith
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (inv_nonneg.2 hm0.le), norm_inv,
      Real.norm_eq_abs, abs_of_pos (hm0.trans_le hy')]
    exact inv_anti₀ hm0 hy'
  have hmaps : MapsTo P (uIcc b x) (Ici (m - G b)) := fun t ht => by
    rw [uIcc_of_le hx] at ht
    have h1 : m ≤ G t := hmin ht
    rw [hG t ht] at h1
    show m - G b ≤ P t
    linarith
  have hAC2 := hLip.comp_absolutelyContinuousOnInterval hmaps hAC
  have hFTC := hAC2.integral_deriv_eq_sub
  have hb' : b ∈ Icc b x := left_mem_Icc.2 hx
  have hx' : x ∈ Icc b x := right_mem_Icc.2 hx
  have hval : ∀ t ∈ Icc b x, ((fun y => log (G b + y)) ∘ P) t = log (G t) := fun t ht => by
    simp only [Function.comp_apply]
    rw [← hG t ht]
  rw [hval x hx', hval b hb'] at hFTC
  rw [← hFTC]
  refine (intervalIntegral.integral_congr_ae ?_).symm
  filter_upwards [hg.ae_hasDerivAt_integral] with t ht htmem
  rw [uIoc_of_le hx] at htmem
  have htI : t ∈ Icc b x := Ioc_subset_Icc_self htmem
  have htu : t ∈ uIcc b x := by rwa [uIcc_of_le hx]
  have hd := ht htu b hb
  have hne : G b + P t ≠ 0 := by
    rw [← hG t htI]
    exact (hpos t htI).ne'
  have := (hd.const_add (G b)).log hne
  have hderiv : deriv ((fun y => log (G b + y)) ∘ P) t = g t / (G b + P t) := this.deriv
  rw [hderiv, ← hG t htI]

/-- A positive indefinite integral `G` of `g` with `t g(t) / G(t) → ρ` is regularly varying with
index `ρ`. The common core of both halves of Karamata's converse. -/
private lemma of_tendsto_mul_div_of_eq_integral {g G : ℝ → ℝ} {ρ b : ℝ} (hb : 0 < b)
    (hg : ∀ x ≥ b, IntervalIntegrable g volume b x)
    (hG : ∀ x ≥ b, G x = G b + ∫ s in b..x, g s) (hpos : ∀ x ≥ b, 0 < G x)
    (h : Tendsto (fun t => t * g t / G t) atTop (𝓝 ρ)) : IsRegularlyVarying G ρ := by
  have hint : ∀ x ≥ b, IntervalIntegrable (fun t => g t / G t) volume b x := by
    intro x hx
    have hc : ContinuousOn G (uIcc b x) := by
      have := ((hg x hx).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
      refine ContinuousOn.congr (f := fun t => G b + ∫ s in b..t, g s)
        (continuousOn_const.add this) fun t ht => ?_
      rw [uIcc_of_le hx] at ht
      exact hG t ht.1
    have := (hg x hx).mul_continuousOn (hc.inv₀ fun t ht => by
      rw [uIcc_of_le hx] at ht
      exact (hpos t ht.1).ne')
    simpa only [div_eq_mul_inv, Pi.inv_apply] using this
  refine of_log_sub_eq_integral hb hpos hint (fun x hx => log_sub_eq_integral_div hx (hg x hx)
    (fun t ht => hG t ht.1) (fun t ht => hpos t ht.1)) ?_
  exact h.congr fun t => by rw [mul_div_assoc]

/-- If `G` is regularly varying with index `σ`, and `x f(x) / G(x) → r > 0`, then `f` is regularly
varying with index `σ - 1`. -/
private lemma of_tendsto_mul_div {f G : ℝ → ℝ} {σ r : ℝ} (hG : IsRegularlyVarying G σ) (hr : 0 < r)
    (h : Tendsto (fun x => x * f x / G x) atTop (𝓝 r)) : IsRegularlyVarying f (σ - 1) := by
  have := ((of_tendsto hr h).mul hG).mul (rpow_id (-1))
  rw [show (0 : ℝ) + σ + -1 = σ - 1 by ring] at this
  refine this.congr ?_
  filter_upwards [eventually_gt_atTop 0, hG.1] with x hx hGx
  rw [rpow_neg_one]
  field_simp

/-- **Karamata's theorem, converse half, for tail integrals** (the case `σ = 0` of
[BGT, Theorem 1.6.1], see `of_tendsto_rpow_mul_div_integral_Ioi`; compare [BGT, Theorem 1.5.11]): if
`F` is eventually positive and `x F(x) / ∫ t in Ioi x, F t → α - 1` with `α > 1`, then `F` is
regularly varying with index `-α`.

Neither monotonicity, measurability nor integrability is assumed. Integrability on a half-line
follows: for a non-integrable `F` the Bochner integral is `0`, the ratio is `0`, and it cannot tend
to `α - 1 ≠ 0`. Eventual positivity cannot be dropped, as `-F` satisfies the same limit.

The proof: `I x = ∫ t in Ioi x, F t` is positive for large `x`, and it is absolutely continuous with
`I' = -F` almost everywhere. Hence `log I x - log I b = -∫ t in b..x, F t / I t`, and since
`t * (F t / I t) → α - 1`, `I ∈ RV_{1-α}` (`IsRegularlyVarying.of_log_sub_eq_integral`). Finally
`F x = (x F x / I x) * I x * x⁻¹` is a product of regularly varying functions. -/
theorem of_tendsto_mul_div_integral_Ioi_of_pos {F : ℝ → ℝ} {α : ℝ}
    (hpos : ∀ᶠ x in atTop, 0 < F x) (hα : 1 < α)
    (h : Tendsto (fun x => x * F x / ∫ t in Ioi x, F t) atTop (𝓝 (α - 1))) :
    IsRegularlyVarying F (-α) := by
  set I : ℝ → ℝ := fun x => ∫ t in Ioi x, F t with hI_def
  have hr : ∀ᶠ x in atTop, 0 < x * F x / I x := h.eventually (lt_mem_nhds (by linarith))
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 (hr.and (hpos.and (eventually_gt_atTop 0)))
  set b := max b₀ 1 with hb_def
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb₁ : ∀ x ≥ b, 0 < x * F x / I x ∧ 0 < F x ∧ 0 < x := fun x hx =>
    hb₀ x ((le_max_left _ _).trans hx)
  have hIpos : ∀ x ≥ b, 0 < I x := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := hb₁ x hx
    exact (div_pos_iff_of_pos_left (mul_pos h3 h2)).1 h1
  have hIb : IntegrableOn F (Ioi b) := by
    by_contra hni
    have : I b = 0 := integral_undef hni
    exact (hIpos b le_rfl).ne' this
  have hIx : ∀ x ≥ b, IntegrableOn F (Ioi x) := fun x hx => hIb.mono_set (Ioi_subset_Ioi hx)
  have hFi : ∀ x ≥ b, IntervalIntegrable F volume b x := fun x hx =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 (hIb.mono_set Ioc_subset_Ioi_self)
  have hIRV : IsRegularlyVarying I (1 - α) := by
    refine of_tendsto_mul_div_of_eq_integral (g := fun t => -F t) hb (fun x hx => (hFi x hx).neg)
      (fun x hx => ?_) hIpos ?_
    · have := intervalIntegral.integral_interval_add_Ioi hIb (hIx x hx)
      rw [intervalIntegral.integral_neg]
      simp only [hI_def]
      linarith
    · have := h.neg
      rw [neg_sub] at this
      refine this.congr fun t => ?_
      ring
  have := of_tendsto_mul_div hIRV (by linarith : (0 : ℝ) < α - 1) h
  rwa [show 1 - α - 1 = -α by ring] at this

/-- **Karamata's theorem, converse half, for integrals over `[a, x]`** (the case `σ = 0` of
[BGT, Theorem 1.6.1], see `of_tendsto_rpow_mul_div_integral`; compare [BGT, Theorem 1.5.11]): if `f`
is eventually positive and `x f(x) / ∫ t in a..x, f t → ρ + 1` with `ρ > -1`, then `f` is regularly
varying with index `ρ`.

Neither monotonicity, measurability nor integrability is assumed: integrability on `[a, x]` for
large `x` follows, as a non-integrable `f` gives integral `0` and ratio `0`. -/
theorem of_tendsto_mul_div_integral {f : ℝ → ℝ} {ρ a : ℝ} (hpos : ∀ᶠ x in atTop, 0 < f x)
    (hρ : -1 < ρ) (h : Tendsto (fun x => x * f x / ∫ t in a..x, f t) atTop (𝓝 (ρ + 1))) :
    IsRegularlyVarying f ρ := by
  set J : ℝ → ℝ := fun x => ∫ t in a..x, f t with hJ_def
  have hr : ∀ᶠ x in atTop, 0 < x * f x / J x := h.eventually (lt_mem_nhds (by linarith))
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 (hr.and (hpos.and (eventually_gt_atTop 0)))
  set b := max b₀ 1 with hb_def
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb₁ : ∀ x ≥ b, 0 < x * f x / J x ∧ 0 < f x ∧ 0 < x := fun x hx =>
    hb₀ x ((le_max_left _ _).trans hx)
  have hJpos : ∀ x ≥ b, 0 < J x := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := hb₁ x hx
    exact (div_pos_iff_of_pos_left (mul_pos h3 h2)).1 h1
  have hfa : ∀ x ≥ b, IntervalIntegrable f volume a x := fun x hx => by
    by_contra hni
    have : J x = 0 := intervalIntegral.integral_undef hni
    exact (hJpos x hx).ne' this
  have hfi : ∀ x ≥ b, IntervalIntegrable f volume b x := fun x hx =>
    (hfa b le_rfl).symm.trans (hfa x hx)
  have hJRV : IsRegularlyVarying J (ρ + 1) := by
    refine of_tendsto_mul_div_of_eq_integral (g := f) hb hfi (fun x hx => ?_) hJpos h
    exact (intervalIntegral.integral_add_adjacent_intervals (hfa b le_rfl) (hfi x hx)).symm
  have := of_tendsto_mul_div hJRV (by linarith : (0 : ℝ) < ρ + 1) h
  rwa [add_sub_cancel_right] at this

/-- **Karamata's theorem, converse half, with weights, for integrals over `[a, x]`** ([BGT, Theorem
1.6.1], as we recall it; the book was not available to check the statement): if `f` is eventually
positive and, for some `σ` with `σ + ρ > -1`,
`x ^ (σ + 1) f(x) / ∫ t in a..x, t ^ σ f t → σ + ρ + 1`, then `f` is regularly varying with
index `ρ`. -/
theorem of_tendsto_rpow_mul_div_integral {f : ℝ → ℝ} {ρ σ a : ℝ} (hpos : ∀ᶠ x in atTop, 0 < f x)
    (hσ : -1 < σ + ρ)
    (h : Tendsto (fun x => x ^ (σ + 1) * f x / ∫ t in a..x, t ^ σ * f t) atTop (𝓝 (σ + ρ + 1))) :
    IsRegularlyVarying f ρ := by
  have hpos' : ∀ᶠ x : ℝ in atTop, 0 < x ^ σ * f x := by
    filter_upwards [hpos, eventually_gt_atTop 0] with x hx hx0
    exact mul_pos (rpow_pos_of_pos hx0 _) hx
  have hg : IsRegularlyVarying (fun x : ℝ => x ^ σ * f x) (σ + ρ) := by
    refine of_tendsto_mul_div_integral (a := a) hpos' hσ (h.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with x hx0
    rw [rpow_add hx0, rpow_one, mul_comm (x ^ σ) x, mul_assoc]
  have := (rpow_id (-σ)).mul hg
  rw [show -σ + (σ + ρ) = ρ by ring] at this
  refine this.congr ?_
  filter_upwards [eventually_gt_atTop 0] with x hx0
  rw [← mul_assoc, ← rpow_add hx0, neg_add_cancel, rpow_zero, one_mul]

/-- **Karamata's theorem, converse half, with weights, for tail integrals** ([BGT, Theorem 1.6.1], as
we recall it; the book was not available to check the statement): if `f` is eventually positive and,
for some `σ` with `σ + ρ < -1`, `x ^ (σ + 1) f(x) / ∫ t in Ioi x, t ^ σ f t → -(σ + ρ + 1)`, then `f`
is regularly varying with index `ρ`. -/
theorem of_tendsto_rpow_mul_div_integral_Ioi {f : ℝ → ℝ} {ρ σ : ℝ} (hpos : ∀ᶠ x in atTop, 0 < f x)
    (hσ : σ + ρ < -1)
    (h : Tendsto (fun x => x ^ (σ + 1) * f x / ∫ t in Ioi x, t ^ σ * f t) atTop
      (𝓝 (-(σ + ρ + 1)))) :
    IsRegularlyVarying f ρ := by
  have hpos' : ∀ᶠ x : ℝ in atTop, 0 < x ^ σ * f x := by
    filter_upwards [hpos, eventually_gt_atTop 0] with x hx hx0
    exact mul_pos (rpow_pos_of_pos hx0 _) hx
  have hg : IsRegularlyVarying (fun x : ℝ => x ^ σ * f x) (-(-(σ + ρ))) := by
    refine of_tendsto_mul_div_integral_Ioi_of_pos hpos' (by linarith) ?_
    rw [show -(σ + ρ) - 1 = -(σ + ρ + 1) by ring]
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx0
    rw [rpow_add hx0, rpow_one, mul_comm (x ^ σ) x, mul_assoc]
  have := (rpow_id (-σ)).mul hg
  rw [show -σ + -(-(σ + ρ)) = ρ by ring] at this
  refine this.congr ?_
  filter_upwards [eventually_gt_atTop 0] with x hx0
  rw [← mul_assoc, ← rpow_add hx0, neg_add_cancel, rpow_zero, one_mul]

/-- Karamata's converse for antitone `F`. Deprecated: `Antitone` and integrability are not needed,
only eventual positivity. Use `IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi_of_pos`. -/
@[deprecated of_tendsto_mul_div_integral_Ioi_of_pos +typeChanged (since := "2026-11-05")]
theorem of_tendsto_mul_div_integral_Ioi {F : ℝ → ℝ} {α a : ℝ} (hF : Antitone F)
    (hint : IntegrableOn F (Ioi a)) (hα : 1 < α)
    (h : Tendsto (fun x => x * F x / ∫ t in Ioi x, F t) atTop (𝓝 (α - 1))) :
    IsRegularlyVarying F (-α) := by
  -- `F` is nonnegative, since otherwise it would not be integrable on a half-line
  have hF0 : ∀ᶠ x in atTop, 0 ≤ F x := by
    filter_upwards [eventually_ge_atTop a] with x hx
    by_contra hneg
    push Not at hneg
    have hc : IntegrableOn (fun _ => F x) (Ioi x) := by
      refine Integrable.mono (hint.mono_set (Ioi_subset_Ioi hx)) aestronglyMeasurable_const
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
      have hFt : F t ≤ F x := hF (le_of_lt ht)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hneg, abs_of_neg (hFt.trans_lt hneg)]
      linarith
    rw [integrableOn_const_iff] at hc
    simp [hneg.ne] at hc
  refine of_tendsto_mul_div_integral_Ioi_of_pos ?_ hα h
  filter_upwards [hF0, h.eventually (lt_mem_nhds (by linarith : (0 : ℝ) < α - 1))] with x h0 h1
  refine lt_of_le_of_ne h0 fun h2 => ?_
  rw [← h2, mul_zero, zero_div] at h1
  exact lt_irrefl _ h1

/-- A measurable regularly varying function is positive and locally integrable near `∞`: there is
`x₀ > 0` such that `f > 0` on `[x₀, ∞)` and `f` is interval integrable between any two points of
`[x₀, ∞)`. The local bound comes from the Potter bounds, so the uniform convergence theorem is what
provides integrability ([BGT, §1.5.1]; no monotonicity is assumed). -/
theorem exists_intervalIntegrable_of_measurable {f : ℝ → ℝ} {ρ : ℝ} (hf : IsRegularlyVarying f ρ)
    (hm : Measurable f) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ (∀ x ≥ x₀, 0 < f x) ∧
      ∀ u ≥ x₀, ∀ v ≥ x₀, IntervalIntegrable f volume u v := by
  obtain ⟨x₀, hx₀, hfpos, hP⟩ := hf.potter_bound_of_measurable hm one_pos one_lt_two
  refine ⟨x₀, hx₀, hfpos, ?_⟩
  -- on `[x₀, v]`, `f` is below the continuous function given by the Potter bound
  have key : ∀ v ≥ x₀, IntervalIntegrable f volume x₀ v := by
    intro v hv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hv]
    set g : ℝ → ℝ := fun y => f x₀ * (2 * max ((y / x₀) ^ (ρ + 1)) ((y / x₀) ^ (ρ - 1))) with hg
    have hgc : ContinuousOn g (Icc x₀ v) := by
      have h0 : ∀ y ∈ Icc x₀ v, y / x₀ ≠ 0 := fun y hy =>
        (div_pos (hx₀.trans_le hy.1) hx₀).ne'
      refine continuousOn_const.mul (continuousOn_const.mul (ContinuousOn.sup ?_ ?_)) <;>
        exact (continuousOn_id.div_const x₀).rpow_const fun y hy => Or.inl (h0 y hy)
    have hgi : IntegrableOn g (Ioc x₀ v) :=
      (hgc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    refine Integrable.mono' hgi hm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => ?_)
    have hy' : x₀ ≤ y := hy.1.le
    have h := hP x₀ le_rfl y hy'
    rw [div_le_iff₀ (hfpos x₀ le_rfl)] at h
    rw [Real.norm_eq_abs, abs_of_pos (hfpos y hy'), hg]
    linarith
  exact fun u hu v hv => (key u hu).symm.trans (key v hv)

/-- **Karamata's theorem for integrals from any lower limit** (the direct half, [BGT, Proposition
1.5.8] and [BGT, Theorem 1.5.11 (i)]): if `f` is measurable, integrable on every `[a, x]`, `x ≥ a`,
and regularly varying with index `ρ > -1`, then `(∫ t in a..x, f t) / (x * f x) → 1 / (ρ + 1)` as
`x → ∞`. The lower limit `a` is arbitrary, and nothing is assumed of `f` below `a`.
`exists_tendsto_integral_interval_div` gives a form without any integrability hypothesis.

The integrability hypothesis cannot be dropped for a given `a`: if `f` is not integrable near `a`,
the Bochner integral is `0`.

After the substitution `t = x u`, the part of the integral over `[x₀, x]` becomes
`∫ u in Ioc 0 1, 1_{u > x₀ / x} f (x u) / f x`, which converges to `∫ u in 0..1, u ^ ρ` by
dominated convergence with the Potter bound `2 u ^ (ρ - δ)`, `δ = (ρ + 1) / 2`; the part over
`[a, x₀]` is negligible since `x f x → ∞`. -/
theorem tendsto_integral_interval_div {f : ℝ → ℝ} {ρ a : ℝ} (hf : IsRegularlyVarying f ρ)
    (hm : Measurable f) (hρ : -1 < ρ) (hint : ∀ x ≥ a, IntervalIntegrable f volume a x) :
    Tendsto (fun x => (∫ t in a..x, f t) / (x * f x)) atTop (𝓝 (1 / (ρ + 1))) := by
  set δ := (ρ + 1) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  have hexp : -1 < ρ - δ := by rw [hδ_def]; linarith
  obtain ⟨x₁, hx₁, hfpos₁, hP₁⟩ := hf.potter_bound_of_measurable hm hδ one_lt_two
  set x₀ := max x₁ a with hx₀_def
  have hx₁₀ : x₁ ≤ x₀ := le_max_left _ _
  have hax₀ : a ≤ x₀ := le_max_right _ _
  have hx₀ : 0 < x₀ := hx₁.trans_le hx₁₀
  have hfpos : ∀ x ≥ x₀, 0 < f x := fun x hx => hfpos₁ x (hx₁₀.trans hx)
  have hP : ∀ x ≥ x₀, ∀ y ≥ x₀, f y / f x ≤ 2 * max ((y / x) ^ (ρ + δ)) ((y / x) ^ (ρ - δ)) :=
    fun x hx y hy => hP₁ x (hx₁₀.trans hx) y (hx₁₀.trans hy)
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
  -- the part over `[a, x₀]` is negligible
  have hconst : Tendsto (fun x => (∫ t in a..x₀, f t) / (x * f x)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hxf).const_mul (∫ t in a..x₀, f t)
    rw [mul_zero] at this
    exact this.congr fun x => (div_eq_mul_inv _ _).symm
  have := hconst.add hmain
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop x₀] with x hx
  have hx0 : 0 < x := hx₀.trans_le hx
  have hfx := hfpos x hx
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint x₀ hax₀)
    ((hint x₀ hax₀).symm.trans (hint x (hax₀.trans hx)))
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

/-- **Karamata's theorem, direct half, with no integrability hypothesis** (compare
[BGT, Proposition 1.5.8]): if `f` is measurable and regularly varying with index `ρ > -1`, then for
every large enough `a`, `f` is integrable on every `[a, x]`, `x ≥ a`, and
`(∫ t in a..x, f t) / (x * f x) → 1 / (ρ + 1)`. -/
theorem exists_tendsto_integral_interval_div {f : ℝ → ℝ} {ρ : ℝ} (hf : IsRegularlyVarying f ρ)
    (hm : Measurable f) (hρ : -1 < ρ) :
    ∀ᶠ a in atTop, (∀ x ≥ a, IntervalIntegrable f volume a x) ∧
      Tendsto (fun x => (∫ t in a..x, f t) / (x * f x)) atTop (𝓝 (1 / (ρ + 1))) := by
  obtain ⟨x₀, -, -, hi⟩ := hf.exists_intervalIntegrable_of_measurable hm
  filter_upwards [eventually_ge_atTop x₀] with a ha
  have hint : ∀ x ≥ a, IntervalIntegrable f volume a x := fun x hx => hi a ha x (ha.trans hx)
  exact ⟨hint, hf.tendsto_integral_interval_div hm hρ hint⟩

/-- Karamata's theorem for integrals over `[0, x]`. Deprecated: the hypothesis asks for integrability
on `[x, 0]` for negative `x` too, which says nothing about the conclusion. Use
`IsRegularlyVarying.tendsto_integral_interval_div` with `a = 0`. -/
@[deprecated tendsto_integral_interval_div +typeChanged (since := "2026-11-05")]
theorem tendsto_integral_zero_div {f : ℝ → ℝ} {ρ : ℝ} (hf : IsRegularlyVarying f ρ)
    (hm : Measurable f) (hρ : -1 < ρ) (hint : ∀ x, IntervalIntegrable f volume 0 x) :
    Tendsto (fun x => (∫ t in (0 : ℝ)..x, f t) / (x * f x)) atTop (𝓝 (1 / (ρ + 1))) :=
  hf.tendsto_integral_interval_div hm hρ fun x _ => hint x

/-- **Karamata's theorem** for tail integrals, measurable version ([BGT, Proposition 1.5.10]): if
`F` is measurable and regularly varying with index `-α`, `α > 1` (no monotonicity is assumed),
then `(∫ t in Ioi x, F t) / (x * F x) → 1 / (α - 1)` as `x → ∞`. Compare
`IsRegularlyVarying.tendsto_integral_Ioi_div` (for antitone `F`), of which this is a
generalization. -/
theorem tendsto_integral_Ioi_div_of_measurable {F : ℝ → ℝ} {α : ℝ} (hm : Measurable F)
    (hRV : IsRegularlyVarying F (-α)) (hα : 1 < α) :
    Tendsto (fun x => (∫ t in Ioi x, F t) / (x * F x)) atTop (𝓝 (1 / (α - 1))) := by
  set δ := (α - 1) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  have hexp : -α + δ < -1 := by rw [hδ_def]; linarith
  obtain ⟨x₀, hx₀, hFpos, hP⟩ := hRV.potter_bound_of_measurable hm hδ one_lt_two
  -- Change of variables `t = x * u`.
  have hsub : ∀ᶠ x in atTop,
      ∫ u in Ioi (1 : ℝ), F (x * u) / F x = (∫ t in Ioi x, F t) / (x * F x) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [integral_div, integral_comp_mul_left_Ioi F 1 hx, mul_one, smul_eq_mul, inv_mul_eq_div,
      div_div]
  have hlim : ∫ u in Ioi (1 : ℝ), u ^ (-α) = 1 / (α - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, one_rpow]
    rw [show -α + 1 = -(α - 1) by ring, neg_div_neg_eq]
  rw [← hlim]
  refine Tendsto.congr' hsub ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun u => 2 * u ^ (-α + δ)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x =>
      ((hm.comp (measurable_id.const_mul x)).div_const _).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop x₀] with x hx
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu : 1 < u := hu
    have hx0 : 0 < x := hx₀.trans_le hx
    have hxu : x₀ ≤ x * u := by nlinarith
    have h := hP x hx (x * u) hxu
    rw [mul_div_cancel_left₀ u hx0.ne',
      max_eq_left (rpow_le_rpow_of_exponent_le hu.le (by linarith))] at h
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (hFpos _ hxu) (hFpos _ hx))]
    exact h
  · exact (integrableOn_Ioi_rpow_of_lt hexp one_pos).const_mul 2
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu : (0 : ℝ) < u := zero_lt_one.trans hu
    exact (hRV.2 u hu).congr fun x => by rw [mul_comm]

/-- **Karamata's theorem** for tail integrals of eventually antitone functions: if `F` is antitone
on some `[a, ∞)` and regularly varying with index `-α`, `α > 1`, then
`(∫ t in Ioi x, F t) / (x * F x) → 1 / (α - 1)` as `x → ∞`. -/
theorem tendsto_integral_Ioi_div_of_antitoneOn {F : ℝ → ℝ} {α a : ℝ} (hF : AntitoneOn F (Ici a))
    (hRV : IsRegularlyVarying F (-α)) (hα : 1 < α) :
    Tendsto (fun x => (∫ t in Ioi x, F t) / (x * F x)) atTop (𝓝 (1 / (α - 1))) := by
  set G : ℝ → ℝ := fun t => F (max t a) with hG
  have hGa : Antitone G := fun s t hst =>
    hF (mem_Ici.2 (le_max_right s a)) (mem_Ici.2 (le_max_right t a)) (max_le_max hst le_rfl)
  have hFG : F =ᶠ[atTop] G := by
    filter_upwards [eventually_ge_atTop a] with x hx
    simp [hG, max_eq_left hx]
  refine (tendsto_integral_Ioi_div hGa (hRV.congr hFG) hα).congr' ?_
  filter_upwards [eventually_ge_atTop a] with x hx
  have hint : ∫ t in Ioi x, G t = ∫ t in Ioi x, F t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      simp [hG, max_eq_left (hx.trans (le_of_lt ht))]
  rw [hint]
  simp [hG, max_eq_left hx]

end IsRegularlyVarying

end ExtremeValueTheory
