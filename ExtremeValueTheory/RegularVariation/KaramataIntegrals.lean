/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.KaramataConverse
import ExtremeValueTheory.RegularVariation.UniformConvergenceTails

/-!
# Karamata's theorem without monotonicity: the index `-1`, and integrals are regularly varying

The direct half of Karamata's theorem for functions that are only measurable near `∞`, including
the boundary index `ρ = -1`, following Bingham, Goldie and Teugels, *Regular Variation* (Cambridge
University Press, 1987), henceforth [BGT]. Citations to [BGT] other than those already in
`KaramataConverse.lean` are as given in the comparison `docs/HIRATA_COMPARISON.md`.

## Main results

* `IsRegularlyVarying.tendsto_integral_mul_mul_div`: for all `p, q > 0`,
  `(∫ t in p x..q x, f t) / (x f x) → ∫ u in p..q, u ^ ρ`. Everything below rests on this.
* `IsRegularlyVarying.tendsto_integral_div_of_measurableNearTop`,
  `IsRegularlyVarying.tendsto_integral_Ioi_div_of_measurableNearTop`: [BGT, Propositions 1.5.8 and
  1.5.10] for `f` measurable near `∞`.
* `IsRegularlyVarying.exists_integrableOn_Ioi_of_measurableNearTop`: for `ρ < -1`, `f` is integrable
  on a half-line.
* `IsRegularlyVarying.tendsto_integral_div_atTop_of_neg_one`: `ρ = -1`, `∫_a^x f / (x f x) → ∞`
  ([BGT, Proposition 1.5.9a]), for `f ≥ 0` on `[a, ∞)`.
* `IsRegularlyVarying.tendsto_integral_Ioi_div_atTop_of_neg_one`: `ρ = -1`,
  `∫_x^∞ f / (x f x) → ∞` when `f` is integrable on a half-line ([BGT, Proposition 1.5.9b]).
* `IsRegularlyVarying.integral`, `IsRegularlyVarying.integral_of_neg_one`,
  `IsRegularlyVarying.integral_Ioi_of_measurableNearTop`, `IsRegularlyVarying.integral_Ioi_of_neg_one`: integrals of
  regularly varying functions are regularly varying.
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

/-- A measurable factor preserves measurability near `∞`. -/
theorem MeasurableNearTop.measurable_mul {f φ : ℝ → ℝ} (hm : MeasurableNearTop f)
    (hφ : Measurable φ) : MeasurableNearTop fun x => φ x * f x := by
  obtain ⟨X, hX⟩ := hm
  refine ⟨X, ?_⟩
  have : (Ici X).indicator (fun x => φ x * f x) = fun x => φ x * (Ici X).indicator f x := by
    funext x
    by_cases hx : x ∈ Ici X <;> simp [hx]
  rw [this]
  exact hφ.mul hX

namespace IsRegularlyVarying

variable {f : ℝ → ℝ} {ρ : ℝ}

/-- **The integral over `[p x, q x]`**: if `f` is measurable near `∞` and regularly varying with
index `ρ`, then `(∫ t in p x..q x, f t) / (x f x) → ∫ u in p..q, u ^ ρ` for all `p, q > 0`. This is
the uniform convergence theorem after the substitution `t = x u`. -/
theorem tendsto_integral_mul_mul_div (hf : IsRegularlyVarying f ρ) (hm : MeasurableNearTop f)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun x => (∫ t in p * x..q * x, f t) / (x * f x)) atTop (𝓝 (∫ u in p..q, u ^ ρ)) := by
  obtain ⟨X, hX⟩ := id hm
  set g : ℝ → ℝ := (Ici X).indicator f with hg
  have hgrv : IsRegularlyVarying g ρ := hf.indicator_Ici X
  have hmin : 0 < min p q := lt_min hp hq
  have hsub : uIcc p q ⊆ Ioi 0 := fun u hu => hmin.trans_le hu.1
  have hU := Metric.tendstoUniformlyOn_iff.1
    (hgrv.tendstoUniformlyOn_of_measurable hX isCompact_uIcc hsub)
  have hmain : Tendsto (fun x => ∫ u in p..q, g (x * u) / g x) atTop (𝓝 (∫ u in p..q, u ^ ρ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun u => u ^ ρ + 1) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        ((hX.comp (measurable_const_mul x)).div_const _).aestronglyMeasurable
    · filter_upwards [hU 1 one_pos] with x hx
      refine ae_of_all _ fun u hu => ?_
      have hu' : u ∈ uIcc p q := uIoc_subset_uIcc hu
      have h := hx u hu'
      have hu0 : 0 < u ^ ρ := rpow_pos_of_pos (hsub hu') _
      rw [Real.dist_eq, abs_lt] at h
      rw [mul_comm x u, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    · refine ContinuousOn.intervalIntegrable ?_
      exact (continuousOn_id.rpow_const fun u hu => Or.inl (hsub hu).ne').add continuousOn_const
    · refine ae_of_all _ fun u hu => ?_
      exact (hgrv.2 u (hsub (uIoc_subset_uIcc hu))).congr fun x => by rw [mul_comm]
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop X, eventually_ge_atTop (X / min p q)]
    with x hx0 hxX hxm
  have hXmin : X ≤ min p q * x := by
    rw [div_le_iff₀ hmin] at hxm
    linarith [mul_comm x (min p q)]
  have hmem : ∀ t ∈ uIcc (p * x) (q * x), X ≤ t := by
    intro t ht
    refine le_trans ?_ ht.1
    rw [← min_mul_of_nonneg _ _ hx0.le]
    exact hXmin
  have e : ∫ t in p * x..q * x, f t = ∫ t in p * x..q * x, g t :=
    intervalIntegral.integral_congr fun t ht =>
      (indicator_of_mem (mem_Ici.2 (hmem t ht)) f).symm
  have hgx : g x = f x := indicator_of_mem (mem_Ici.2 hxX) f
  rw [e, intervalIntegral.integral_div, intervalIntegral.integral_comp_mul_left g hx0.ne',
    mul_comm x p, mul_comm x q, smul_eq_mul, hgx, inv_mul_eq_div, div_div]

/-- A function measurable near `∞` and regularly varying is positive and locally integrable near
`∞`. This form uses the uniform convergence theorem, not any integrability hypothesis. -/
theorem exists_intervalIntegrable_of_measurableNearTop (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ (∀ x ≥ x₀, 0 < f x) ∧
      ∀ u ≥ x₀, ∀ v ≥ x₀, IntervalIntegrable f volume u v := by
  obtain ⟨X, hX⟩ := hm
  obtain ⟨x₁, hx₁, hpos, hi⟩ := (hf.indicator_Ici X).exists_intervalIntegrable_of_measurable hX
  set x₀ := max x₁ X with hx₀
  have h₁ : x₁ ≤ x₀ := le_max_left _ _
  have h₂ : X ≤ x₀ := le_max_right _ _
  have hg : ∀ x ≥ x₀, (Ici X).indicator f x = f x := fun x hx =>
    indicator_of_mem (mem_Ici.2 (h₂.trans hx)) f
  refine ⟨x₀, hx₁.trans_le h₁, fun x hx => ?_, fun u hu v hv => ?_⟩
  · rw [← hg x hx]
    exact hpos x (h₁.trans hx)
  · refine (hi u (h₁.trans hu) v (h₁.trans hv)).congr fun t ht => ?_
    exact hg t ((le_min hu hv).trans ht.1.le)

/-- **Karamata's theorem, direct half, from any lower limit** ([BGT, Proposition 1.5.8]), for `f`
measurable near `∞`: if `f` is integrable on every `[a, x]`, `x ≥ a`, and regularly varying with
index `ρ > -1`, then `(∫ t in a..x, f t) / (x * f x) → 1 / (ρ + 1)`. -/
theorem tendsto_integral_div_of_measurableNearTop {a : ℝ} (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) (hρ : -1 < ρ) (hint : ∀ x ≥ a, IntervalIntegrable f volume a x) :
    Tendsto (fun x => (∫ t in a..x, f t) / (x * f x)) atTop (𝓝 (1 / (ρ + 1))) := by
  obtain ⟨X, hX⟩ := id hm
  set g : ℝ → ℝ := (Ici X).indicator f with hg
  set b := max a X with hb
  have hab : a ≤ b := le_max_left _ _
  have hXb : X ≤ b := le_max_right _ _
  have hgf : ∀ t ≥ b, g t = f t := fun t ht => indicator_of_mem (mem_Ici.2 (hXb.trans ht)) f
  have hfi : ∀ x ≥ b, IntervalIntegrable f volume b x := fun x hx =>
    (hint b hab).symm.trans (hint x (hab.trans hx))
  have hgi : ∀ x ≥ b, IntervalIntegrable g volume b x := fun x hx =>
    (hfi x hx).congr fun t ht => by
      rw [uIoc_of_le hx] at ht
      exact (hgf t ht.1.le).symm
  have h1 := (hf.indicator_Ici X).tendsto_integral_interval_div hX hρ hgi
  -- `x f x → ∞`
  have hxf : Tendsto (fun x => x * f x) atTop atTop := by
    have hrv : IsRegularlyVarying (fun x : ℝ => x ^ (1 : ℝ) * f x) (1 + ρ) := (rpow_id 1).mul hf
    have hmv : MeasurableNearTop fun x : ℝ => x ^ (1 : ℝ) * f x :=
      hm.measurable_mul (by fun_prop)
    simpa using hrv.tendsto_atTop_of_measurableNearTop hmv (by linarith)
  have h2 : Tendsto (fun x => (∫ t in a..b, f t) / (x * f x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hxf
  have := h2.add h1
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop b] with x hx
  have e : ∫ t in b..x, g t = ∫ t in b..x, f t :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hx] at ht
      exact hgf t ht.1
  have hgx : (Ici X).indicator f x = f x := hgf x hx
  rw [e, hgx, ← add_div,
    intervalIntegral.integral_add_adjacent_intervals (hint b hab) (hfi x hx)]

/-- **Karamata's theorem, direct half, with no integrability hypothesis**, for `f` measurable near
`∞` and `ρ > -1`: for every large enough `a`, `f` is integrable on every `[a, x]`, `x ≥ a`, and
`(∫ t in a..x, f t) / (x * f x) → 1 / (ρ + 1)`. -/
theorem eventually_tendsto_integral_div_of_measurableNearTop (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) (hρ : -1 < ρ) :
    ∀ᶠ a in atTop, (∀ x ≥ a, IntervalIntegrable f volume a x) ∧
      Tendsto (fun x => (∫ t in a..x, f t) / (x * f x)) atTop (𝓝 (1 / (ρ + 1))) := by
  obtain ⟨x₀, -, -, hi⟩ := hf.exists_intervalIntegrable_of_measurableNearTop hm
  filter_upwards [eventually_ge_atTop x₀] with a ha
  have hint : ∀ x ≥ a, IntervalIntegrable f volume a x := fun x hx => hi a ha x (ha.trans hx)
  exact ⟨hint, hf.tendsto_integral_div_of_measurableNearTop hm hρ hint⟩

/-- **Karamata's theorem for tail integrals** ([BGT, Proposition 1.5.10]), for `F` measurable near
`∞`: if `F` is regularly varying with index `-α`, `α > 1`, then
`(∫ t in Ioi x, F t) / (x * F x) → 1 / (α - 1)`. -/
theorem tendsto_integral_Ioi_div_of_measurableNearTop {F : ℝ → ℝ} {α : ℝ}
    (hm : MeasurableNearTop F) (hRV : IsRegularlyVarying F (-α)) (hα : 1 < α) :
    Tendsto (fun x => (∫ t in Ioi x, F t) / (x * F x)) atTop (𝓝 (1 / (α - 1))) := by
  obtain ⟨X, hX⟩ := hm
  refine (tendsto_integral_Ioi_div_of_measurable hX (hRV.indicator_Ici X) hα).congr' ?_
  filter_upwards [eventually_ge_atTop X] with x hx
  have hg : ∀ t ≥ X, (Ici X).indicator F t = F t := fun t ht => indicator_of_mem (mem_Ici.2 ht) F
  have e : ∫ t in Ioi x, (Ici X).indicator F t = ∫ t in Ioi x, F t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => hg t (hx.trans (mem_Ioi.1 ht).le)
  rw [e, hg x hx]

/-- For `ρ < -1`, a function measurable near `∞` and regularly varying with index `ρ` is integrable
on a half-line. The conclusion of Karamata's theorem has a nonzero limit, so the integrals in it are
not junk values. -/
theorem exists_integrableOn_Ioi_of_measurableNearTop (hf : IsRegularlyVarying f ρ)
    (hm : MeasurableNearTop f) (hρ : ρ < -1) : ∃ T : ℝ, IntegrableOn f (Ioi T) := by
  have hf' : IsRegularlyVarying f (-(-ρ)) := by rwa [neg_neg]
  have h := tendsto_integral_Ioi_div_of_measurableNearTop hm hf' (by linarith : 1 < -ρ)
  have hpos : (0 : ℝ) < 1 / (-ρ - 1) := by
    apply div_pos one_pos
    linarith
  obtain ⟨T, hT⟩ := (h.eventually (lt_mem_nhds hpos)).exists
  refine ⟨T, ?_⟩
  by_contra hni
  have h0 : ∫ t in Ioi T, f t = 0 := integral_undef hni
  simp [h0] at hT

/-- `∫ u in p..q, u ^ (-1) = log (q / p)`. -/
private lemma integral_rpow_neg_one {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ u in p..q, u ^ (-1 : ℝ) = log (q / p) := by
  have : ∫ u in p..q, u ^ (-1 : ℝ) = ∫ u in p..q, u⁻¹ :=
    intervalIntegral.integral_congr fun u _ => rpow_neg_one u
  rw [this, integral_inv_of_pos hp hq]

/-- **Karamata's theorem at the index `-1`, integrals over `[a, x]`** ([BGT, Proposition 1.5.9a]):
if `f` is measurable near `∞`, regularly varying with index `-1`, nonnegative and integrable on
`[a, x]` for `x ≥ a`, then `(∫ t in a..x, f t) / (x f x) → ∞`.

The nonnegativity on all of `[a, ∞)` cannot be dropped for a given `a`: `x f x` may tend to `0`, and
then a negative value of `∫ t in a..x, f t` sends the ratio to `-∞`. In [BGT] the function is positive
by definition. -/
theorem tendsto_integral_div_atTop_of_neg_one (hf : IsRegularlyVarying f (-1))
    (hm : MeasurableNearTop f) {a : ℝ} (hnn : ∀ x ≥ a, 0 ≤ f x)
    (hint : ∀ x ≥ a, IntervalIntegrable f volume a x) :
    Tendsto (fun x => (∫ t in a..x, f t) / (x * f x)) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  set K := exp (|M| + 1) with hK
  have hK0 : 0 < K := exp_pos _
  have h := hf.tendsto_integral_mul_mul_div hm (inv_pos.2 hK0) one_pos
  rw [integral_rpow_neg_one (inv_pos.2 hK0) one_pos, div_inv_eq_mul, one_mul, hK, log_exp, ← hK] at h
  filter_upwards [h.eventually (lt_mem_nhds (show |M| < |M| + 1 by linarith)),
    eventually_ge_atTop (K * a), eventually_gt_atTop 0, hf.1] with x h1 hxa hx0 hfx
  have hbase : a ≤ K⁻¹ * x := by
    rw [inv_mul_eq_div, le_div_iff₀ hK0]
    linarith [mul_comm K a]
  have hx1 : K⁻¹ * x ≤ x := by
    have : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_exp (by positivity))
    nlinarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint _ hbase)
    ((hint _ hbase).symm.trans (hint x (hbase.trans hx1)))
  have hnonneg : 0 ≤ ∫ t in a..K⁻¹ * x, f t :=
    intervalIntegral.integral_nonneg hbase fun t ht => hnn t ht.1
  rw [one_mul] at h1
  have hxf : 0 < x * f x := mul_pos hx0 hfx
  have hle : (∫ t in K⁻¹ * x..x, f t) / (x * f x) ≤ (∫ t in a..x, f t) / (x * f x) :=
    div_le_div_of_nonneg_right (by linarith) hxf.le
  linarith [le_abs_self M]

/-- **Karamata's theorem at the index `-1`, tail integrals** ([BGT, Proposition 1.5.9b]): if `f` is
measurable near `∞`, regularly varying with index `-1` and integrable on a half-line, then
`(∫ t in Ioi x, f t) / (x f x) → ∞`. No monotonicity is assumed. Compare the antitone form
`ExtremeValueTheory.Minimality.tendsto_integral_Ioi_div_atTop_of_neg_one`.

The integrability hypothesis is needed: it can fail at index `-1`, and then the integral is `0`. -/
theorem tendsto_integral_Ioi_div_atTop_of_neg_one (hf : IsRegularlyVarying f (-1))
    (hm : MeasurableNearTop f) {a : ℝ} (hint : IntegrableOn f (Ioi a)) :
    Tendsto (fun x => (∫ t in Ioi x, f t) / (x * f x)) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  set K := exp (|M| + 1) with hK
  have hK0 : 0 < K := exp_pos _
  have hK1 : 1 ≤ K := one_le_exp (by positivity)
  have h := hf.tendsto_integral_mul_mul_div hm one_pos hK0
  rw [integral_rpow_neg_one one_pos hK0, div_one, hK, log_exp, ← hK] at h
  obtain ⟨T, hT⟩ := eventually_atTop.1 hf.1
  filter_upwards [h.eventually (lt_mem_nhds (show |M| < |M| + 1 by linarith)),
    eventually_ge_atTop a, eventually_gt_atTop 0, eventually_ge_atTop T] with x h1 hxa hx0 hxT
  have hx1 : x ≤ K * x := le_mul_of_one_le_left hx0.le hK1
  have hIx : IntegrableOn f (Ioi x) := hint.mono_set (Ioi_subset_Ioi hxa)
  have hIy : IntegrableOn f (Ioi (K * x)) := hint.mono_set (Ioi_subset_Ioi (hxa.trans hx1))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hIx hIy
  have hnonneg : 0 ≤ ∫ t in Ioi (K * x), f t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      (hT t (hxT.trans (hx1.trans (mem_Ioi.1 ht).le))).le
  rw [one_mul] at h1
  have hxf : 0 < x * f x := mul_pos hx0 (hT x hxT)
  have hle : (∫ t in x..K * x, f t) / (x * f x) ≤ (∫ t in Ioi x, f t) / (x * f x) :=
    div_le_div_of_nonneg_right (by linarith) hxf.le
  linarith [le_abs_self M]

/-- **Integrals of regularly varying functions are regularly varying, `ρ > -1`** ([BGT, Proposition
1.5.8]): if `f` is measurable near `∞`, regularly varying with index `ρ > -1`, and integrable on
every `[a, x]`, `x ≥ a`, then `x ↦ ∫ t in a..x, f t` is regularly varying with index `ρ + 1`. -/
theorem integral (hf : IsRegularlyVarying f ρ) (hm : MeasurableNearTop f) (hρ : -1 < ρ) {a : ℝ}
    (hint : ∀ x ≥ a, IntervalIntegrable f volume a x) :
    IsRegularlyVarying (fun x => ∫ t in a..x, f t) (ρ + 1) := by
  have hg : IsRegularlyVarying (fun x : ℝ => x ^ (1 : ℝ) * f x) (ρ + 1) := by
    rw [add_comm]
    exact (rpow_id 1).mul hf
  refine hg.of_tendsto_div (L := 1 / (ρ + 1)) ?_ (one_div_pos.2 (by linarith))
  simpa only [rpow_one] using hf.tendsto_integral_div_of_measurableNearTop hm hρ hint

/-- **Integrals at the index `-1` are slowly varying** ([BGT, Proposition 1.5.9a]): if `f` is
measurable near `∞`, regularly varying with index `-1`, nonnegative and integrable on `[a, x]` for
`x ≥ a`, then `x ↦ ∫ t in a..x, f t` is slowly varying. -/
theorem integral_of_neg_one (hf : IsRegularlyVarying f (-1)) (hm : MeasurableNearTop f) {a : ℝ}
    (hnn : ∀ x ≥ a, 0 ≤ f x) (hint : ∀ x ≥ a, IntervalIntegrable f volume a x) :
    IsSlowlyVarying fun x => ∫ t in a..x, f t := by
  have hJ := hf.tendsto_integral_div_atTop_of_neg_one hm hnn hint
  have hxf : ∀ᶠ x in atTop, 0 < x * f x := by
    filter_upwards [eventually_gt_atTop 0, hf.1] with x h1 h2
    exact mul_pos h1 h2
  have hpos : ∀ᶠ x in atTop, 0 < ∫ t in a..x, f t := by
    filter_upwards [hJ.eventually_gt_atTop 0, hxf] with x h1 h2
    exact (div_pos_iff_of_pos_right h2).1 h1
  refine ⟨hpos, fun c hc => ?_⟩
  have h1 := hf.tendsto_integral_mul_mul_div hm one_pos hc
  have h2 := (h1.div_atTop hJ).const_add 1
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop a, (tendsto_id.const_mul_atTop hc).eventually
    (eventually_ge_atTop a), hxf, hpos] with x hxa hcxa hxf0 hJ0
  simp only [id] at hcxa
  rw [one_mul, ← intervalIntegral.integral_add_adjacent_intervals (hint x hxa)
    ((hint x hxa).symm.trans (hint _ hcxa)), div_div_div_cancel_right₀ hxf0.ne', add_div,
    div_self hJ0.ne']

/-- **Tail integrals of regularly varying functions are regularly varying, `ρ = -α < -1`** ([BGT,
Proposition 1.5.10]): if `F` is measurable near `∞` and regularly varying with index `-α`, `α > 1`,
then `x ↦ ∫ t in Ioi x, F t` is regularly varying with index `1 - α`. -/
theorem integral_Ioi_of_measurableNearTop {F : ℝ → ℝ} {α : ℝ} (hm : MeasurableNearTop F)
    (hRV : IsRegularlyVarying F (-α)) (hα : 1 < α) :
    IsRegularlyVarying (fun x => ∫ t in Ioi x, F t) (1 - α) := by
  have hg : IsRegularlyVarying (fun x : ℝ => x ^ (1 : ℝ) * F x) (1 - α) := by
    rw [sub_eq_add_neg]
    exact (rpow_id 1).mul hRV
  refine hg.of_tendsto_div (L := 1 / (α - 1)) ?_ (one_div_pos.2 (by linarith))
  simpa only [rpow_one] using tendsto_integral_Ioi_div_of_measurableNearTop hm hRV hα

/-- **Tail integrals at the index `-1` are slowly varying** ([BGT, Proposition 1.5.9b]): if `f` is
measurable near `∞`, regularly varying with index `-1` and integrable on a half-line, then
`x ↦ ∫ t in Ioi x, f t` is slowly varying. -/
theorem integral_Ioi_of_neg_one (hf : IsRegularlyVarying f (-1)) (hm : MeasurableNearTop f) {a : ℝ}
    (hint : IntegrableOn f (Ioi a)) : IsSlowlyVarying fun x => ∫ t in Ioi x, f t := by
  have hT := hf.tendsto_integral_Ioi_div_atTop_of_neg_one hm hint
  have hxf : ∀ᶠ x in atTop, 0 < x * f x := by
    filter_upwards [eventually_gt_atTop 0, hf.1] with x h1 h2
    exact mul_pos h1 h2
  have hpos : ∀ᶠ x in atTop, 0 < ∫ t in Ioi x, f t := by
    filter_upwards [hT.eventually_gt_atTop 0, hxf] with x h1 h2
    exact (div_pos_iff_of_pos_right h2).1 h1
  refine ⟨hpos, fun c hc => ?_⟩
  have h1 := hf.tendsto_integral_mul_mul_div hm one_pos hc
  have h2 := (h1.div_atTop hT).neg.const_add 1
  rw [neg_zero, add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop a, (tendsto_id.const_mul_atTop hc).eventually
    (eventually_ge_atTop a), hxf, hpos] with x hxa hcxa hxf0 hT0
  simp only [id] at hcxa
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (hint.mono_set (Ioi_subset_Ioi hxa)) (hint.mono_set (Ioi_subset_Ioi hcxa))
  have hs : ∫ t in Ioi (c * x), f t = (∫ t in Ioi x, f t) - ∫ t in x..c * x, f t := by linarith
  rw [one_mul, hs, div_div_div_cancel_right₀ hxf0.ne', sub_div, div_self hT0.ne']
  ring

end IsRegularlyVarying

end ExtremeValueTheory
