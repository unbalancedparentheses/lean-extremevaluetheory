/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.UniformConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Karamata representation theorem

Following Bingham, Goldie and Teugels, *Regular Variation* (Cambridge University Press, 1987),
henceforth [BGT], we prove the **representation theorem** ([BGT, Theorem 1.3.1]): a measurable
function `L` is slowly varying if and only if it can be written as
`L x = c x * exp (∫ t in a..x, ε t / t)` for `x ≥ a`, where `c x → c₀ ∈ (0, ∞)` and `ε x → 0`.
The direction (⇒) rests on the uniform convergence theorem for measurable slowly varying
functions ([BGT, Theorem 1.2.1], `IsSlowlyVarying.tendstoUniformlyOn_of_measurable`); the
general Potter bounds ([BGT, Theorem 1.5.6]) are in
`ExtremeValueTheory.RegularVariation.UniformConvergence`.

## Main results

* `ExtremeValueTheory.IsSlowlyVarying.of_representation`: (⇐), for arbitrary (not necessarily
  measurable) `L`, `c`, `ε`.
* `ExtremeValueTheory.IsSlowlyVarying.exists_representation`: (⇒), for measurable `L`.
* `ExtremeValueTheory.isSlowlyVarying_iff_exists_representation`: [BGT, Theorem 1.3.1].

## Proof of (⇒)

Write `ℓ = log ∘ L` and `g t = ℓ t / t`. By the uniform convergence theorem,
`ℓ t - ℓ x → 0` uniformly for `t ∈ [x, e x]`; in particular `ℓ` is locally bounded on some
`[a, ∞)`, so `g` is locally integrable there. With `ε t = ℓ (e t) - ℓ t` (for `t ≥ a`) the
substitution `t ↦ e t` gives
`∫ t in a..x, ε t / t = ∫ t in x..e x, g t - ∫ t in a..e a, g t`, and since
`∫ t in x..e x, t⁻¹ = 1`, we get `ℓ x - ∫ t in x..e x, g t = ∫ t in x..e x, (ℓ x - ℓ t) / t → 0`.
Hence `c x = L x * exp (-∫ t in a..x, ε t / t) → exp (∫ t in a..e a, g t)`.
-/

open Filter Topology Set Real MeasureTheory intervalIntegral

namespace ExtremeValueTheory

variable {L : ℝ → ℝ}

private lemma intervalIntegrable_inv_of_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (fun t : ℝ => t⁻¹) volume u v :=
  intervalIntegrable_inv (fun _ ht => ((lt_min hu hv).trans_le ht.1).ne') continuousOn_id

/-- `|∫ t in x..y, ε t / t| ≤ η * |log (y / x)|` if `|ε| ≤ η` on `[min x y, ∞)`. -/
private lemma abs_integral_div_le {ε : ℝ → ℝ} {η x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hε : ∀ t, min x y ≤ t → |ε t| ≤ η) :
    |∫ t in x..y, ε t / t| ≤ η * |log (y / x)| := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hε (min x y) le_rfl)
  have h := norm_integral_le_abs_of_norm_le (μ := volume) (f := fun t => ε t / t)
    (g := fun t => η * t⁻¹) ?_ ((intervalIntegrable_inv_of_pos hx hy).const_mul η)
  · rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hx hy, abs_mul,
      abs_of_nonneg hη] at h
    exact h
  · refine (ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun t ht => ?_)
    have ht' : min x y ≤ t := by
      rw [uIoc] at ht
      exact ht.1.le
    have ht0 : 0 < t := (lt_min hx hy).trans_le ht'
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hε t ht') (inv_nonneg.2 ht0.le)

/-- **Representation theorem**, direction (⇐) ([BGT, Theorem 1.3.1]): if
`L x = c x * exp (∫ t in a..x, ε t / t)` for `x ≥ a`, where `c x → c₀ > 0`, `ε x → 0` and the
integrals exist, then `L` is slowly varying. -/
theorem IsSlowlyVarying.of_representation {c ε : ℝ → ℝ} {a c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hε : Tendsto ε atTop (𝓝 0))
    (hint : ∀ x ≥ a, IntervalIntegrable (fun t => ε t / t) volume a x)
    (hL : ∀ x ≥ a, L x = c x * exp (∫ t in a..x, ε t / t)) : IsSlowlyVarying L := by
  have hcpos : ∀ᶠ x in atTop, 0 < c x := hc.eventually (lt_mem_nhds hc₀)
  refine ⟨?_, fun l hl => ?_⟩
  · filter_upwards [hcpos, eventually_ge_atTop a] with x hx hxa
    rw [hL x hxa]
    exact mul_pos hx (exp_pos _)
  set F : ℝ → ℝ := fun y => ∫ t in a..y, ε t / t with hF
  have hlx : Tendsto (fun x => l * x) atTop atTop := tendsto_id.const_mul_atTop hl
  -- the integral over `[x, l x]` tends to `0`
  have hFl : Tendsto (fun x => F (l * x) - F x) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set η' := η / (|log l| + 1) with hη'
    have hη'0 : 0 < η' := by positivity
    have hεη : ∀ᶠ t in atTop, |ε t| ≤ η' := by
      have := Metric.tendsto_nhds.1 hε η' hη'0
      filter_upwards [this] with t ht
      rw [Real.dist_eq, sub_zero] at ht
      exact ht.le
    obtain ⟨T, hT⟩ := eventually_atTop.1 hεη
    filter_upwards [eventually_ge_atTop (max (max T a) 1), hlx.eventually
      (eventually_ge_atTop (max (max T a) 1))] with x hx hlx'
    have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
    have hlx0 : 0 < l * x := mul_pos hl hx0
    have hxa : a ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
    have hlxa : a ≤ l * x := (le_max_right _ _).trans ((le_max_left _ _).trans hlx')
    have hsub : F (l * x) - F x = ∫ t in x..l * x, ε t / t :=
      integral_interval_sub_left (hint _ hlxa) (hint _ hxa)
    have hb := abs_integral_div_le (ε := ε) (η := η') hx0 hlx0 fun t ht => hT t (by
      have : T ≤ min x (l * x) := le_min ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
        ((le_max_left _ _).trans ((le_max_left _ _).trans hlx'))
      linarith)
    rw [mul_div_assoc, div_self hx0.ne', mul_one] at hb
    rw [Real.dist_eq, sub_zero, hsub]
    calc |∫ t in x..l * x, ε t / t| ≤ η' * |log l| := hb
      _ < η' * (|log l| + 1) := by gcongr; linarith
      _ = η := by rw [hη']; field_simp
  have hlim : Tendsto (fun x => c (l * x) / c x * exp (F (l * x) - F x)) atTop
      (𝓝 (c₀ / c₀ * exp 0)) :=
    ((hc.comp hlx).div hc hc₀.ne').mul ((continuous_exp.tendsto 0).comp hFl)
  rw [div_self hc₀.ne', exp_zero, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hcpos, eventually_ge_atTop a, hlx.eventually (eventually_ge_atTop a)]
    with x hx hxa hlxa
  rw [hL x hxa, hL _ hlxa, exp_sub]
  have := exp_pos (F x)
  simp only [hF] at this ⊢
  field_simp

/-- The local boundedness and local uniformity of `log ∘ L` coming from the uniform convergence
theorem. -/
private lemma eventually_abs_log_sub_lt (hL : IsSlowlyVarying L) (hm : Measurable L) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ x in atTop, ∀ t ∈ Icc x (exp 1 * x), |log (L t) - log (L x)| < η := by
  set g : ℝ → ℝ := fun t => log (L (exp t)) - 0 * t with hg
  have hgm : Measurable g :=
    (measurable_log.comp (hm.comp measurable_exp)).sub (measurable_const.mul measurable_id)
  have hU := Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_sub_of_measurable hgm
    (hL.isRegularlyVarying.tendsto_log_comp_exp_sub) (isCompact_Icc (a := 0) (b := 1))) η hη
  filter_upwards [tendsto_log_atTop.eventually hU, eventually_gt_atTop 0] with x hx hx0 t ht
  have ht0 : 0 < t := hx0.trans_le ht.1
  have h1 : log x ≤ log t := log_le_log hx0 ht.1
  have h2 : log t ≤ 1 + log x := by
    have := log_le_log ht0 ht.2
    rwa [log_mul (exp_pos 1).ne' hx0.ne', log_exp] at this
  have := hx (log t - log x) ⟨by linarith, by linarith⟩
  rw [dist_comm, Real.dist_eq, sub_zero, add_sub_cancel, hg] at this
  simpa [exp_log ht0, exp_log hx0] using this

/-- **Representation theorem**, direction (⇒) ([BGT, Theorem 1.3.1]): a measurable slowly
varying function `L` can be written as `L x = c x * exp (∫ t in a..x, ε t / t)` for `x ≥ a`,
with `a > 0`, `c` and `ε` measurable, `c x → c₀ ∈ (0, ∞)` and `ε x → 0`. -/
theorem IsSlowlyVarying.exists_representation (hL : IsSlowlyVarying L) (hm : Measurable L) :
    ∃ a : ℝ, 0 < a ∧ ∃ c ε : ℝ → ℝ, Measurable c ∧ Measurable ε ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ Tendsto c atTop (𝓝 c₀)) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ x ≥ a, IntervalIntegrable (fun t => ε t / t) volume a x) ∧
      ∀ x ≥ a, L x = c x * exp (∫ t in a..x, ε t / t) := by
  set ℓ : ℝ → ℝ := fun t => log (L t) with hℓ
  set e : ℝ := exp 1 with he
  have he1 : 1 ≤ e := one_le_exp zero_le_one
  have he0 : 0 < e := exp_pos 1
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.1 ((eventually_abs_log_sub_lt hL hm one_pos).and hL.1)
  set a := max a₀ 1 with ha_def
  have ha : 0 < a := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hpos : ∀ x ≥ a, 0 < L x := fun x hx => (ha₀ x ((le_max_left _ _).trans hx)).2
  have hloc : ∀ x ≥ a, ∀ t ∈ Icc x (e * x), |ℓ t - ℓ x| < 1 :=
    fun x hx => (ha₀ x ((le_max_left _ _).trans hx)).1
  -- local boundedness of `ℓ` on `[a, ∞)`
  have hbd : ∀ n : ℕ, ∀ t ∈ Icc a (exp n * a), |ℓ t - ℓ a| ≤ n := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have : t = a := le_antisymm (by simpa using ht.2) ht.1
      simp [this]
    | succ n ih =>
      intro t ht
      push_cast at ht ⊢
      rcases le_or_gt t (e * a) with hta | hta
      · have := hloc a le_rfl t ⟨ht.1, hta⟩
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      · have hs1 : a ≤ t / e := by rw [le_div_iff₀ he0]; linarith
        have hs2 : t / e ≤ exp n * a := by
          rw [div_le_iff₀ he0]
          have := ht.2
          rw [exp_add] at this
          linarith
        have h1 := ih (t / e) ⟨hs1, hs2⟩
        have h2 := hloc (t / e) hs1 t ⟨div_le_self (ha.trans_le ht.1).le he1,
          by rw [mul_div_cancel₀ t he0.ne']⟩
        have := abs_sub_le (ℓ t) (ℓ (t / e)) (ℓ a)
        linarith
  have hbd' : ∀ X, ∃ B, 0 ≤ B ∧ ∀ t ∈ Icc a X, |ℓ t| ≤ B := by
    intro X
    obtain ⟨n, hn⟩ := exists_nat_ge (X / a)
    refine ⟨|ℓ a| + n, by positivity, fun t ht => ?_⟩
    have hX : X ≤ exp n * a := by
      rw [div_le_iff₀ ha] at hn
      have := add_one_le_exp (n : ℝ)
      nlinarith
    have := hbd n t ⟨ht.1, ht.2.trans hX⟩
    have := abs_sub_abs_le_abs_sub (ℓ t) (ℓ a)
    linarith
  -- local integrability of `g₁ t = ℓ t / t` on `[a, ∞)`
  set g₁ : ℝ → ℝ := fun t => ℓ t / t with hg₁
  have hg₁m : Measurable g₁ := (measurable_log.comp hm).div measurable_id
  have hg₁a : ∀ v ≥ a, IntervalIntegrable g₁ volume a v := by
    intro v hv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hv]
    obtain ⟨B, hB0, hB⟩ := hbd' v
    refine Measure.integrableOn_of_bounded (M := B / a) measure_Ioc_lt_top.ne
      hg₁m.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).2
        (ae_of_all _ fun t ht => ?_))
    have ht0 : 0 < t := ha.trans ht.1
    rw [Real.norm_eq_abs, hg₁, abs_div, abs_of_pos ht0]
    exact div_le_div₀ hB0 (hB t ⟨ht.1.le, ht.2⟩) ha ht.1.le
  have hg₁int : ∀ u v, a ≤ u → a ≤ v → IntervalIntegrable g₁ volume u v :=
    fun u v hu hv => (hg₁a u hu).symm.trans (hg₁a v hv)
  -- the function `ε`
  set ε : ℝ → ℝ := fun t => if a ≤ t then ℓ (e * t) - ℓ t else 0 with hε_def
  have hεm : Measurable ε :=
    Measurable.ite measurableSet_Ici
      ((measurable_log.comp (hm.comp (measurable_const_mul e))).sub (measurable_log.comp hm))
      measurable_const
  have hεbdd : ∀ t, ‖ε t / t‖ ≤ 1 / a := by
    intro t
    by_cases ht : a ≤ t
    · have ht0 : 0 < t := ha.trans_le ht
      have h1 := hloc t ht (e * t) ⟨le_mul_of_one_le_left ht0.le he1, le_rfl⟩
      simp only [hε_def, ht, ↓reduceIte]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
      exact div_le_div₀ zero_le_one h1.le ha ht
    · simp only [hε_def, ht, ↓reduceIte, zero_div, norm_zero]
      positivity
  have hεt_m : Measurable fun t => ε t / t := hεm.div measurable_id
  have hεt_int : ∀ u v, IntervalIntegrable (fun t => ε t / t) volume u v := fun u v =>
    ⟨Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hεt_m.aestronglyMeasurable
      (ae_of_all _ hεbdd),
     Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hεt_m.aestronglyMeasurable
      (ae_of_all _ hεbdd)⟩
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := ((hL.2 e he0).log one_ne_zero)
    rw [log_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop a] with t ht
    have ht0 : 0 < t := ha.trans_le ht
    simp only [hε_def, ht, ↓reduceIte, hℓ]
    rw [log_div (hpos _ (ht.trans (le_mul_of_one_le_left ht0.le he1))).ne' (hpos t ht).ne']
  -- the key identity
  have hId : ∀ x ≥ a, ∫ t in a..x, ε t / t = (∫ t in x..e * x, g₁ t) - ∫ t in a..e * a, g₁ t := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx
    have hea : a ≤ e * a := le_mul_of_one_le_left ha.le he1
    have hex : a ≤ e * x := hx.trans (le_mul_of_one_le_left hx0.le he1)
    have h1 : ∫ t in a..x, (ε t / t + g₁ t) = ∫ t in a..x, e * g₁ (e * t) := by
      refine integral_congr fun t ht => ?_
      have ht' : a ≤ t := by
        rw [uIcc_of_le hx] at ht
        exact ht.1
      have ht0 : 0 < t := ha.trans_le ht'
      simp only [hε_def, ht', ↓reduceIte, hg₁]
      field_simp
      ring
    rw [integral_add (hεt_int a x) (hg₁a x hx), intervalIntegral.integral_const_mul,
      ← smul_eq_mul, smul_integral_comp_mul_left] at h1
    have h2 := integral_add_adjacent_intervals (hg₁int a (e * a) le_rfl hea)
      (hg₁int (e * a) (e * x) hea hex)
    have h3 := integral_add_adjacent_intervals (hg₁int a x le_rfl hx)
      (hg₁int x (e * x) hx hex)
    linarith
  -- `ℓ x - ∫ t in x..e x, g₁ t → 0`
  have hD : Tendsto (fun x => ℓ x - ∫ t in x..e * x, g₁ t) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [eventually_abs_log_sub_lt hL hm (half_pos hη), eventually_ge_atTop a]
      with x hx hxa
    have hx0 : 0 < x := ha.trans_le hxa
    have hex0 : 0 < e * x := mul_pos he0 hx0
    have hxex : x ≤ e * x := le_mul_of_one_le_left hx0.le he1
    have hinv := intervalIntegrable_inv_of_pos hx0 hex0
    have h1 : ∫ t in x..e * x, (g₁ t - ℓ x * t⁻¹) = (∫ t in x..e * x, g₁ t) - ℓ x := by
      rw [integral_sub (hg₁int x (e * x) hxa (hxa.trans hxex)) (hinv.const_mul _),
        intervalIntegral.integral_const_mul, integral_inv_of_pos hx0 hex0,
        mul_div_assoc, div_self hx0.ne', mul_one, he, log_exp, mul_one]
    have h2 : ‖∫ t in x..e * x, (g₁ t - ℓ x * t⁻¹)‖ ≤ ∫ t in x..e * x, η / 2 * t⁻¹ := by
      refine norm_integral_le_of_norm_le hxex (ae_of_all _ fun t ht => ?_) (hinv.const_mul _)
      have ht0 : 0 < t := hx0.trans ht.1
      have := hx t ⟨ht.1.le, ht.2⟩
      rw [hg₁, show ℓ t / t - ℓ x * t⁻¹ = (ℓ t - ℓ x) * t⁻¹ by ring, Real.norm_eq_abs,
        abs_mul, abs_of_pos (inv_pos.2 ht0)]
      exact mul_le_mul_of_nonneg_right this.le (inv_pos.2 ht0).le
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hx0 hex0, mul_div_assoc,
      div_self hx0.ne', mul_one, he, log_exp, mul_one, h1, Real.norm_eq_abs] at h2
    rw [Real.dist_eq, sub_zero, abs_sub_comm]
    linarith
  -- the function `c`
  have hcont : Continuous fun x => ∫ t in a..x, ε t / t := continuous_primitive hεt_int a
  refine ⟨a, ha, fun x => L x * exp (-∫ t in a..x, ε t / t), ε,
    hm.mul (continuous_exp.comp hcont.neg).measurable, hεm,
    ⟨exp (∫ t in a..e * a, g₁ t), exp_pos _, ?_⟩, hεlim, fun x _ => hεt_int a x, fun x _ => ?_⟩
  · have h := (continuous_exp.tendsto _).comp (hD.add_const (∫ t in a..e * a, g₁ t))
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop a] with x hx
    simp only [Function.comp]
    rw [hId x hx, ← exp_log (hpos x hx), ← exp_add]
    simp only [hℓ]
    congr 1
    ring
  · rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]

/-- **Karamata representation theorem** ([BGT, Theorem 1.3.1]): a measurable function `L` is
slowly varying if and only if there are `a > 0` and measurable functions `c`, `ε` with
`c x → c₀ ∈ (0, ∞)`, `ε x → 0` and `L x = c x * exp (∫ t in a..x, ε t / t)` for all `x ≥ a`. -/
theorem isSlowlyVarying_iff_exists_representation (hm : Measurable L) :
    IsSlowlyVarying L ↔ ∃ a : ℝ, 0 < a ∧ ∃ c ε : ℝ → ℝ, Measurable c ∧ Measurable ε ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ Tendsto c atTop (𝓝 c₀)) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ x ≥ a, IntervalIntegrable (fun t => ε t / t) volume a x) ∧
      ∀ x ≥ a, L x = c x * exp (∫ t in a..x, ε t / t) := by
  refine ⟨fun hL => hL.exists_representation hm, ?_⟩
  rintro ⟨a, -, c, ε, -, -, ⟨c₀, hc₀, hc⟩, hε, hint, hrep⟩
  exact IsSlowlyVarying.of_representation hc₀ hc hε hint hrep

end ExtremeValueTheory
