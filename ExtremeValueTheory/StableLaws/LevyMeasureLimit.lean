/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.LevyMeasureLimit.SecondDifference

/-!
# Convergence of the Lévy measures of normalized sums

Let `X₁, X₂, …` be i.i.d. with law `μ`, `aₙ > 0`, and suppose the laws of `(Sₙ - bₙ) / aₙ`
converge weakly to `ν` whose characteristic function `φ` does not vanish. Under the a priori
bounds that `n E[min (1, (X / aₙ)²)]` is bounded, `n E[min (1, (s X / aₙ)²)]` is uniformly small
for small `s`, and `n P(|X| > 2 aₙ)` is bounded below, we show that `n P(X / aₙ ∈ ·)` converges
vaguely away from `0`: `n E[f(X / aₙ)]` converges for every bounded Lipschitz `f` vanishing near
`0` ([GK, §25], [Feller, Vol. II, §XVII.2]). This is the step of the converse of the
generalized CLT that sees the asymmetry of the law; no uniqueness of the Lévy–Khintchine
representation is needed.

## Main definitions

* `GCLTConverse.ctr μ a n = E[clip (X / aₙ)]` (truncated mean) and `GCLTConverse.cLaw μ a n`,
  the law of `X / aₙ - τₙ`; `GCLTConverse.wfun μ a n t = φ_{cLaw}(t) - 1`.
* `GCLTConverse.dfun μ a n t s = n (wₙ(t + s) + wₙ(t - s) - 2 wₙ(t))`, the second differences.
* `GCLTConverse.kern s₀ z = ∫₀^{s₀} (1 - cos (s z)) ds` and the canonical measures
  `GCLTConverse.kernMeasure s₀ (cLaw μ a n)`, normalized as `GCLTConverse.kernNorm`.

## Main results

* `GCLTConverse.norm_wfun_le`: `|wₙ(t)| ≤ (12 t² + 2 |t| + 2) E[min (1, (X / aₙ)²)]`.
* `GCLTConverse.tendsto_one_add_pow_sub_exp`: `(1 + wₙ)ⁿ - e^{n wₙ} → 0` when `n wₙ` is bounded.
* `GCLTConverse.tendsto_exp_dfun`, `GCLTConverse.tendsto_dfun_log`: the centering cancels in
  second differences, `e^{Dₙ(t, s)} → φ(t + s) φ(t - s) / φ(t)²`, and for `|Dₙ| ≤ 1` (small `s`,
  `exists_forall_norm_dfun_le`) `Dₙ(t, s) → log (φ(t + s) φ(t - s) / φ(t)²)`.
* `GCLTConverse.charFun_kernMeasure`: `φ_{k ρₙ}(t) = -∫₀^{s₀} Dₙ(t, s) ds / (2n)`.
* `GCLTConverse.exists_tendsto_mul_integral_kern`: Lévy's continuity theorem makes the
  normalized canonical measures converge: `n ∫ k g dρₙ → L₀ ∫ g dP`.
* `GCLTConverse.exists_tendsto_mul_integral_comp`: **vague convergence** of `n P(X / aₙ ∈ ·)`
  on test functions vanishing near `0` (removing the shift by `τₙ → 0`).

## File layout

* `ExtremeValueTheory.StableLaws.LevyMeasureLimit.SecondDifference`: the centered laws, the bound
  on `wₙ`, and the convergence of the second differences `Dₙ`.
* this file: the kernel `kern`, the canonical measures, and the vague limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

namespace GCLTConverse

open GCLT Subexp

section Kern

variable {s₀ : ℝ}

/-- The kernel `k(z) = ∫₀^{s₀} (1 - cos (s z)) ds = s₀ - sin (s₀ z) / z`. -/
noncomputable def kern (s₀ z : ℝ) : ℝ := ∫ s in (0 : ℝ)..s₀, (1 - Real.cos (s * z))

theorem continuous_kern : Continuous (kern s₀) := by
  unfold kern
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun z s => 1 - Real.cos (s * z)) (by fun_prop) 0 s₀

theorem kern_eq (z : ℝ) (hz : z ≠ 0) : kern s₀ z = s₀ - Real.sin (s₀ * z) / z := by
  have hi : IntervalIntegrable (fun s : ℝ => Real.cos (s * z)) volume 0 s₀ :=
    (by fun_prop : Continuous fun s : ℝ => Real.cos (s * z)).intervalIntegrable _ _
  rw [kern, intervalIntegral.integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one]
  have : ∫ s in (0 : ℝ)..s₀, Real.cos (s * z) = ∫ s in (0 : ℝ)..s₀, Real.cos (z * s) := by
    congr 1; funext s; rw [mul_comm]
  rw [this, intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) hz, integral_cos,
    mul_zero, Real.sin_zero, sub_zero, smul_eq_mul, mul_comm z s₀, inv_mul_eq_div]

theorem kern_nonneg (hs₀ : 0 ≤ s₀) (z : ℝ) : 0 ≤ kern s₀ z :=
  intervalIntegral.integral_nonneg hs₀ fun s _ => by linarith [Real.cos_le_one (s * z)]

theorem kern_le (hs₀ : 0 ≤ s₀) (z : ℝ) : kern s₀ z ≤ 2 * s₀ := by
  have h := intervalIntegral.integral_mono_on hs₀
    ((by fun_prop : Continuous fun s : ℝ => 1 - Real.cos (s * z)).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume) (c := (2 : ℝ))) fun s _ => by linarith [Real.neg_one_le_cos (s * z)]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  unfold kern; linarith

theorem kern_pos (hs₀ : 0 < s₀) {z : ℝ} (hz : z ≠ 0) : 0 < kern s₀ z := by
  rw [kern_eq z hz, sub_pos]
  rcases lt_or_gt_of_ne hz with h | h
  · rw [div_lt_iff_of_neg h]
    have := Real.sin_lt (show 0 < s₀ * -z by nlinarith)
    rw [mul_neg, Real.sin_neg] at this
    linarith
  · rw [div_lt_iff₀ h]
    exact Real.sin_lt (by positivity)

/-- `k` is bounded below away from `0`. -/
theorem exists_le_kern (hs₀ : 0 < s₀) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∃ c > 0, ∀ z, x₀ ≤ |z| → c ≤ kern s₀ z := by
  set R := max x₀ (2 / s₀)
  have hK : IsCompact {z : ℝ | x₀ ≤ |z| ∧ |z| ≤ R} := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    · refine (Metric.isBounded_Icc (-R) R).subset fun z hz => ?_
      exact abs_le.1 hz.2
  have hne : ({z : ℝ | x₀ ≤ |z| ∧ |z| ≤ R}).Nonempty :=
    ⟨x₀, by simp [abs_of_pos hx₀, R]⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne continuous_kern.continuousOn
  have hz₀0 : z₀ ≠ 0 := by
    rintro rfl; simp at hz₀; linarith [hz₀.1]
  refine ⟨min (kern s₀ z₀) (s₀ / 2), lt_min (kern_pos hs₀ hz₀0) (by positivity), fun z hz => ?_⟩
  by_cases hzR : |z| ≤ R
  · exact (min_le_left _ _).trans (hmin ⟨hz, hzR⟩)
  · refine (min_le_right _ _).trans ?_
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
    have hzR' : 2 / s₀ < |z| := lt_of_le_of_lt (le_max_right _ _) (not_le.1 hzR)
    rw [kern_eq z hz0]
    have h1 : |Real.sin (s₀ * z) / z| ≤ 1 / |z| := by
      rw [abs_div]; exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
    have h2 : 1 / |z| ≤ s₀ / 2 := by
      rw [div_le_iff₀ (abs_pos.2 hz0)]
      rw [div_lt_iff₀ hs₀] at hzR'
      linarith
    linarith [le_abs_self (Real.sin (s₀ * z) / z)]

end Kern

section KernMeasure

variable {s₀ : ℝ}

/-- `ρ` weighted by the kernel `k`. -/
noncomputable def kernMeasure (s₀ : ℝ) (ρ : Measure ℝ) : Measure ℝ :=
  ρ.withDensity fun z => ((kern s₀ z).toNNReal : ℝ≥0∞)

theorem measurable_kern_toNNReal : Measurable fun z => (kern s₀ z).toNNReal :=
  continuous_kern.measurable.real_toNNReal

instance (ρ : Measure ℝ) [IsFiniteMeasure ρ] : IsFiniteMeasure (kernMeasure s₀ ρ) := by
  refine isFiniteMeasure_withDensity ?_
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := (2 * |s₀|).toNNReal))
    (measure_ne_top ρ univ)) ?_
  calc ∫⁻ z, ((kern s₀ z).toNNReal : ℝ≥0∞) ∂ρ ≤ ∫⁻ _z, ((2 * |s₀|).toNNReal : ℝ≥0∞) ∂ρ :=
        lintegral_mono fun z => by
          refine ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal ?_)
          rcases le_total 0 s₀ with h | h
          · rw [abs_of_nonneg h]; exact kern_le h z
          · have : kern s₀ z ≤ 0 := by
              rw [kern, intervalIntegral.integral_symm]
              exact neg_nonpos.2 (intervalIntegral.integral_nonneg h fun s _ => by
                linarith [Real.cos_le_one (s * z)])
            linarith [abs_nonneg s₀]
    _ = _ := by rw [lintegral_const]

theorem integral_kernMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hs₀ : 0 ≤ s₀) (ρ : Measure ℝ) (g : ℝ → E) :
    ∫ z, g z ∂(kernMeasure s₀ ρ) = ∫ z, kern s₀ z • g z ∂ρ := by
  rw [kernMeasure, integral_withDensity_eq_integral_smul measurable_kern_toNNReal]
  congr 1; funext z
  rw [NNReal.smul_def, Real.coe_toNNReal _ (kern_nonneg hs₀ z)]

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

/-- **Characteristic function of the kernel measure**:
`φ_{k ρₙ}(t) = ∫₀^{s₀} -Dₙ(t, s) / (2n) ds`. -/
theorem charFun_kernMeasure (hs₀ : 0 ≤ s₀) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    charFun (kernMeasure s₀ (cLaw μ a n)) t =
      ∫ s in (0 : ℝ)..s₀, -dfun μ a n t s / (2 * n) := by
  set ρ := cLaw μ a n
  set F : ℝ → ℝ → ℂ := fun z s => ((1 - Real.cos (s * z) : ℝ) : ℂ) *
    Complex.exp (t * z * Complex.I)
  have hF : Continuous (Function.uncurry F) := by
    simp only [F]; fun_prop
  have hint : Integrable (Function.uncurry F) (ρ.prod (volume.restrict (Ioc 0 s₀))) := by
    refine Integrable.of_bound hF.aestronglyMeasurable 2 (ae_of_all _ fun p => ?_)
    obtain ⟨z, s⟩ := p
    simp only [Function.uncurry_apply_pair, F, norm_mul, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]; constructor <;> linarith [Real.cos_le_one (s * z), Real.neg_one_le_cos (s * z)]
  have hk : ∀ z, kern s₀ z • Complex.exp (t * z * Complex.I) = ∫ s in Ioc 0 s₀, F z s := by
    intro z
    rw [kern, intervalIntegral.integral_of_le hs₀, Complex.real_smul, ← integral_complex_ofReal,
      ← integral_mul_const]
  rw [charFun_apply_real, integral_kernMeasure hs₀]
  simp_rw [hk]
  rw [integral_integral_swap hint, intervalIntegral.integral_of_le hs₀]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [dfun_eq]
  field_simp
  ring

end KernMeasure

section LevyLimit

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ} {ν : ProbabilityMeasure ℝ}
  {s₀ : ℝ}

/-- `R(t, s) = φ(t + s) φ(t - s) / φ(t)²`. -/
noncomputable def rfun (ν : Measure ℝ) (t s : ℝ) : ℂ :=
  charFun ν (t + s) * charFun ν (t - s) / charFun ν t ^ 2

/-- The limit transform `λ(t) = ∫₀^{s₀} -log R(t, s) / 2 ds`. -/
noncomputable def lamK (ν : Measure ℝ) (s₀ t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..s₀, -Complex.log (rfun ν t s) / 2

theorem continuous_wfun (n : ℕ) : Continuous (wfun μ a n) := by
  unfold wfun; have := continuous_charFun (μ := cLaw μ a n); fun_prop

theorem continuous_dfun (n : ℕ) (t : ℝ) : Continuous (dfun μ a n t) := by
  unfold dfun; have := continuous_wfun (μ := μ) (a := a) n; fun_prop

/-- Local boundedness of `n wₙ` from the bound on `n E[min (1, (X / aₙ)²)]`. -/
theorem exists_norm_mul_wfun_le (ha : ∀ n, 0 < a n)
    (hS : ∃ C, ∀ᶠ n : ℕ in atTop, (n : ℝ) * sqRatio μ (a n) ≤ C) (t : ℝ) :
    ∃ C, ∀ᶠ n : ℕ in atTop, ‖(n : ℂ) * wfun μ a n t‖ ≤ C := by
  obtain ⟨C, hC⟩ := hS
  refine ⟨(12 * t ^ 2 + 2 * |t| + 2) * C, hC.mono fun n hn => ?_⟩
  rw [norm_mul, Complex.norm_natCast]
  calc (n : ℝ) * ‖wfun μ a n t‖ ≤ n * ((12 * t ^ 2 + 2 * |t| + 2) * sqRatio μ (a n)) :=
        mul_le_mul_of_nonneg_left (norm_wfun_le (ha n).ne' t) (Nat.cast_nonneg n)
    _ = (12 * t ^ 2 + 2 * |t| + 2) * (n * sqRatio μ (a n)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)

variable (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
  (hφ : ∀ t, charFun (ν : Measure ℝ) t ≠ 0)
  (hw : ∀ t, ∃ C, ∀ᶠ n : ℕ in atTop, ‖(n : ℂ) * wfun μ a n t‖ ≤ C)
  (hD : ∀ᶠ n : ℕ in atTop, ∀ t s, 0 ≤ s → s ≤ s₀ → ‖dfun μ a n t s‖ ≤ 1)
include hconv hφ hw hD

theorem tendsto_dfun_log' {t s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s₀) :
    Real.exp (-1) * Real.cos 1 ≤ (rfun ν t s).re ∧
      Tendsto (fun n => dfun μ a n t s) atTop (𝓝 (Complex.log (rfun ν t s))) :=
  tendsto_dfun_log hconv hφ hw (hD.mono fun _ hn => hn t s hs0 hs)

theorem norm_log_rfun_le {t s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s₀) :
    ‖Complex.log (rfun ν t s)‖ ≤ 1 :=
  le_of_tendsto (tendsto_dfun_log' hconv hφ hw hD hs0 hs).2.norm
    (hD.mono fun _ hn => hn t s hs0 hs)

/-- `n φ_{k ρₙ}(t) → λ(t)`. -/
theorem tendsto_mul_charFun_kernMeasure (hs₀ : 0 ≤ s₀) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) * charFun (kernMeasure s₀ (cLaw μ a n)) t) atTop
      (𝓝 (lamK (ν : Measure ℝ) s₀ t)) := by
  have he : ∀ᶠ n : ℕ in atTop, (n : ℂ) * charFun (kernMeasure s₀ (cLaw μ a n)) t =
      ∫ s in (0 : ℝ)..s₀, -dfun μ a n t s / 2 := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [charFun_kernMeasure hs₀ hn, ← intervalIntegral.integral_const_mul]
    congr 1; funext s; field_simp
  refine Tendsto.congr' (EventuallyEq.symm he) ?_
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1 / 2)
    (Eventually.of_forall fun n => ((continuous_dfun n t).neg.div_const 2).aestronglyMeasurable)
    ?_ intervalIntegrable_const (ae_of_all _ fun s hs => ?_)
  · filter_upwards [hD] with n hn
    refine ae_of_all _ fun s hs => ?_
    rw [Set.uIoc_of_le hs₀] at hs
    rw [norm_div, norm_neg, Complex.norm_ofNat]
    linarith [hn t s hs.1.le hs.2]
  · rw [Set.uIoc_of_le hs₀] at hs
    exact ((tendsto_dfun_log' hconv hφ hw hD hs.1.le hs.2).2.neg).div_const 2

theorem continuousAt_lamK (hs₀ : 0 ≤ s₀) : ContinuousAt (lamK (ν : Measure ℝ) s₀) 0 := by
  have hRc : ∀ s, Continuous fun t => rfun (ν : Measure ℝ) t s := by
    intro s
    have hc := continuous_charFun (μ := (ν : Measure ℝ))
    exact ((hc.comp (continuous_id.add continuous_const)).mul
      (hc.comp (continuous_id.sub continuous_const))).div (hc.pow 2)
      fun t => pow_ne_zero 2 (hφ t)
  have hRs : ∀ t, Continuous fun s => rfun (ν : Measure ℝ) t s := by
    intro t
    have hc := continuous_charFun (μ := (ν : Measure ℝ))
    exact ((hc.comp (continuous_const.add continuous_id)).mul
      (hc.comp (continuous_const.sub continuous_id))).div continuous_const
      fun _ => pow_ne_zero 2 (hφ t)
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => 1 / 2)
    (Eventually.of_forall fun t => ((Complex.measurable_log.comp (hRs t).measurable).neg.div_const
      2).aestronglyMeasurable) (Eventually.of_forall fun t => ae_of_all _ fun s hs => ?_)
    intervalIntegrable_const (ae_of_all _ fun s hs => ?_)
  · rw [Set.uIoc_of_le hs₀] at hs
    rw [norm_div, norm_neg, Complex.norm_ofNat]
    linarith [norm_log_rfun_le hconv hφ hw hD (t := t) hs.1.le hs.2]
  · rw [Set.uIoc_of_le hs₀] at hs
    have hpos : 0 < (rfun (ν : Measure ℝ) 0 s).re := lt_of_lt_of_le (mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by
        linarith [Real.pi_gt_three]⟩)) (tendsto_dfun_log' hconv hφ hw hD hs.1.le hs.2).1
    have h1 : ContinuousAt (fun t => Complex.log (rfun (ν : Measure ℝ) t s)) 0 :=
      ContinuousAt.comp (x := (0 : ℝ)) (g := Complex.log)
        (continuousAt_clog (Complex.mem_slitPlane_iff.2 (Or.inl hpos))) (hRc s).continuousAt
    exact h1.neg.div_const 2

omit hconv hφ hw hD in
omit [IsProbabilityMeasure μ] in
theorem measureReal_univ_kernMeasure (hs₀ : 0 ≤ s₀) (n : ℕ) :
    (kernMeasure s₀ (cLaw μ a n)).real univ = ∫ z, kern s₀ z ∂(cLaw μ a n) := by
  have h := integral_kernMeasure hs₀ (cLaw μ a n) (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  exact h

omit hconv hφ hw hD in
/-- The mass of the kernel measure is at least `c P(|X| > 2 aₙ)`. -/
theorem le_measureReal_univ_kernMeasure (hs₀ : 0 < s₀) {c : ℝ}
    (hc : ∀ z, 1 ≤ |z| → c ≤ kern s₀ z) {n : ℕ} (ha : 0 < a n) :
    c * absTail μ (2 * a n) ≤ (kernMeasure s₀ (cLaw μ a n)).real univ := by
  rw [measureReal_univ_kernMeasure hs₀.le, cLaw, integral_map (by fun_prop)
    continuous_kern.aestronglyMeasurable]
  have hτ := abs_ctr_le (μ := μ) (a := a) n
  calc c * absTail μ (2 * a n) = ∫ x, {y : ℝ | 2 * a n < |y|}.indicator (fun _ => c) x ∂μ := by
        rw [integral_indicator_const _ (measurableSet_abs_gt _), smul_eq_mul, mul_comm]; rfl
    _ ≤ ∫ x, kern s₀ ((a n)⁻¹ * x - ctr μ a n) ∂μ := by
        refine integral_mono ((integrable_const c).indicator (measurableSet_abs_gt _))
          (Integrable.of_bound ((continuous_kern.comp (by fun_prop : Continuous fun x : ℝ =>
            (a n)⁻¹ * x - ctr μ a n)).aestronglyMeasurable)
            (2 * s₀) (ae_of_all _ fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg hs₀.le _)]
              exact kern_le hs₀.le _)) fun x => ?_
        by_cases hx : 2 * a n < |x|
        · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | 2 * a n < |y|} from hx)]
          refine hc _ ?_
          have h1 : 2 < |(a n)⁻¹ * x| := by
            rw [abs_mul, abs_inv, abs_of_pos ha, ← div_eq_inv_mul, lt_div_iff₀ ha]
            linarith
          have := abs_sub_abs_le_abs_sub ((a n)⁻¹ * x) (ctr μ a n)
          linarith
        · rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | 2 * a n < |y|} from hx)]
          exact kern_nonneg hs₀.le _

/-- The normalized kernel measures `k ρₙ / (k ρₙ)(ℝ)`. -/
noncomputable def kernNorm (s₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℕ → ℝ)
    (n : ℕ) : ProbabilityMeasure ℝ :=
  FiniteMeasure.normalize ⟨kernMeasure s₀ (cLaw μ a n), inferInstance⟩

omit hconv hφ hw hD in
theorem kernNorm_eq {n : ℕ} (h0 : 0 < (kernMeasure s₀ (cLaw μ a n)).real univ) :
    (kernNorm s₀ μ a n : Measure ℝ) =
      ((kernMeasure s₀ (cLaw μ a n)).real univ).toNNReal⁻¹ • kernMeasure s₀ (cLaw μ a n) := by
  set Λ : FiniteMeasure ℝ := ⟨kernMeasure s₀ (cLaw μ a n), inferInstance⟩
  have hmass : (Λ.mass : ℝ) = (kernMeasure s₀ (cLaw μ a n)).real univ := by
    rw [measureReal_def, ← ENNReal.coe_toReal, FiniteMeasure.ennreal_mass]
    rfl
  have hne : Λ ≠ 0 := by
    refine (FiniteMeasure.mass_nonzero_iff _).1 fun hz => ?_
    rw [hz] at hmass
    simp only [NNReal.coe_zero] at hmass
    linarith
  rw [kernNorm, FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hne]
  congr 2
  rw [← hmass, Real.toNNReal_coe]

omit hconv hφ hw hD in
theorem integral_kernNorm {n : ℕ} (h0 : 0 < (kernMeasure s₀ (cLaw μ a n)).real univ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ z, g z ∂(kernNorm s₀ μ a n : Measure ℝ) =
      ((kernMeasure s₀ (cLaw μ a n)).real univ)⁻¹ • ∫ z, g z ∂(kernMeasure s₀ (cLaw μ a n)) := by
  rw [kernNorm_eq h0, integral_smul_nnreal_measure, NNReal.smul_def]
  simp only [NNReal.coe_inv, Real.coe_toNNReal _ h0.le]

/-- **Convergence of the canonical measures.** Under the standing hypotheses, together with the
lower bound `n P(|X| > 2 aₙ) ≥ c > 0`, there are `L₀ > 0` and a probability measure `P` with
`n ∫ k(z) g(z) dρₙ(z) → L₀ ∫ g dP` for every bounded continuous `g`. -/
theorem exists_tendsto_mul_integral_kern (ha : ∀ n, 0 < a n) (hs₀ : 0 < s₀)
    (hlow : ∃ c > 0, ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) * absTail μ (2 * a n)) :
    ∃ L₀ > 0, ∃ P : ProbabilityMeasure ℝ, ∀ g : ℝ →ᵇ ℝ,
      Tendsto (fun n : ℕ => (n : ℝ) * ∫ z, kern s₀ z * g z ∂(cLaw μ a n)) atTop
        (𝓝 (L₀ * ∫ z, g z ∂(P : Measure ℝ))) := by
  obtain ⟨c, hc, hlow⟩ := hlow
  obtain ⟨ck, hck, hk⟩ := exists_le_kern hs₀ one_pos
  set r : ℕ → ℝ := fun n => (n : ℝ) * (kernMeasure s₀ (cLaw μ a n)).real univ with hr
  have hr_lim : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 (lamK (ν : Measure ℝ) s₀ 0)) := by
    refine (tendsto_mul_charFun_kernMeasure hconv hφ hw hD hs₀.le 0).congr fun n => ?_
    rw [charFun_zero, hr]; push_cast; ring
  have hr_low : ∀ᶠ n : ℕ in atTop, ck * c ≤ r n := by
    filter_upwards [hlow] with n hn
    have h1 := le_measureReal_univ_kernMeasure (μ := μ) hs₀ hk (ha n)
    calc ck * c ≤ ck * ((n : ℝ) * absTail μ (2 * a n)) := mul_le_mul_of_nonneg_left hn hck.le
      _ = n * (ck * absTail μ (2 * a n)) := by ring
      _ ≤ r n := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
  set L₀ := (lamK (ν : Measure ℝ) s₀ 0).re
  have hr_lim' : Tendsto r atTop (𝓝 L₀) := by
    have := (Complex.continuous_re.tendsto _).comp hr_lim
    exact this.congr fun n => by simp
  have hL₀ : ck * c ≤ L₀ := ge_of_tendsto hr_lim' hr_low
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le (mul_pos hck hc) hL₀
  have hlam0 : lamK (ν : Measure ℝ) s₀ 0 = (L₀ : ℂ) := by
    have him := (Complex.continuous_im.tendsto _).comp hr_lim
    have h0 : (lamK (ν : Measure ℝ) s₀ 0).im = 0 :=
      tendsto_nhds_unique him (tendsto_const_nhds.congr fun n => by simp)
    exact Complex.ext rfl (by rw [h0]; simp)
  -- eventually the mass is positive
  have hmass : ∀ᶠ n : ℕ in atTop, 0 < (kernMeasure s₀ (cLaw μ a n)).real univ ∧ 0 < r n := by
    filter_upwards [hr_low, eventually_gt_atTop 0] with n hn hn0
    have hrpos : 0 < r n := lt_of_lt_of_le (mul_pos hck hc) hn
    refine ⟨?_, hrpos⟩
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    by_contra h
    have h' : (kernMeasure s₀ (cLaw μ a n)).real univ = 0 := le_antisymm (not_lt.1 h)
      measureReal_nonneg
    simp only [hr, h', mul_zero] at hrpos
    exact lt_irrefl _ hrpos
  -- characteristic functions of the normalized measures
  have hcf : ∀ t, Tendsto (fun n => charFun (kernNorm s₀ μ a n : Measure ℝ) t) atTop
      (𝓝 (lamK (ν : Measure ℝ) s₀ t / (L₀ : ℂ))) := by
    intro t
    refine ((tendsto_mul_charFun_kernMeasure hconv hφ hw hD hs₀.le t).div hr_lim'.ofReal
      (by exact_mod_cast hL₀pos.ne')).congr' ?_
    filter_upwards [hmass, eventually_gt_atTop 0] with n hn hn0
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [charFun_apply_real, integral_kernNorm hn.1, ← charFun_apply_real, Complex.real_smul, hr]
    push_cast
    have h1 : ((kernMeasure s₀ (cLaw μ a n)).real univ : ℂ) ≠ 0 := by exact_mod_cast hn.1.ne'
    have h2 : (n : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    simp only [Pi.div_apply]
    field_simp
  have hcont : ContinuousAt (fun t => lamK (ν : Measure ℝ) s₀ t / (L₀ : ℂ)) 0 :=
    (continuousAt_lamK hconv hφ hw hD hs₀.le).div_const _
  obtain ⟨P, -, hPlim⟩ := exists_tendsto_of_tendsto_charFun (μ := kernNorm s₀ μ a) hcont hcf
  refine ⟨L₀, hL₀pos, P, fun g => ?_⟩
  have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hPlim) g
  refine (hr_lim'.mul hint).congr' ?_
  filter_upwards [hmass] with n hn
  rw [integral_kernNorm hn.1, integral_kernMeasure hs₀.le, smul_eq_mul, hr]
  simp only [smul_eq_mul]
  have := hn.1.ne'
  field_simp

end LevyLimit

section Vague

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ} {ν : ProbabilityMeasure ℝ}

/-- `f / k` as a bounded continuous function, for `f` vanishing near `0`. -/
theorem exists_bcf_div_kern {s₀ : ℝ} (hs₀ : 0 < s₀) (f : ℝ →ᵇ ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hf0 : ∀ z, |z| < x₀ → f z = 0) :
    ∃ g : ℝ →ᵇ ℝ, ∀ z, kern s₀ z * g z = f z := by
  obtain ⟨c, hc, hk⟩ := exists_le_kern hs₀ hx₀
  have hcont : Continuous fun z => f z / kern s₀ z := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z = 0
    · subst hz
      have hev : (fun z => f z / kern s₀ z) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hx₀] with y hy
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
        rw [hf0 y hy, zero_div]
      exact (continuousAt_const.congr hev.symm)
    · exact f.continuous.continuousAt.div continuous_kern.continuousAt (kern_pos hs₀ hz).ne'
  have hbd : ∀ z, ‖f z / kern s₀ z‖ ≤ ‖f‖ / c := by
    intro z
    by_cases hz : |z| < x₀
    · rw [hf0 z hz, zero_div, norm_zero]; positivity
    · have hkz := hk z (not_lt.1 hz)
      rw [norm_div, Real.norm_eq_abs (kern s₀ z), abs_of_pos (hc.trans_le hkz)]
      exact div_le_div₀ (norm_nonneg _) (f.norm_coe_le_norm z) hc hkz
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup _ hcont _ hbd, fun z => ?_⟩
  simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
  by_cases hz : z = 0
  · subst hz; rw [hf0 0 (by simpa using hx₀)]; simp
  · rw [mul_div_cancel₀ _ (kern_pos hs₀ hz).ne']

/-- **Vague convergence of `n P(X / aₙ ∈ ·)` away from `0`** (Gnedenko–Kolmogorov, Feller
§XVII.2). Let `(Sₙ - bₙ) / aₙ → ν` weakly, where `φ_ν` does not vanish, and assume
`n E[min (1, (X / aₙ)²)]` is bounded, `n E[min (1, (s X / aₙ)²)]` is uniformly small for small
`s`, and `n P(|X| > 2 aₙ)` is bounded below. Then for every bounded Lipschitz `f` vanishing on a
neighbourhood of `0`, `n E[f(X / aₙ)]` converges. -/
theorem exists_tendsto_mul_integral_comp (ha : ∀ n, 0 < a n)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    (hφ : ∀ t, charFun (ν : Measure ℝ) t ≠ 0)
    (hS : ∃ C, ∀ᶠ n : ℕ in atTop, (n : ℝ) * sqRatio μ (a n) ≤ C)
    (hsmall : ∀ η > 0, ∃ s₀ > 0, ∀ᶠ n : ℕ in atTop, (n : ℝ) * sqRatio μ (a n / s₀) ≤ η)
    (hlow : ∃ c > 0, ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) * absTail μ (2 * a n))
    (f : ℝ →ᵇ ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hf0 : ∀ z, |z| < x₀ → f z = 0) {K : ℝ≥0}
    (hfL : LipschitzWith K f) :
    ∃ L, Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, f ((a n)⁻¹ * x) ∂μ) atTop (𝓝 L) := by
  obtain ⟨s₀, hs₀, hD⟩ := exists_forall_norm_dfun_le ha hS hsmall
  have hw := exists_norm_mul_wfun_le ha hS
  obtain ⟨L₀, -, P, hP⟩ := exists_tendsto_mul_integral_kern hconv hφ hw hD ha hs₀ hlow
  obtain ⟨g, hg⟩ := exists_bcf_div_kern hs₀ f hx₀ hf0
  refine ⟨L₀ * ∫ z, g z ∂(P : Measure ℝ), ?_⟩
  have h1 := hP g
  simp_rw [hg] at h1
  -- the shift by `τₙ` is negligible
  obtain ⟨C, hC⟩ := hS
  set M := max 1 (4 / x₀ ^ 2)
  have hτ0 : Tendsto (fun n => ctr μ a n) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n => ctr μ a n ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => sq_nonneg _) ?_
        ((tendsto_const_nhds (x := C)).div_atTop tendsto_natCast_atTop_atTop)
      filter_upwards [hC, eventually_gt_atTop 0] with n hn hn0
      have : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [le_div_iff₀ this]
      have := ctr_sq_le (μ := μ) (ha n).ne'
      nlinarith
    have := (continuous_sqrt.tendsto 0).comp hsq
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at this
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 this
  have hdiff : Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, f ((a n)⁻¹ * x) ∂μ -
      (n : ℝ) * ∫ z, f z ∂(cLaw μ a n)) atTop (𝓝 0) := by
    have hbound : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) * ∫ x, f ((a n)⁻¹ * x) ∂μ -
        (n : ℝ) * ∫ z, f z ∂(cLaw μ a n)‖ ≤ K * M * max C 0 * |ctr μ a n| := by
      filter_upwards [hC, (tendsto_order.1 hτ0.abs).2 (x₀ / 2) (by rw [abs_zero]; positivity)]
        with n hn hτ
      set τ := ctr μ a n
      have hi1 : Integrable (fun x => f ((a n)⁻¹ * x)) μ :=
        Integrable.of_bound (f.continuous.comp (by fun_prop)).aestronglyMeasurable ‖f‖
          (ae_of_all _ fun x => f.norm_coe_le_norm _)
      have hi2 : Integrable (fun x => f ((a n)⁻¹ * x - τ)) μ :=
        Integrable.of_bound (f.continuous.comp (by fun_prop)).aestronglyMeasurable ‖f‖
          (ae_of_all _ fun x => f.norm_coe_le_norm _)
      have hpt : ∀ y : ℝ, |f y - f (y - τ)| ≤ K * |τ| * (M * min 1 (y ^ 2)) := by
        intro y
        by_cases hy : |y| < x₀ / 2
        · have h1 : |y| < x₀ := by linarith
          have h2 : |y - τ| < x₀ := by
            have := abs_sub y τ; linarith
          rw [hf0 y h1, hf0 _ h2, sub_zero, abs_zero]
          positivity
        · have hL := hfL.dist_le_mul y (y - τ)
          rw [Real.dist_eq, Real.dist_eq, show y - (y - τ) = τ by ring] at hL
          have hM : 1 ≤ M * min 1 (y ^ 2) := by
            rcases le_total 1 (y ^ 2) with h | h
            · rw [min_eq_left h, mul_one]; exact le_max_left _ _
            · rw [min_eq_right h]
              have hy2 : x₀ ^ 2 / 4 ≤ y ^ 2 := by
                have : x₀ / 2 ≤ |y| := not_lt.1 hy
                rw [← sq_abs y]; nlinarith
              calc (1 : ℝ) = 4 / x₀ ^ 2 * (x₀ ^ 2 / 4) := by field_simp
                _ ≤ M * y ^ 2 := mul_le_mul (le_max_right _ _) hy2 (by positivity)
                    (by positivity)
          calc |f y - f (y - τ)| ≤ K * |τ| := hL
            _ = K * |τ| * 1 := (mul_one _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)
      rw [cLaw, integral_map (by fun_prop) f.continuous.aestronglyMeasurable, ← mul_sub,
        ← integral_sub hi1 hi2, norm_mul, Real.norm_natCast]
      have hint : ∫ x, ‖f ((a n)⁻¹ * x) - f ((a n)⁻¹ * x - τ)‖ ∂μ ≤
          K * |τ| * (M * sqRatio μ (a n)) := by
        rw [sqRatio_eq_integral_min (ha n).ne', ← integral_const_mul, ← integral_const_mul]
        refine integral_mono (hi1.sub hi2).norm ((integrable_min_one_sq n).const_mul _
          |>.const_mul _) fun x => ?_
        simp only
        rw [Real.norm_eq_abs]
        exact (hpt _).trans_eq (by ring)
      calc (n : ℝ) * ‖∫ x, (f ((a n)⁻¹ * x) - f ((a n)⁻¹ * x - τ)) ∂μ‖
          ≤ n * (K * |τ| * (M * sqRatio μ (a n))) :=
            mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans hint)
              (Nat.cast_nonneg n)
        _ = K * M * |τ| * (n * sqRatio μ (a n)) := by ring
        _ ≤ K * M * |τ| * max C 0 :=
            mul_le_mul_of_nonneg_left (hn.trans (le_max_left _ _)) (by positivity)
        _ = _ := by ring
    have := (hτ0.abs.const_mul (K * M * max C 0))
    rw [abs_zero, mul_zero] at this
    exact squeeze_zero_norm' hbound this
  have := h1.add hdiff
  rw [add_zero] at this
  exact this.congr fun n => by ring

end Vague

end GCLTConverse

end ExtremeValueTheory
