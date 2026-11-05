/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GPDLogLikExpansion
import ExtremeValueTheory.Statistics.GPDMLENormality
import ExtremeValueTheory.Statistics.ConfidenceIntervals
import ExtremeValueTheory.ForMathlib.Probability.ChiSquared

/-!
# Stochastic expansion of the GPD deviance, `ξ₀ > 0`

The deviance of a root of the likelihood equations, and of an estimator restricted to a curve
through the true parameter, as a quadratic form in the normalized score plus `o_P(1)`.

## Main results

* `isLittleO_full_deviance`, `isLittleO_curve_deviance`: the deterministic core, for fixed sequences.
* `tendstoInMeasure_zero_of_ae_isLittleO`: almost surely `o` of a sequence bounded in probability
  implies convergence to `0` in probability.
* `gpdNormScore_eq`, `abs_gpdDeviance_sub_le`: the sample score and the sample deviance to second
  order.
* `ae_gpdWilks_limits`: the strong laws needed.
* `tendstoInMeasure_gpdDeviance_sub`: `2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - Sₙᵀ I⁻¹ Sₙ → 0` in probability.
* `tendstoInMeasure_gpdCurveDeviance_sub`: `2 (ℓₙ(θ̃ₙ) - ℓₙ(θ₀)) - (t · Sₙ)²/(tᵀ I t) → 0` in
  probability, for a restricted estimator stationary along a curve with tangent `t` at `θ₀`.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §2.6.5–2.6.6.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), §16.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Asymptotics

namespace ExtremeValueTheory

/-! ### Stochastic order: a sequence that is almost surely `o` of a tight one -/

section Stochastic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- If, almost surely, `fₙ = o(Gₙ)` along the sequence, and `Gₙ` is bounded in probability, then
`fₙ → 0` in probability. -/
theorem tendstoInMeasure_zero_of_ae_isLittleO {f G : ℕ → Ω → ℝ}
    (hf : ∀ n, AEMeasurable (f n) P) (hGm : ∀ n, AEMeasurable (G n) P)
    (hG : IsBoundedInProbability P G)
    (h : ∀ᵐ ω ∂P, (fun n => f n ω) =o[atTop] fun n => G n ω) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  set Z : ℕ → Ω → ℝ := fun n ω => 1 + |G n ω|
  have hZ0 : ∀ n ω, 0 < Z n ω := fun n ω => by positivity
  have hZ : IsBoundedInProbability P Z := fun ε hε => by
    obtain ⟨M, hM⟩ := hG ε hε
    refine ⟨1 + M, hM.mono fun n hn => (measure_mono fun ω hω => ?_).trans hn⟩
    simp only [Z, mem_ofPred_eq, abs_of_pos (hZ0 n ω)] at hω ⊢
    linarith
  set Y : ℕ → Ω → ℝ := fun n ω => f n ω / Z n ω
  have hY : TendstoInMeasure P Y atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · have := hf n; have := hGm n
      exact (by simp only [Y, Z]; fun_prop : AEMeasurable (Y n) P).aestronglyMeasurable
    · filter_upwards [h] with ω hω
      have hb : (fun n => G n ω) =O[atTop] fun n => Z n ω :=
        IsBigO.of_bound 1 (Eventually.of_forall fun n => by
          simp only [Z, Real.norm_eq_abs, one_mul, abs_of_pos (hZ0 n ω)]
          linarith)
      exact (hω.trans_isBigO hb).tendsto_div_nhds_zero
  have := tendstoInMeasure_mul_zero_of_isBoundedInProbability' hZ hY
  convert this using 2 with n
  funext ω
  simp only [Y]
  field_simp [(hZ0 n ω).ne']

omit [IsProbabilityMeasure P] in
/-- A cubic polynomial in two sequences bounded in probability is bounded in probability. -/
theorem isBoundedInProbability_cube {S₁ S₂ : ℕ → Ω → ℝ} (h₁ : IsBoundedInProbability P S₁)
    (h₂ : IsBoundedInProbability P S₂) :
    IsBoundedInProbability P fun n ω => (1 + |S₁ n ω| + |S₂ n ω|) ^ 3 := by
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨M₁, hM₁⟩ := h₁ _ hε2
  obtain ⟨M₂, hM₂⟩ := h₂ _ hε2
  refine ⟨(1 + M₁ + M₂) ^ 3, ?_⟩
  filter_upwards [hM₁, hM₂] with n h1 h2
  refine (measure_mono (t := {ω | M₁ < |S₁ n ω|} ∪ {ω | M₂ < |S₂ n ω|}) ?_).trans
    ((measure_union_le _ _).trans ((add_le_add h1 h2).trans (ENNReal.add_halves ε).le))
  intro ω hω
  simp only [mem_ofPred_eq, mem_union] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨hz, hy⟩ := hcon
  have h0 : 0 ≤ 1 + |S₁ n ω| + |S₂ n ω| := by positivity
  have h3 : (1 + |S₁ n ω| + |S₂ n ω|) ^ 3 ≤ (1 + M₁ + M₂) ^ 3 :=
    pow_le_pow_left₀ h0 (by linarith) 3
  rw [abs_of_nonneg (by positivity)] at hω
  linarith

end Stochastic

/-! ### Deterministic asymptotics of the deviance -/

section Deterministic

variable {S₁ S₂ : ℕ → ℝ}

private lemma isBigO_S₁ : S₁ =O[atTop] fun n => 1 + |S₁ n| + |S₂ n| :=
  IsBigO.of_bound 1 (Eventually.of_forall fun n => by
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + |S₁ n| + |S₂ n|)]
    linarith [abs_nonneg (S₂ n)])

private lemma isBigO_S₂ : S₂ =O[atTop] fun n => 1 + |S₁ n| + |S₂ n| :=
  IsBigO.of_bound 1 (Eventually.of_forall fun n => by
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + |S₁ n| + |S₂ n|)]
    linarith [abs_nonneg (S₁ n)])

/-- A linear combination with convergent coefficients is `O(g)`, and `o(g)` if the limits vanish. -/
private lemma isLittleO_comb {a b g : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (h₁ : S₁ =O[atTop] g) (h₂ : S₂ =O[atTop] g) :
    (fun n => a n * S₁ n + b n * S₂ n) =o[atTop] g := by
  have ha' : a =o[atTop] fun _ => (1 : ℝ) := (isLittleO_one_iff ℝ).2 ha
  have hb' : b =o[atTop] fun _ => (1 : ℝ) := (isLittleO_one_iff ℝ).2 hb
  simpa using (ha'.mul_isBigO h₁).add (hb'.mul_isBigO h₂)

private lemma isBigO_mul_of_tendsto {a f g : ℕ → ℝ} {l : ℝ} (ha : Tendsto a atTop (𝓝 l))
    (hf : f =O[atTop] g) : (fun n => a n * f n) =O[atTop] g := by
  simpa using (ha.isBigO_one ℝ).mul hf

private lemma isLittleO_mul_of_tendsto_zero {a f g : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    (hf : f =O[atTop] g) : (fun n => a n * f n) =o[atTop] g := by
  simpa using ((isLittleO_one_iff ℝ).2 ha).mul_isBigO hf

/-- **Deterministic core of Wilks' theorem along a curve.** Numbers:
`Sᵢ`, normalized scores at the true parameter; `τ`, the normalized distance along the curve;
`slᵢ` the chord of the curve; `tanᵢ` the tangent at the constrained maximizer; `Bᵢⱼ` the averaged
segment Hessians; `hᵢⱼ` the averaged Hessians at the true parameter; `D` the restricted deviance. -/
theorem isLittleO_curve_deviance {τ sl₁ sl₂ tn₁ tn₂ B₁₁ B₁₂ B₂₂ h₁₁ h₁₂ h₂₂ ε D : ℕ → ℝ}
    {A B C t₁ t₂ : ℝ} (hc : 0 < A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2)
    (hsl₁ : Tendsto sl₁ atTop (𝓝 t₁)) (hsl₂ : Tendsto sl₂ atTop (𝓝 t₂))
    (htn₁ : Tendsto tn₁ atTop (𝓝 t₁)) (htn₂ : Tendsto tn₂ atTop (𝓝 t₂))
    (hB₁₁ : Tendsto B₁₁ atTop (𝓝 (-A))) (hB₁₂ : Tendsto B₁₂ atTop (𝓝 (-B)))
    (hB₂₂ : Tendsto B₂₂ atTop (𝓝 (-C)))
    (hh₁₁ : Tendsto h₁₁ atTop (𝓝 (-A))) (hh₁₂ : Tendsto h₁₂ atTop (𝓝 (-B)))
    (hh₂₂ : Tendsto h₂₂ atTop (𝓝 (-C)))
    (hε : Tendsto ε atTop (𝓝 0))
    (hroot : ∀ᶠ n in atTop,
      tn₁ n * (S₁ n + τ n * (sl₁ n * B₁₁ n + sl₂ n * B₁₂ n)) +
        tn₂ n * (S₂ n + τ n * (sl₁ n * B₁₂ n + sl₂ n * B₂₂ n)) = 0)
    (hD : ∀ᶠ n in atTop, |D n - (2 * τ n * (sl₁ n * (S₁ n + τ n * (sl₁ n * B₁₁ n + sl₂ n * B₁₂ n)) +
        sl₂ n * (S₂ n + τ n * (sl₁ n * B₁₂ n + sl₂ n * B₂₂ n))) -
        τ n ^ 2 * (sl₁ n ^ 2 * h₁₁ n + 2 * sl₁ n * sl₂ n * h₁₂ n + sl₂ n ^ 2 * h₂₂ n))| ≤
      ε n * (|τ n| * (|sl₁ n| + |sl₂ n|)) ^ 3) :
    (fun n => D n - (t₁ * S₁ n + t₂ * S₂ n) ^ 2 / (A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2))
      =o[atTop] fun n => (1 + |S₁ n| + |S₂ n|) ^ 3 := by
  set c := A * t₁ ^ 2 + 2 * B * t₁ * t₂ + C * t₂ ^ 2 with hcdef
  set g : ℕ → ℝ := fun n => 1 + |S₁ n| + |S₂ n| with hg
  have hg1 : ∀ n, 1 ≤ g n := fun n => by simp only [hg]; linarith [abs_nonneg (S₁ n), abs_nonneg (S₂ n)]
  have hS₁ : S₁ =O[atTop] g := isBigO_S₁
  have hS₂ : S₂ =O[atTop] g := isBigO_S₂
  -- the coefficient of `τ`
  set Cn : ℕ → ℝ := fun n => -(tn₁ n * (sl₁ n * B₁₁ n + sl₂ n * B₁₂ n) +
    tn₂ n * (sl₁ n * B₁₂ n + sl₂ n * B₂₂ n)) with hCn
  have hCnl : Tendsto Cn atTop (𝓝 c) := by
    have := ((htn₁.mul ((hsl₁.mul hB₁₁).add (hsl₂.mul hB₁₂))).add
      (htn₂.mul ((hsl₁.mul hB₁₂).add (hsl₂.mul hB₂₂)))).neg
    convert this using 2
    simp only [hcdef]
    ring
  have hτeq : ∀ᶠ n in atTop, τ n = tn₁ n / Cn n * S₁ n + tn₂ n / Cn n * S₂ n := by
    filter_upwards [hroot, hCnl.eventually (lt_mem_nhds hc)] with n h1 h2
    have h3 : Cn n ≠ 0 := h2.ne'
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h3]
    simp only [hCn]
    linear_combination (-1 : ℝ) * h1
  have hcoef₁ : Tendsto (fun n => tn₁ n / Cn n) atTop (𝓝 (t₁ / c)) := htn₁.div hCnl hc.ne'
  have hcoef₂ : Tendsto (fun n => tn₂ n / Cn n) atTop (𝓝 (t₂ / c)) := htn₂.div hCnl hc.ne'
  set y : ℕ → ℝ := fun n => t₁ / c * S₁ n + t₂ / c * S₂ n with hy
  have hyO : y =O[atTop] g := (hS₁.const_mul_left _).add (hS₂.const_mul_left _)
  have hτy : (fun n => τ n - y n) =o[atTop] g := by
    have := isLittleO_comb (S₁ := S₁) (S₂ := S₂) (a := fun n => tn₁ n / Cn n - t₁ / c)
      (b := fun n => tn₂ n / Cn n - t₂ / c) (by simpa using hcoef₁.sub_const (t₁ / c))
      (by simpa using hcoef₂.sub_const (t₂ / c)) hS₁ hS₂
    refine this.congr' ?_ EventuallyEq.rfl
    filter_upwards [hτeq] with n hn
    rw [hn]
    simp only [hy]
    ring
  have hτO : τ =O[atTop] g :=
    ((isBigO_mul_of_tendsto hcoef₁ hS₁).add (isBigO_mul_of_tendsto hcoef₂ hS₂)).congr'
      (hτeq.mono fun n hn => hn.symm) EventuallyEq.rfl
  -- the normalized scores at the constrained maximizer
  set W₁ : ℕ → ℝ := fun n => S₁ n + τ n * (sl₁ n * B₁₁ n + sl₂ n * B₁₂ n) with hW₁d
  set W₂ : ℕ → ℝ := fun n => S₂ n + τ n * (sl₁ n * B₁₂ n + sl₂ n * B₂₂ n) with hW₂d
  have hW₁ : W₁ =O[atTop] g := hS₁.add
    ((isBigO_mul_of_tendsto ((hsl₁.mul hB₁₁).add (hsl₂.mul hB₁₂)) hτO).congr_left
      fun n => mul_comm _ _)
  have hW₂ : W₂ =O[atTop] g := hS₂.add
    ((isBigO_mul_of_tendsto ((hsl₁.mul hB₁₂).add (hsl₂.mul hB₂₂)) hτO).congr_left
      fun n => mul_comm _ _)
  have hgg : (fun n => g n * g n) =O[atTop] fun n => g n ^ 3 :=
    IsBigO.of_bound 1 (Eventually.of_forall fun n => by
      have h0 := hg1 n
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h0) (zero_le_one.trans h0))
        (zero_le_one.trans h0)])
  -- the linear term
  set T1 : ℕ → ℝ := fun n => 2 * τ n * ((sl₁ n - tn₁ n) * W₁ n + (sl₂ n - tn₂ n) * W₂ n) with hT1d
  have hT1 : T1 =o[atTop] fun n => g n ^ 3 := by
    have hinner := isLittleO_comb (S₁ := W₁) (S₂ := W₂) (a := fun n => sl₁ n - tn₁ n)
      (b := fun n => sl₂ n - tn₂ n) (by simpa using hsl₁.sub htn₁) (by simpa using hsl₂.sub htn₂)
      hW₁ hW₂
    exact ((hτO.const_mul_left 2).mul_isLittleO hinner).trans_isBigO hgg
  -- the quadratic term
  set Qn : ℕ → ℝ := fun n => sl₁ n ^ 2 * h₁₁ n + 2 * sl₁ n * sl₂ n * h₁₂ n + sl₂ n ^ 2 * h₂₂ n
    with hQnd
  have hQ : Tendsto (fun n => -Qn n - c) atTop (𝓝 0) := by
    have := ((((hsl₁.pow 2).mul hh₁₁).add (((hsl₁.const_mul 2).mul hsl₂).mul hh₁₂)).add
      ((hsl₂.pow 2).mul hh₂₂)).neg.sub_const c
    convert this using 2
    simp only [hcdef]
    ring
  set T2 : ℕ → ℝ := fun n => (-Qn n - c) * τ n * τ n + c * ((τ n - y n) * (τ n + y n)) with hT2d
  have hT2 : T2 =o[atTop] fun n => g n ^ 3 := by
    have h1 := (isLittleO_mul_of_tendsto_zero hQ hτO).mul_isBigO hτO
    have h2 := (hτy.mul_isBigO (hτO.add hyO)).const_mul_left c
    exact (h1.add h2).trans_isBigO hgg
  -- the remainder
  set R : ℕ → ℝ := fun n => D n - (2 * τ n * (sl₁ n * W₁ n + sl₂ n * W₂ n) - τ n ^ 2 * Qn n) with hRd
  have hR : R =o[atTop] fun n => g n ^ 3 := by
    have hinner : (fun n => |τ n| * (|sl₁ n| + |sl₂ n|)) =O[atTop] g :=
      (isBigO_mul_of_tendsto (hsl₁.abs.add hsl₂.abs) hτO.norm_left).congr_left fun n => by
        rw [Real.norm_eq_abs, mul_comm]
    have h3 := isLittleO_mul_of_tendsto_zero hε (hinner.pow 3)
    refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_) h3
    filter_upwards [hD] with n hn
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact hn.trans (le_abs_self _)
  refine ((hR.add hT1).add hT2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hroot] with n hn
  have hy2 : (t₁ * S₁ n + t₂ * S₂ n) ^ 2 / c = c * y n ^ 2 := by
    simp only [hy]
    field_simp
  rw [hy2]
  simp only [hRd, hT1d, hT2d]
  linear_combination (-2 * τ n) * hn

/-- **Deterministic core of Wilks' theorem for the full parameter.** With `Tᵢ` the normalized
distance to the true parameter of a root of the likelihood equations, the deviance `D` is
`(C S₁² - 2 B S₁ S₂ + A S₂²)/(A C - B²)` (the quadratic form of the inverse information in the
normalized score), up to `o((1 + |S₁| + |S₂|)³)`. -/
theorem isLittleO_full_deviance {T₁ T₂ B₁₁ B₁₂ B₂₂ h₁₁ h₁₂ h₂₂ ε D : ℕ → ℝ} {A B C : ℝ}
    (hd : 0 < A * C - B ^ 2)
    (hB₁₁ : Tendsto B₁₁ atTop (𝓝 (-A))) (hB₁₂ : Tendsto B₁₂ atTop (𝓝 (-B)))
    (hB₂₂ : Tendsto B₂₂ atTop (𝓝 (-C)))
    (hh₁₁ : Tendsto h₁₁ atTop (𝓝 (-A))) (hh₁₂ : Tendsto h₁₂ atTop (𝓝 (-B)))
    (hh₂₂ : Tendsto h₂₂ atTop (𝓝 (-C)))
    (hε : Tendsto ε atTop (𝓝 0))
    (hroot₁ : ∀ᶠ n in atTop, S₁ n + (T₁ n * B₁₁ n + T₂ n * B₁₂ n) = 0)
    (hroot₂ : ∀ᶠ n in atTop, S₂ n + (T₁ n * B₁₂ n + T₂ n * B₂₂ n) = 0)
    (hD : ∀ᶠ n in atTop, |D n - -(T₁ n ^ 2 * h₁₁ n + 2 * T₁ n * T₂ n * h₁₂ n + T₂ n ^ 2 * h₂₂ n)| ≤
      ε n * (|T₁ n| + |T₂ n|) ^ 3) :
    (fun n => D n - (C * S₁ n ^ 2 - 2 * B * S₁ n * S₂ n + A * S₂ n ^ 2) / (A * C - B ^ 2))
      =o[atTop] fun n => (1 + |S₁ n| + |S₂ n|) ^ 3 := by
  set d := A * C - B ^ 2 with hdd
  set g : ℕ → ℝ := fun n => 1 + |S₁ n| + |S₂ n| with hg
  have hg1 : ∀ n, 1 ≤ g n := fun n => by simp only [hg]; linarith [abs_nonneg (S₁ n), abs_nonneg (S₂ n)]
  have hS₁ : S₁ =O[atTop] g := isBigO_S₁
  have hS₂ : S₂ =O[atTop] g := isBigO_S₂
  set Δ : ℕ → ℝ := fun n => B₁₁ n * B₂₂ n - B₁₂ n ^ 2 with hΔd
  have hΔ : Tendsto Δ atTop (𝓝 d) := by
    have := (hB₁₁.mul hB₂₂).sub (hB₁₂.pow 2)
    convert this using 2
    simp only [hdd]
    ring
  have hcoef₁ : Tendsto (fun n => -B₂₂ n / Δ n) atTop (𝓝 (C / d)) := by
    have := hB₂₂.neg.div hΔ hd.ne'
    rwa [neg_neg] at this
  have hcoef₂ : Tendsto (fun n => B₁₂ n / Δ n) atTop (𝓝 (-B / d)) := hB₁₂.div hΔ hd.ne'
  have hcoef₃ : Tendsto (fun n => -B₁₁ n / Δ n) atTop (𝓝 (A / d)) := by
    have := hB₁₁.neg.div hΔ hd.ne'
    rwa [neg_neg] at this
  have hT₁e : ∀ᶠ n in atTop, T₁ n = -B₂₂ n / Δ n * S₁ n + B₁₂ n / Δ n * S₂ n := by
    filter_upwards [hroot₁, hroot₂, hΔ.eventually (lt_mem_nhds hd)] with n h1 h2 h3
    have h4 : Δ n ≠ 0 := h3.ne'
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h4]
    simp only [hΔd]
    linear_combination B₂₂ n * h1 - B₁₂ n * h2
  have hT₂e : ∀ᶠ n in atTop, T₂ n = B₁₂ n / Δ n * S₁ n + -B₁₁ n / Δ n * S₂ n := by
    filter_upwards [hroot₁, hroot₂, hΔ.eventually (lt_mem_nhds hd)] with n h1 h2 h3
    have h4 : Δ n ≠ 0 := h3.ne'
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h4]
    simp only [hΔd]
    linear_combination B₁₁ n * h2 - B₁₂ n * h1
  set y₁ : ℕ → ℝ := fun n => C / d * S₁ n + -B / d * S₂ n with hy₁
  set y₂ : ℕ → ℝ := fun n => -B / d * S₁ n + A / d * S₂ n with hy₂
  have hy₁O : y₁ =O[atTop] g := (hS₁.const_mul_left _).add (hS₂.const_mul_left _)
  have hy₂O : y₂ =O[atTop] g := (hS₁.const_mul_left _).add (hS₂.const_mul_left _)
  have hT₁y : (fun n => T₁ n - y₁ n) =o[atTop] g := by
    have := isLittleO_comb (S₁ := S₁) (S₂ := S₂) (a := fun n => -B₂₂ n / Δ n - C / d)
      (b := fun n => B₁₂ n / Δ n - -B / d) (by simpa using hcoef₁.sub_const (C / d))
      (by simpa using hcoef₂.sub_const (-B / d)) hS₁ hS₂
    refine this.congr' ?_ EventuallyEq.rfl
    filter_upwards [hT₁e] with n hn
    rw [hn]
    simp only [hy₁]
    ring
  have hT₂y : (fun n => T₂ n - y₂ n) =o[atTop] g := by
    have := isLittleO_comb (S₁ := S₁) (S₂ := S₂) (a := fun n => B₁₂ n / Δ n - -B / d)
      (b := fun n => -B₁₁ n / Δ n - A / d) (by simpa using hcoef₂.sub_const (-B / d))
      (by simpa using hcoef₃.sub_const (A / d)) hS₁ hS₂
    refine this.congr' ?_ EventuallyEq.rfl
    filter_upwards [hT₂e] with n hn
    rw [hn]
    simp only [hy₂]
    ring
  have hT₁O : T₁ =O[atTop] g :=
    ((isBigO_mul_of_tendsto hcoef₁ hS₁).add (isBigO_mul_of_tendsto hcoef₂ hS₂)).congr'
      (hT₁e.mono fun n hn => hn.symm) EventuallyEq.rfl
  have hT₂O : T₂ =O[atTop] g :=
    ((isBigO_mul_of_tendsto hcoef₂ hS₁).add (isBigO_mul_of_tendsto hcoef₃ hS₂)).congr'
      (hT₂e.mono fun n hn => hn.symm) EventuallyEq.rfl
  have hgg : (fun n => g n * g n) =O[atTop] fun n => g n ^ 3 :=
    IsBigO.of_bound 1 (Eventually.of_forall fun n => by
      have h0 := hg1 n
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h0) (zero_le_one.trans h0))
        (zero_le_one.trans h0)])
  -- the quadratic form
  set T2 : ℕ → ℝ := fun n => (-h₁₁ n - A) * T₁ n * T₁ n + 2 * ((-h₁₂ n - B) * T₁ n * T₂ n) +
      (-h₂₂ n - C) * T₂ n * T₂ n +
      (A * ((T₁ n - y₁ n) * (T₁ n + y₁ n)) +
        2 * B * ((T₁ n - y₁ n) * T₂ n + y₁ n * (T₂ n - y₂ n)) +
        C * ((T₂ n - y₂ n) * (T₂ n + y₂ n))) with hT2d
  have h0lim : ∀ {h : ℕ → ℝ} {a : ℝ}, Tendsto h atTop (𝓝 (-a)) →
      Tendsto (fun n => -h n - a) atTop (𝓝 0) := fun {h a} hh => by
    simpa using hh.neg.sub_const a
  have hT2 : T2 =o[atTop] fun n => g n ^ 3 := by
    have e1 := (isLittleO_mul_of_tendsto_zero (h0lim hh₁₁) hT₁O).mul_isBigO hT₁O
    have e2 := ((isLittleO_mul_of_tendsto_zero (h0lim hh₁₂) hT₁O).mul_isBigO hT₂O).const_mul_left 2
    have e3 := (isLittleO_mul_of_tendsto_zero (h0lim hh₂₂) hT₂O).mul_isBigO hT₂O
    have e4 := (hT₁y.mul_isBigO (hT₁O.add hy₁O)).const_mul_left A
    have e5 := ((hT₁y.mul_isBigO hT₂O).add (hy₁O.mul_isLittleO hT₂y)).const_mul_left (2 * B)
    have e6 := (hT₂y.mul_isBigO (hT₂O.add hy₂O)).const_mul_left C
    exact ((((e1.add e2).add e3)).add ((e4.add e5).add e6)).trans_isBigO hgg
  set R : ℕ → ℝ := fun n =>
    D n - -(T₁ n ^ 2 * h₁₁ n + 2 * T₁ n * T₂ n * h₁₂ n + T₂ n ^ 2 * h₂₂ n) with hRd
  have hR : R =o[atTop] fun n => g n ^ 3 := by
    have hinner : (fun n => |T₁ n| + |T₂ n|) =O[atTop] g := hT₁O.norm_left.add hT₂O.norm_left
    have h3 := isLittleO_mul_of_tendsto_zero hε (hinner.pow 3)
    refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_) h3
    filter_upwards [hD] with n hn
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact hn.trans (le_abs_self _)
  refine (hR.add hT2).congr' (Eventually.of_forall fun n => ?_) EventuallyEq.rfl
  have hk : A * (C * S₁ n - B * S₂ n) ^ 2 + 2 * B * ((C * S₁ n - B * S₂ n) * (-B * S₁ n + A * S₂ n)) +
      C * (-B * S₁ n + A * S₂ n) ^ 2 = d * (C * S₁ n ^ 2 - 2 * B * S₁ n * S₂ n + A * S₂ n ^ 2) := by
    rw [hdd]
    ring
  have hq : (C * S₁ n ^ 2 - 2 * B * S₁ n * S₂ n + A * S₂ n ^ 2) / d =
      A * y₁ n ^ 2 + 2 * B * (y₁ n * y₂ n) + C * y₂ n ^ 2 := by
    have e₁ : y₁ n = (C * S₁ n - B * S₂ n) / d := by simp only [hy₁]; ring
    have e₂ : y₂ n = (-B * S₁ n + A * S₂ n) / d := by simp only [hy₂]; ring
    have hd0 := hd.ne'
    have : A * y₁ n ^ 2 + 2 * B * (y₁ n * y₂ n) + C * y₂ n ^ 2 =
        (A * (C * S₁ n - B * S₂ n) ^ 2 + 2 * B * ((C * S₁ n - B * S₂ n) * (-B * S₁ n + A * S₂ n)) +
          C * (-B * S₁ n + A * S₂ n) ^ 2) / d ^ 2 := by
      rw [e₁, e₂]
      field_simp
    rw [this, hk]
    field_simp
  change R n + T2 n = D n - (C * S₁ n ^ 2 - 2 * B * S₁ n * S₂ n + A * S₂ n ^ 2) / d
  rw [hq]
  simp only [hRd, hT2d]
  ring

end Deterministic

/-! ### The sample quantities -/

section Sample

/-- The normalized score in the shape, `n^{-1/2} ∑_{i<n} ∂_ξ ℓ(ξ, σ; xᵢ)`. -/
noncomputable def gpdNormScoreXi (ξ σ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreXi ξ σ (x i)

/-- The normalized score in the scale, `n^{-1/2} ∑_{i<n} ∂_σ ℓ(ξ, σ; xᵢ)`. -/
noncomputable def gpdNormScoreSigma (ξ σ : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, gpdScoreSigma ξ σ (x i)

/-- The empirical mean `n⁻¹ ∑_{i<n} f(xᵢ)`. -/
noncomputable def sampleAvg (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (x i)

variable {ξ₀ σ₀ K : ℝ}

/-- The normalized score at `θ` in terms of the normalized score at `θ₀` and the averaged segment
Hessians. -/
theorem gpdNormScore_eq (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀) (hK0 : 0 ≤ K)
    (hK : ∀ θ ∈ gpdNbhd ξ₀ σ₀, ∀ x, 0 ≤ x →
      |gpdHessXiXi θ.1 θ.2 x - gpdHessXiXi ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessXiSigma θ.1 θ.2 x - gpdHessXiSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessSigmaSigma θ.1 θ.2 x - gpdHessSigmaSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)))
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {n : ℕ} (hn : 0 < n) :
    gpdNormScoreXi θ.1 θ.2 x n = gpdNormScoreXi ξ₀ σ₀ x n +
        (√(n : ℝ) * (θ.1 - ξ₀) * sampleAvg (segHess gpdHessXiXi ξ₀ σ₀ θ) x n +
          √(n : ℝ) * (θ.2 - σ₀) * sampleAvg (segHess gpdHessXiSigma ξ₀ σ₀ θ) x n) ∧
    gpdNormScoreSigma θ.1 θ.2 x n = gpdNormScoreSigma ξ₀ σ₀ x n +
        (√(n : ℝ) * (θ.1 - ξ₀) * sampleAvg (segHess gpdHessXiSigma ξ₀ σ₀ θ) x n +
          √(n : ℝ) * (θ.2 - σ₀) * sampleAvg (segHess gpdHessSigmaSigma ξ₀ σ₀ θ) x n) := by
  have hexp := fun i => gpdScore_sub_eq_segHess hξ₀ hσ₀ hK0 hK hθ (hx i)
  have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hN : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  have e₁ : ∑ i ∈ Finset.range n, gpdScoreXi θ.1 θ.2 (x i) =
      ∑ i ∈ Finset.range n, gpdScoreXi ξ₀ σ₀ (x i) +
        ((θ.1 - ξ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiXi ξ₀ σ₀ θ (x i) +
          (θ.2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma ξ₀ σ₀ θ (x i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by linarith [(hexp i).1]
  have e₂ : ∑ i ∈ Finset.range n, gpdScoreSigma θ.1 θ.2 (x i) =
      ∑ i ∈ Finset.range n, gpdScoreSigma ξ₀ σ₀ (x i) +
        ((θ.1 - ξ₀) * ∑ i ∈ Finset.range n, segHess gpdHessXiSigma ξ₀ σ₀ θ (x i) +
          (θ.2 - σ₀) * ∑ i ∈ Finset.range n, segHess gpdHessSigmaSigma ξ₀ σ₀ θ (x i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by linarith [(hexp i).2.1]
  simp only [gpdNormScoreXi, gpdNormScoreSigma, sampleAvg, e₁, e₂]
  rw [hN]
  simp only [Real.sqrt_sq hr.le]
  constructor <;> field_simp

/-- **The sample deviance to second order.** With `r = √n`, `Uᵢ = r (θᵢ - θ₀ᵢ)`, `Wᵢ` the normalized
score at `θ`, `hᵢⱼ` the empirical mean of the Hessian at `θ₀` and `Λ` the empirical mean of
`1 + log(1 + ξ₀ x/σ₀)`,

  `|2 (ℓₙ(θ) - ℓₙ(θ₀)) - (2 U·W - Uᵀ h U)| ≤ 2 K r⁻¹ Λ (|U₁| + |U₂|)³`. -/
theorem abs_gpdDeviance_sub_le (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀) (hK0 : 0 ≤ K)
    (hK : ∀ θ ∈ gpdNbhd ξ₀ σ₀, ∀ x, 0 ≤ x →
      |gpdHessXiXi θ.1 θ.2 x - gpdHessXiXi ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessXiSigma θ.1 θ.2 x - gpdHessXiSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessSigmaSigma θ.1 θ.2 x - gpdHessSigmaSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)))
    {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {n : ℕ} (hn : 0 < n) :
    |2 * (gpdLogLikN θ.1 θ.2 x n - gpdLogLikN ξ₀ σ₀ x n) -
      (2 * (√(n : ℝ) * (θ.1 - ξ₀) * gpdNormScoreXi θ.1 θ.2 x n +
          √(n : ℝ) * (θ.2 - σ₀) * gpdNormScoreSigma θ.1 θ.2 x n) -
        ((√(n : ℝ) * (θ.1 - ξ₀)) ^ 2 * sampleAvg (gpdHessXiXi ξ₀ σ₀) x n +
          2 * (√(n : ℝ) * (θ.1 - ξ₀)) * (√(n : ℝ) * (θ.2 - σ₀)) *
            sampleAvg (gpdHessXiSigma ξ₀ σ₀) x n +
          (√(n : ℝ) * (θ.2 - σ₀)) ^ 2 * sampleAvg (gpdHessSigmaSigma ξ₀ σ₀) x n))| ≤
      2 * K * ((√(n : ℝ))⁻¹ * sampleAvg (fun y => 1 + log (1 + ξ₀ * y / σ₀)) x n) *
        (|√(n : ℝ) * (θ.1 - ξ₀)| + |√(n : ℝ) * (θ.2 - σ₀)|) ^ 3 := by
  have hexp := abs_gpdLogLikN_expansion_le hξ₀ hσ₀ hK0 hK hθ hx n
  have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hN : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  set r := √(n : ℝ)
  have hlin : ∑ i ∈ Finset.range n, ((ξ₀ - θ.1) * gpdScoreXi θ.1 θ.2 (x i) +
      (σ₀ - θ.2) * gpdScoreSigma θ.1 θ.2 (x i)) =
      (ξ₀ - θ.1) * ∑ i ∈ Finset.range n, gpdScoreXi θ.1 θ.2 (x i) +
        (σ₀ - θ.2) * ∑ i ∈ Finset.range n, gpdScoreSigma θ.1 θ.2 (x i) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
  have hquad : ∑ i ∈ Finset.range n, gpdHessQuad ξ₀ σ₀ (ξ₀ - θ.1) (σ₀ - θ.2) (x i) / 2 =
      ((ξ₀ - θ.1) ^ 2 * ∑ i ∈ Finset.range n, gpdHessXiXi ξ₀ σ₀ (x i) +
        2 * (ξ₀ - θ.1) * (σ₀ - θ.2) * ∑ i ∈ Finset.range n, gpdHessXiSigma ξ₀ σ₀ (x i) +
        (σ₀ - θ.2) ^ 2 * ∑ i ∈ Finset.range n, gpdHessSigmaSigma ξ₀ σ₀ (x i)) / 2 := by
    rw [← Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rfl
  rw [hlin, hquad] at hexp
  simp only [gpdNormScoreXi, gpdNormScoreSigma, sampleAvg]
  rw [hN, Real.sqrt_sq hr.le]
  set A₁ := ∑ i ∈ Finset.range n, gpdScoreXi θ.1 θ.2 (x i)
  set A₂ := ∑ i ∈ Finset.range n, gpdScoreSigma θ.1 θ.2 (x i)
  set H₁ := ∑ i ∈ Finset.range n, gpdHessXiXi ξ₀ σ₀ (x i)
  set H₂ := ∑ i ∈ Finset.range n, gpdHessXiSigma ξ₀ σ₀ (x i)
  set H₃ := ∑ i ∈ Finset.range n, gpdHessSigmaSigma ξ₀ σ₀ (x i)
  set L := ∑ i ∈ Finset.range n, (1 + log (1 + ξ₀ * x i / σ₀))
  set ℓ := gpdLogLikN θ.1 θ.2 x n
  set ℓ₀ := gpdLogLikN ξ₀ σ₀ x n
  have hL : 2 * (K * gpdDist ξ₀ σ₀ θ ^ 3 * L) = 2 * K * (r⁻¹ * ((r ^ 2)⁻¹ * L)) *
      (|r * (θ.1 - ξ₀)| + |r * (θ.2 - σ₀)|) ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos hr, gpdDist]
    field_simp
  rw [← hL]
  have e : 2 * (ℓ - ℓ₀) - (2 * (r * (θ.1 - ξ₀) * (r⁻¹ * A₁) + r * (θ.2 - σ₀) * (r⁻¹ * A₂)) -
      ((r * (θ.1 - ξ₀)) ^ 2 * ((r ^ 2)⁻¹ * H₁) +
        2 * (r * (θ.1 - ξ₀)) * (r * (θ.2 - σ₀)) * ((r ^ 2)⁻¹ * H₂) +
        (r * (θ.2 - σ₀)) ^ 2 * ((r ^ 2)⁻¹ * H₃))) =
      -(2 * (ℓ₀ - ℓ - ((ξ₀ - θ.1) * A₁ + (σ₀ - θ.2) * A₂) -
        ((ξ₀ - θ.1) ^ 2 * H₁ + 2 * (ξ₀ - θ.1) * (σ₀ - θ.2) * H₂ + (σ₀ - θ.2) ^ 2 * H₃) / 2)) := by
    field_simp
    ring
  rw [e, abs_neg, abs_mul, abs_two]
  gcongr

end Sample

/-! ### The almost sure limits -/

section Limits

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {ξ₀ σ₀ K : ℝ}

/-- The quadratic form `sᵀ I(ξ, σ)⁻¹ s = (1 + ξ) ((1 + ξ) s₁² - 2 σ s₁ s₂ + 2 σ² s₂²)` of the
inverse Fisher information. -/
noncomputable def gpdInfoInvQuad (ξ σ s₁ s₂ : ℝ) : ℝ :=
  (1 + ξ) * ((1 + ξ) * s₁ ^ 2 - 2 * σ * s₁ * s₂ + 2 * σ ^ 2 * s₂ ^ 2)

/-- The Fisher information is positive definite: `tᵀ I t > 0` for `ξ > -1/2`, `σ > 0`, `t ≠ 0`. -/
lemma gpdInfoQuad_pos {ξ σ t₁ t₂ : ℝ} (hξ : -1 / 2 < ξ) (hσ : 0 < σ) (ht : t₁ ≠ 0 ∨ t₂ ≠ 0) :
    0 < gpdInfoQuad ξ σ t₁ t₂ := by
  have h1 : 0 < 1 + ξ := by linarith
  have h2 : 0 < 1 + 2 * ξ := by linarith
  have e : gpdInfoQuad ξ σ t₁ t₂ =
      (2 * σ ^ 2 * t₁ ^ 2 + 2 * σ * t₁ * t₂ + (1 + ξ) * t₂ ^ 2) /
        (σ ^ 2 * (1 + ξ) * (1 + 2 * ξ)) := by
    unfold gpdInfoQuad
    field_simp
  rw [e]
  refine div_pos ?_ (by positivity)
  have hk : 2 * (2 * σ ^ 2 * t₁ ^ 2 + 2 * σ * t₁ * t₂ + (1 + ξ) * t₂ ^ 2) =
      (2 * σ * t₁ + t₂) ^ 2 + (1 + 2 * ξ) * t₂ ^ 2 := by ring
  rcases ht with ht | ht
  · have : 0 < (2 * σ * t₁ + t₂) ^ 2 + (1 + 2 * ξ) * t₂ ^ 2 := by
      by_cases h0 : t₂ = 0
      · subst h0
        have : 0 < (2 * σ * t₁) ^ 2 := by positivity
        simpa using this
      · have : 0 < (1 + 2 * ξ) * t₂ ^ 2 := by positivity
        nlinarith [sq_nonneg (2 * σ * t₁ + t₂)]
    linarith
  · have : 0 < (1 + 2 * ξ) * t₂ ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * σ * t₁ + t₂)]

omit [IsProbabilityMeasure P] in
/-- **The strong laws needed for Wilks' theorem**: almost surely the observations are nonnegative,
the empirical means of the Hessian at `θ₀` tend to `-I(θ₀)`, the scaled empirical mean of
`1 + log(1 + ξ₀ x/σ₀)` tends to `0`, and along every sequence `θₛ → θ₀` the empirical means of the
averaged segment Hessians tend to `-I(θ₀)`. -/
theorem ae_gpdWilks_limits (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀) (hK0 : 0 ≤ K)
    (hK : ∀ θ ∈ gpdNbhd ξ₀ σ₀, ∀ x, 0 ≤ x →
      |gpdHessXiXi θ.1 θ.2 x - gpdHessXiXi ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessXiSigma θ.1 θ.2 x - gpdHessXiSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)) ∧
      |gpdHessSigmaSigma θ.1 θ.2 x - gpdHessSigmaSigma ξ₀ σ₀ x| ≤
          K * gpdDist ξ₀ σ₀ θ * (1 + log (1 + ξ₀ * x / σ₀)))
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, (∀ i, 0 ≤ X i ω) ∧
      Tendsto (sampleAvg (gpdHessXiXi ξ₀ σ₀) fun i => X i ω) atTop
        (𝓝 (-(2 / ((1 + ξ₀) * (1 + 2 * ξ₀))))) ∧
      Tendsto (sampleAvg (gpdHessXiSigma ξ₀ σ₀) fun i => X i ω) atTop
        (𝓝 (-(1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀))))) ∧
      Tendsto (sampleAvg (gpdHessSigmaSigma ξ₀ σ₀) fun i => X i ω) atTop
        (𝓝 (-(1 / (σ₀ ^ 2 * (1 + 2 * ξ₀))))) ∧
      Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹ *
        sampleAvg (fun y => 1 + log (1 + ξ₀ * y / σ₀)) (fun i => X i ω) n) atTop (𝓝 0) ∧
      ∀ θs : ℕ → ℝ × ℝ, Tendsto θs atTop (𝓝 (ξ₀, σ₀)) →
        Tendsto (fun n => sampleAvg (segHess gpdHessXiXi ξ₀ σ₀ (θs n)) (fun i => X i ω) n) atTop
          (𝓝 (-(2 / ((1 + ξ₀) * (1 + 2 * ξ₀))))) ∧
        Tendsto (fun n => sampleAvg (segHess gpdHessXiSigma ξ₀ σ₀ (θs n)) (fun i => X i ω) n) atTop
          (𝓝 (-(1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀))))) ∧
        Tendsto (fun n => sampleAvg (segHess gpdHessSigmaSigma ξ₀ σ₀ (θs n)) (fun i => X i ω) n)
          atTop (𝓝 (-(1 / (σ₀ ^ 2 * (1 + 2 * ξ₀))))) := by
  have hξ : -1 / 2 < ξ₀ := by linarith
  have hξ0 : ξ₀ ≠ 0 := hξ₀.ne'
  have hL₀m : Measurable fun x : ℝ => log (1 + ξ₀ * x / σ₀) := by fun_prop
  have hL₀i : Integrable (fun x : ℝ => log (1 + ξ₀ * x / σ₀)) (gpdMeasure ξ₀ σ₀) :=
    integrable_gpdMeasure_of_poly hξ hL₀m 0 ξ₀ 0 0 0 0 fun t => by
      rw [log_one_add_mul_gpdTransform hσ₀ hξ0]; ring
  have hsL := ae_tendsto_avg_comp hX hind hL₀m hL₀i
  have hsL' := ae_tendsto_avg_comp hX hind (g := fun y => 1 + log (1 + ξ₀ * y / σ₀))
    (by fun_prop) ((integrable_const _).add hL₀i)
  have hs₁₁ := ae_tendsto_avg_comp hX hind (measurable_gpdHessXiXi ξ₀ σ₀)
    (integrable_gpdHessXiXi hσ₀ hξ0 hξ)
  have hs₁₂ := ae_tendsto_avg_comp hX hind (measurable_gpdHessXiSigma ξ₀ σ₀)
    (integrable_gpdHessXiSigma hσ₀ hξ0 hξ)
  have hs₂₂ := ae_tendsto_avg_comp hX hind (measurable_gpdHessSigmaSigma ξ₀ σ₀)
    (integrable_gpdHessSigmaSigma hσ₀ hξ0 hξ)
  rw [integral_gpdHessXiXi hσ₀ hξ0 hξ] at hs₁₁
  rw [integral_gpdHessXiSigma hσ₀ hξ0 hξ] at hs₁₂
  rw [integral_gpdHessSigmaSigma hσ₀ hξ0 hξ] at hs₂₂
  have hexp := fun {θ : ℝ × ℝ} (hθ : θ ∈ gpdNbhd ξ₀ σ₀) {x : ℝ} (hx : 0 ≤ x) =>
    gpdScore_sub_eq_segHess hξ₀ hσ₀ hK0 hK hθ hx
  have hr : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ae_forall_pos_of_gpd hσ₀ hX, hsL, hsL', hs₁₁, hs₁₂, hs₂₂]
    with ω hω hl hl' h₁₁ h₁₂ h₂₂
  have hx : ∀ i, 0 ≤ X i ω := fun i => (hω i).le
  refine ⟨hx, h₁₁, h₁₂, h₂₂, ?_, fun θs hθs => ⟨?_, ?_, ?_⟩⟩
  · simpa [sampleAvg] using hr.mul hl'
  · exact tendsto_avg_segHess hξ₀ hσ₀ (fun θ hθ x hx => (hexp hθ hx).2.2.1) hx hθs h₁₁ hl
  · exact tendsto_avg_segHess hξ₀ hσ₀ (fun θ hθ x hx => (hexp hθ hx).2.2.2.1) hx hθs h₁₂ hl
  · exact tendsto_avg_segHess hξ₀ hσ₀ (fun θ hθ x hx => (hexp hθ hx).2.2.2.2) hx hθs h₂₂ hl

/-- The normalized score in the shape is bounded in probability. -/
lemma isBoundedInProbability_gpdNormScoreXi (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) :
    IsBoundedInProbability P fun n ω => gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n := by
  simpa [gpdNormScoreXi] using
    isBoundedInProbability_lin_score (by linarith) hξ₀.ne' hσ₀ hX hind 1 0

/-- The normalized score in the scale is bounded in probability. -/
lemma isBoundedInProbability_gpdNormScoreSigma (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P) :
    IsBoundedInProbability P fun n ω => gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n := by
  simpa [gpdNormScoreSigma] using
    isBoundedInProbability_lin_score (by linarith) hξ₀.ne' hσ₀ hX hind 0 1

omit [IsProbabilityMeasure P] in
lemma aemeasurable_gpdNormScoreXi (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (n : ℕ) :
    AEMeasurable (fun ω => gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n) P := by
  have := measurable_gpdScoreXi ξ₀ σ₀
  unfold gpdNormScoreXi
  exact (Finset.aemeasurable_fun_sum _ fun i _ =>
    this.comp_aemeasurable (hX i).aemeasurable).const_mul _

omit [IsProbabilityMeasure P] in
lemma aemeasurable_gpdNormScoreSigma (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (n : ℕ) :
    AEMeasurable (fun ω => gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) P := by
  have := measurable_gpdScoreSigma ξ₀ σ₀
  unfold gpdNormScoreSigma
  exact (Finset.aemeasurable_fun_sum _ fun i _ =>
    this.comp_aemeasurable (hX i).aemeasurable).const_mul _

omit [IsProbabilityMeasure P] in
/-- The log-likelihood at a random parameter is a random variable. -/
lemma aemeasurable_gpdLogLikN (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P)
    {θ : Ω → ℝ × ℝ} (hθ : AEMeasurable θ P) (n : ℕ) :
    AEMeasurable (fun ω => gpdLogLikN (θ ω).1 (θ ω).2 (fun i => X i ω) n) P := by
  have hx : AEMeasurable (fun ω => (fun i => X i ω : ℕ → ℝ)) P :=
    aemeasurable_pi_iff.2 fun i => (hX i).aemeasurable
  exact (measurable_gpdLogLikN n).comp_aemeasurable (hθ.prodMk hx)

lemma quad_div_eq_of_div_eq {A B C d j₁₁ j₁₂ j₂₂ s₁ s₂ : ℝ} (h₁ : C / d = j₁₁)
    (h₂ : -B / d = j₁₂) (h₃ : A / d = j₂₂) :
    (C * s₁ ^ 2 - 2 * B * s₁ * s₂ + A * s₂ ^ 2) / d =
      j₁₁ * s₁ ^ 2 + 2 * j₁₂ * s₁ * s₂ + j₂₂ * s₂ ^ 2 := by
  subst h₁ h₂ h₃
  ring

/-- **The deviance is the score quadratic form, up to `o_P(1)`.** For measurable, strongly
consistent roots `θ̂ₙ` of the likelihood equations, `ξ₀ > 0`,
`2 (ℓₙ(θ̂ₙ) - ℓₙ(θ₀)) - Sₙᵀ I(θ₀)⁻¹ Sₙ → 0` in probability, where `Sₙ` is the normalized score at
`θ₀`. -/
theorem tendstoInMeasure_gpdDeviance_sub (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {θh : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hcons : ∀ᵐ ω ∂P, Tendsto (fun n => θh n ω) atTop (𝓝 (ξ₀, σ₀)))
    (hroot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (X i ω) = 0 ∧
      ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (X i ω) = 0) :
    TendstoInMeasure P (fun n ω =>
      2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n) -
        gpdInfoInvQuad ξ₀ σ₀ (gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n)
          (gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n)) atTop (fun _ => 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_gpdHess_lipschitz hξ₀ hσ₀
  have hξ : -1 / 2 < ξ₀ := by linarith
  obtain ⟨hd, hJ₁₁, hJ₁₂, hJ₂₂⟩ := gpdFisherInfo_det_adj hξ hσ₀
  have hS₁m := aemeasurable_gpdNormScoreXi (ξ₀ := ξ₀) (σ₀ := σ₀) hX
  have hS₂m := aemeasurable_gpdNormScoreSigma (ξ₀ := ξ₀) (σ₀ := σ₀) hX
  refine tendstoInMeasure_zero_of_ae_isLittleO
    (G := fun n ω => (1 + |gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n| +
      |gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n|) ^ 3) (fun n => ?_) (fun n => ?_)
    (isBoundedInProbability_cube (isBoundedInProbability_gpdNormScoreXi hξ₀ hσ₀ hX hind)
      (isBoundedInProbability_gpdNormScoreSigma hξ₀ hσ₀ hX hind)) ?_
  · have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
    have h2 := aemeasurable_gpdLogLikN (θ := fun _ => (ξ₀, σ₀)) hX aemeasurable_const n
    have h3 := hS₁m n; have h4 := hS₂m n
    simp only at h2
    unfold gpdInfoInvQuad
    fun_prop
  · have h3 := hS₁m n; have h4 := hS₂m n
    fun_prop
  filter_upwards [ae_gpdWilks_limits hξ₀ hσ₀ hK0 hK hX hind, hcons, hroot]
    with ω ⟨hx, h₁₁, h₁₂, h₂₂, hε, hB⟩ hc hr
  obtain ⟨hB₁₁, hB₁₂, hB₂₂⟩ := hB _ hc
  set x : ℕ → ℝ := fun i => X i ω
  have hnb := hc.eventually (gpdNbhd_mem_nhds hξ₀ hσ₀)
  have key := isLittleO_full_deviance
    (S₁ := gpdNormScoreXi ξ₀ σ₀ x) (S₂ := gpdNormScoreSigma ξ₀ σ₀ x)
    (T₁ := fun n => √(n : ℝ) * ((θh n ω).1 - ξ₀)) (T₂ := fun n => √(n : ℝ) * ((θh n ω).2 - σ₀))
    (D := fun n => 2 * (gpdLogLikN (θh n ω).1 (θh n ω).2 x n - gpdLogLikN ξ₀ σ₀ x n))
    (ε := fun n => 2 * K * ((√(n : ℝ))⁻¹ * sampleAvg (fun y => 1 + log (1 + ξ₀ * y / σ₀)) x n))
    hd hB₁₁ hB₁₂ hB₂₂ h₁₁ h₁₂ h₂₂ (by simpa using hε.const_mul (2 * K))
    ?_ ?_ ?_
  · refine key.congr_left fun n => ?_
    congr 1
    rw [gpdInfoInvQuad, quad_div_eq_of_div_eq hJ₁₁ hJ₁₂ hJ₂₂]
    ring
  · filter_upwards [hnb, hr, eventually_gt_atTop 0] with n hn hrn hn0
    have h := (gpdNormScore_eq hξ₀ hσ₀ hK0 hK hn hx hn0).1
    rw [gpdNormScoreXi, show ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (x i) = 0 from hrn.1,
      mul_zero] at h
    exact h.symm
  · filter_upwards [hnb, hr, eventually_gt_atTop 0] with n hn hrn hn0
    have h := (gpdNormScore_eq hξ₀ hσ₀ hK0 hK hn hx hn0).2
    rw [gpdNormScoreSigma, show ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (x i) = 0 from hrn.2,
      mul_zero] at h
    exact h.symm
  · filter_upwards [hnb, hr, eventually_gt_atTop 0] with n hn hrn hn0
    have h := abs_gpdDeviance_sub_le hξ₀ hσ₀ hK0 hK hn hx hn0
    rw [gpdNormScoreXi, gpdNormScoreSigma,
      show ∑ i ∈ Finset.range n, gpdScoreXi (θh n ω).1 (θh n ω).2 (x i) = 0 from hrn.1,
      show ∑ i ∈ Finset.range n, gpdScoreSigma (θh n ω).1 (θh n ω).2 (x i) = 0 from hrn.2] at h
    simpa using h

/-- **Asymptotics along a curve.** Let `γ = (γ₁, γ₂)` be a curve through `θ₀ = γ(s₀)`, with
`γ'(s) = (t₁(s), t₂(s))`, differentiable at `s₀`, with `t₁`, `t₂` continuous at `s₀`, and tangent
vector `t₀ = γ'(s₀) ≠ 0`. Let `θ̃ₙ` be measurable and such that almost surely `θ̃ₙ = γ(sₙ)` with
`sₙ → s₀` and the likelihood along the curve is stationary at `sₙ`: `γ'(sₙ) · ∇ℓₙ(θ̃ₙ) = 0`, for
all large `n`. Then

  `2 (ℓₙ(θ̃ₙ) - ℓₙ(θ₀)) - (t₀ · Sₙ)² / (t₀ᵀ I(θ₀) t₀) → 0` in probability. -/
theorem tendstoInMeasure_gpdCurveDeviance_sub (hξ₀ : 0 < ξ₀) (hσ₀ : 0 < σ₀)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ₀ σ₀) P) (hind : iIndepFun X P)
    {γ₁ γ₂ t₁ t₂ : ℝ → ℝ} {s₀ : ℝ} (hγ₁ : HasDerivAt γ₁ (t₁ s₀) s₀) (hγ₂ : HasDerivAt γ₂ (t₂ s₀) s₀)
    (ht₁ : ContinuousAt t₁ s₀) (ht₂ : ContinuousAt t₂ s₀) (hs₁ : γ₁ s₀ = ξ₀) (hs₂ : γ₂ s₀ = σ₀)
    (hne : t₁ s₀ ≠ 0 ∨ t₂ s₀ ≠ 0)
    {θt : ℕ → Ω → ℝ × ℝ} (hθm : ∀ n, AEMeasurable (θt n) P)
    (hcurve : ∀ᵐ ω ∂P, ∃ s : ℕ → ℝ, Tendsto s atTop (𝓝 s₀) ∧ ∀ᶠ n in atTop,
      θt n ω = (γ₁ (s n), γ₂ (s n)) ∧
      t₁ (s n) * ∑ i ∈ Finset.range n, gpdScoreXi (θt n ω).1 (θt n ω).2 (X i ω) +
        t₂ (s n) * ∑ i ∈ Finset.range n, gpdScoreSigma (θt n ω).1 (θt n ω).2 (X i ω) = 0) :
    TendstoInMeasure P (fun n ω =>
      2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 (fun i => X i ω) n -
          gpdLogLikN ξ₀ σ₀ (fun i => X i ω) n) -
        (t₁ s₀ * gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n +
          t₂ s₀ * gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n) ^ 2 /
            gpdInfoQuad ξ₀ σ₀ (t₁ s₀) (t₂ s₀)) atTop (fun _ => 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_gpdHess_lipschitz hξ₀ hσ₀
  have hξ : -1 / 2 < ξ₀ := by linarith
  have hS₁m := aemeasurable_gpdNormScoreXi (ξ₀ := ξ₀) (σ₀ := σ₀) hX
  have hS₂m := aemeasurable_gpdNormScoreSigma (ξ₀ := ξ₀) (σ₀ := σ₀) hX
  have hq : gpdInfoQuad ξ₀ σ₀ (t₁ s₀) (t₂ s₀) =
      2 / ((1 + ξ₀) * (1 + 2 * ξ₀)) * t₁ s₀ ^ 2 +
        2 * (1 / (σ₀ * (1 + ξ₀) * (1 + 2 * ξ₀))) * t₁ s₀ * t₂ s₀ +
        1 / (σ₀ ^ 2 * (1 + 2 * ξ₀)) * t₂ s₀ ^ 2 := by
    unfold gpdInfoQuad; ring
  have hc := gpdInfoQuad_pos hξ hσ₀ hne
  rw [hq] at hc
  refine tendstoInMeasure_zero_of_ae_isLittleO
    (G := fun n ω => (1 + |gpdNormScoreXi ξ₀ σ₀ (fun i => X i ω) n| +
      |gpdNormScoreSigma ξ₀ σ₀ (fun i => X i ω) n|) ^ 3) (fun n => ?_) (fun n => ?_)
    (isBoundedInProbability_cube (isBoundedInProbability_gpdNormScoreXi hξ₀ hσ₀ hX hind)
      (isBoundedInProbability_gpdNormScoreSigma hξ₀ hσ₀ hX hind)) ?_
  · have h1 := aemeasurable_gpdLogLikN hX (hθm n) n
    have h2 := aemeasurable_gpdLogLikN (θ := fun _ => (ξ₀, σ₀)) hX aemeasurable_const n
    have h3 := hS₁m n; have h4 := hS₂m n
    simp only at h2
    fun_prop
  · have h3 := hS₁m n; have h4 := hS₂m n
    fun_prop
  filter_upwards [ae_gpdWilks_limits hξ₀ hσ₀ hK0 hK hX hind, hcurve]
    with ω ⟨hx, h₁₁, h₁₂, h₂₂, hε, hB⟩ ⟨s, hs, hev⟩
  set x : ℕ → ℝ := fun i => X i ω
  -- the chords and the tangents
  have hsl₁ : Tendsto (fun n => dslope γ₁ s₀ (s n)) atTop (𝓝 (t₁ s₀)) := by
    have := (continuousAt_dslope_same.2 hγ₁.differentiableAt).tendsto.comp hs
    rwa [dslope_same, hγ₁.deriv] at this
  have hsl₂ : Tendsto (fun n => dslope γ₂ s₀ (s n)) atTop (𝓝 (t₂ s₀)) := by
    have := (continuousAt_dslope_same.2 hγ₂.differentiableAt).tendsto.comp hs
    rwa [dslope_same, hγ₂.deriv] at this
  have htn₁ : Tendsto (fun n => t₁ (s n)) atTop (𝓝 (t₁ s₀)) := ht₁.tendsto.comp hs
  have htn₂ : Tendsto (fun n => t₂ (s n)) atTop (𝓝 (t₂ s₀)) := ht₂.tendsto.comp hs
  have hc' : Tendsto (fun n => θt n ω) atTop (𝓝 (ξ₀, σ₀)) := by
    have h1 : Tendsto (fun n => (γ₁ (s n), γ₂ (s n))) atTop (𝓝 (ξ₀, σ₀)) := by
      rw [← hs₁, ← hs₂]
      exact (hγ₁.continuousAt.tendsto.comp hs).prodMk_nhds (hγ₂.continuousAt.tendsto.comp hs)
    exact h1.congr' (hev.mono fun n hn => hn.1.symm)
  obtain ⟨hB₁₁, hB₁₂, hB₂₂⟩ := hB _ hc'
  have hnb := hc'.eventually (gpdNbhd_mem_nhds hξ₀ hσ₀)
  -- the coordinates
  have hU : ∀ n, θt n ω = (γ₁ (s n), γ₂ (s n)) →
      √(n : ℝ) * ((θt n ω).1 - ξ₀) = √(n : ℝ) * (s n - s₀) * dslope γ₁ s₀ (s n) ∧
      √(n : ℝ) * ((θt n ω).2 - σ₀) = √(n : ℝ) * (s n - s₀) * dslope γ₂ s₀ (s n) := fun n hn => by
    have e₁ := sub_smul_dslope γ₁ s₀ (s n)
    have e₂ := sub_smul_dslope γ₂ s₀ (s n)
    simp only [smul_eq_mul, hs₁, hs₂] at e₁ e₂
    rw [hn]
    simp only
    rw [← e₁, ← e₂]
    constructor <;> ring
  have key := isLittleO_curve_deviance
    (S₁ := gpdNormScoreXi ξ₀ σ₀ x) (S₂ := gpdNormScoreSigma ξ₀ σ₀ x)
    (τ := fun n => √(n : ℝ) * (s n - s₀))
    (D := fun n => 2 * (gpdLogLikN (θt n ω).1 (θt n ω).2 x n - gpdLogLikN ξ₀ σ₀ x n))
    (ε := fun n => 2 * K * ((√(n : ℝ))⁻¹ * sampleAvg (fun y => 1 + log (1 + ξ₀ * y / σ₀)) x n))
    hc hsl₁ hsl₂ htn₁ htn₂ hB₁₁ hB₁₂ hB₂₂ h₁₁ h₁₂ h₂₂ (by simpa using hε.const_mul (2 * K))
    ?_ ?_
  · rw [← hq] at key
    exact key
  · filter_upwards [hnb, hev, eventually_gt_atTop 0] with n hn ⟨hγn, hrn⟩ hn0
    obtain ⟨hU₁, hU₂⟩ := hU n hγn
    obtain ⟨h₁, h₂⟩ := gpdNormScore_eq hξ₀ hσ₀ hK0 hK hn hx hn0
    rw [hU₁, hU₂] at h₁ h₂
    have h0 : t₁ (s n) * gpdNormScoreXi (θt n ω).1 (θt n ω).2 x n +
        t₂ (s n) * gpdNormScoreSigma (θt n ω).1 (θt n ω).2 x n = 0 := by
      simp only [gpdNormScoreXi, gpdNormScoreSigma]
      linear_combination (√(n : ℝ))⁻¹ * hrn
    rw [h₁, h₂] at h0
    linear_combination h0
  · filter_upwards [hnb, hev, eventually_gt_atTop 0] with n hn ⟨hγn, hrn⟩ hn0
    obtain ⟨hU₁, hU₂⟩ := hU n hγn
    obtain ⟨h₁, h₂⟩ := gpdNormScore_eq hξ₀ hσ₀ hK0 hK hn hx hn0
    have h := abs_gpdDeviance_sub_le hξ₀ hσ₀ hK0 hK hn hx hn0
    rw [h₁, h₂, hU₁, hU₂] at h
    convert h using 1
    · congr 1
      ring
    · simp only [abs_mul]
      ring

end Limits

end ExtremeValueTheory
