/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.HillNormality

/-!
# The intervals estimator of the extremal index (Ferro and Segers 2003)

Let `T_1, …, T_m` be the inter-exceedance times of a level `u` (the gaps between consecutive
exceedances among `N = m + 1` exceedances). Ferro and Segers (2003, Theorem 1) show that for a
stationary sequence with extremal index `θ ∈ (0, 1]` (under a mixing condition), the normalized
inter-exceedance time `F̄(uₙ) T` converges in law to the mixture
`(1 - θ) δ₀ + θ Exp(θ)`: with probability `1 - θ` the next exceedance is in the same cluster
(gap `o(1 / F̄(uₙ))`), otherwise the gap is exponential with mean `1 / θ`. The moments of this
limit are `E T = 1` and `E T² = 2 / θ`, so `θ = 2 (E T)² / E T²`: this is the population identity
behind the **intervals estimator**
`θ̂₁ = 2 (∑ T_i)² / (m ∑ T_i²)` (and its bias-corrected version
`θ̂₂ = 2 (∑ (T_i - 1))² / (m ∑ (T_i - 1)(T_i - 2))`, used when `max T_i > 2`).

## Main results

* `ferroSegersLaw θ = (1 - θ) δ₀ + θ Exp(θ)`, `isProbabilityMeasure_ferroSegersLaw`.
* `integral_pow_ferroSegersLaw`: `∫ x^j d(ferroSegersLaw θ) = θ · j! / θ^j` for `j ≥ 1`; in
  particular `integral_id_ferroSegersLaw` (`= 1`) and `integral_sq_ferroSegersLaw` (`= 2 / θ`).
* `ferroSegers_moment_ratio`: **the population identity** `2 (E T)² / E T² = θ`.
* `intervalsEstimator₁`, `intervalsEstimator₂`, `intervalsEstimator` (the combined rule,
  truncated at `1`), and `intervalsEstimator₁_smul`: `θ̂₁` is scale invariant, so it does not
  depend on the (unknown) normalization `F̄(uₙ)`.
* `tendstoInMeasure_intervalsEstimator₁`: **consistency of `θ̂₁` from the moments**: if the
  first two empirical moments of the normalized inter-exceedance times converge in probability to
  the moments `1` and `2 / θ` of the Ferro–Segers law, then `θ̂₁ → θ` in probability.

## Not formalized

The convergence in law of the normalized inter-exceedance times (Ferro–Segers Theorem 1) and the
laws of large numbers for the empirical moments (which need mixing and a truncation argument)
are not formalized here; they are the hypotheses of `tendstoInMeasure_intervalsEstimator₁`.

## References

* C. A. T. Ferro and J. Segers, *Inference for clusters of extreme values*, JRSS B 65 (2003).
* R. Kulik and P. Soulier, *Heavy-Tailed Time Series*, Springer (2020), Ch. 10.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

namespace ExtremeValueTheory

/-! ### The Ferro–Segers limit law -/

section Law

/-- **The Ferro–Segers law** `(1 - θ) δ₀ + θ Exp(θ)`, the limit law of the normalized
inter-exceedance times of a sequence with extremal index `θ` (Ferro and Segers 2003,
Theorem 1). `Exp(θ)` (mean `1 / θ`) is the image of the standard exponential law under
`x ↦ x / θ`. -/
noncomputable def ferroSegersLaw (θ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - θ) • Measure.dirac 0 + ENNReal.ofReal θ • (expMeasure 1).map (· / θ)

theorem isProbabilityMeasure_ferroSegersLaw {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    IsProbabilityMeasure (ferroSegersLaw θ) := by
  have := isProbabilityMeasure_expMeasure (r := 1) one_pos
  constructor
  rw [ferroSegersLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ,
    measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add (by linarith) hθ0.le]
  simp

/-- **Moments of the Ferro–Segers law**: `∫ x^j = θ · j! / θ^j` for `j ≥ 1`. -/
theorem integral_pow_ferroSegersLaw {θ : ℝ} (hθ0 : 0 < θ) {j : ℕ} (hj : 1 ≤ j) :
    ∫ x, x ^ j ∂(ferroSegersLaw θ) = θ * (Nat.factorial j / θ ^ j) := by
  have := isProbabilityMeasure_expMeasure (r := 1) one_pos
  have hmeas : Measurable fun x : ℝ => x / θ := by fun_prop
  have hint : Integrable (fun x : ℝ => x ^ j) ((expMeasure 1).map (· / θ)) := by
    rw [integrable_map_measure (by fun_prop) hmeas.aemeasurable]
    have := (integrable_pow_expMeasure j).div_const (θ ^ j)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [div_pow]
  have hdirac : Integrable (fun x : ℝ => x ^ j) (Measure.dirac 0) :=
    integrable_dirac (by simp)
  rw [ferroSegersLaw, integral_add_measure (hdirac.smul_measure ENNReal.ofReal_ne_top)
    (hint.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_map hmeas.aemeasurable (by fun_prop)]
  have : ∫ x, (x / θ) ^ j ∂(expMeasure 1) = Nat.factorial j / θ ^ j := by
    simp_rw [div_pow]
    rw [integral_div, integral_pow_expMeasure]
  rw [this, zero_pow (by omega), smul_zero, zero_add, ENNReal.toReal_ofReal hθ0.le, smul_eq_mul]

theorem integral_id_ferroSegersLaw {θ : ℝ} (hθ0 : 0 < θ) :
    ∫ x, x ∂(ferroSegersLaw θ) = 1 := by
  have := integral_pow_ferroSegersLaw hθ0 (j := 1) le_rfl
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at this
  rw [this]; field_simp

theorem integral_sq_ferroSegersLaw {θ : ℝ} (hθ0 : 0 < θ) :
    ∫ x, x ^ 2 ∂(ferroSegersLaw θ) = 2 / θ := by
  rw [integral_pow_ferroSegersLaw hθ0 (by norm_num)]
  simp only [Nat.factorial_two, Nat.cast_ofNat]
  field_simp

/-- **The population identity of the intervals estimator**: for the Ferro–Segers law,
`2 (E T)² / E T² = θ`. -/
theorem ferroSegers_moment_ratio {θ : ℝ} (hθ0 : 0 < θ) :
    2 * (∫ x, x ∂(ferroSegersLaw θ)) ^ 2 / ∫ x, x ^ 2 ∂(ferroSegersLaw θ) = θ := by
  rw [integral_id_ferroSegersLaw hθ0, integral_sq_ferroSegersLaw hθ0]
  field_simp

end Law

/-! ### The estimator -/

section Estimator

/-- The intervals estimator `θ̂₁ = 2 (∑ T_i)² / (m ∑ T_i²)` from `m` inter-exceedance times. -/
noncomputable def intervalsEstimator₁ {m : ℕ} (T : Fin m → ℝ) : ℝ :=
  2 * (∑ i, T i) ^ 2 / (m * ∑ i, T i ^ 2)

/-- The bias-corrected intervals estimator
`θ̂₂ = 2 (∑ (T_i - 1))² / (m ∑ (T_i - 1)(T_i - 2))` (Ferro–Segers 2003, for integer times). -/
noncomputable def intervalsEstimator₂ {m : ℕ} (T : Fin m → ℝ) : ℝ :=
  2 * (∑ i, (T i - 1)) ^ 2 / (m * ∑ i, (T i - 1) * (T i - 2))

/-- **The intervals estimator** of Ferro and Segers (2003): `min(1, θ̂₁)` if all inter-exceedance
times are at most `2`, `min(1, θ̂₂)` otherwise. -/
noncomputable def intervalsEstimator {m : ℕ} (T : Fin m → ℝ) : ℝ :=
  if ∀ i, T i ≤ 2 then min 1 (intervalsEstimator₁ T) else min 1 (intervalsEstimator₂ T)

/-- `θ̂₁` is scale invariant: it does not depend on the normalization of the times. -/
theorem intervalsEstimator₁_smul {m : ℕ} (T : Fin m → ℝ) {c : ℝ} (hc : c ≠ 0) :
    intervalsEstimator₁ (fun i => c * T i) = intervalsEstimator₁ T := by
  unfold intervalsEstimator₁
  simp_rw [mul_pow, ← Finset.mul_sum]
  rcases eq_or_ne (∑ i, T i ^ 2) 0 with h | h
  · simp [h]
  · rcases eq_or_ne (m : ℝ) 0 with hm | hm
    · simp [hm]
    · field_simp

/-- `θ̂₁` in terms of the empirical moments `M₁ = (1/m) ∑ T_i`, `M₂ = (1/m) ∑ T_i²`:
`θ̂₁ = 2 M₁² / M₂`. -/
theorem intervalsEstimator₁_eq {m : ℕ} (hm : 0 < m) (T : Fin m → ℝ) :
    intervalsEstimator₁ T = 2 * ((∑ i, T i) / m) ^ 2 / ((∑ i, T i ^ 2) / m) := by
  unfold intervalsEstimator₁
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rcases eq_or_ne (∑ i, T i ^ 2) 0 with h | h
  · simp [h]
  · field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Consistency of the intervals estimator from the moments.** Let `m n → ∞` (or just
`m n > 0` eventually) inter-exceedance times `T n i` be observed, and let `c n ≠ 0` be any
normalization (e.g. `F̄(uₙ)`). If the empirical first and second moments of the normalized
times `c n T n i` converge in probability to the moments `1` and `2 / θ` of the Ferro–Segers law,
then `θ̂₁ → θ` in probability. -/
theorem tendstoInMeasure_intervalsEstimator₁ {m : ℕ → ℕ} (hm : ∀ᶠ n in atTop, 0 < m n)
    {T : (n : ℕ) → Ω → Fin (m n) → ℝ} {c : ℕ → ℝ} (hc : ∀ᶠ n in atTop, c n ≠ 0)
    {θ : ℝ} (hθ0 : 0 < θ)
    (h1 : TendstoInMeasure P (fun n ω => (∑ i, c n * T n ω i) / m n) atTop
      (fun _ => ∫ x, x ∂(ferroSegersLaw θ)))
    (h2 : TendstoInMeasure P (fun n ω => (∑ i, (c n * T n ω i) ^ 2) / m n) atTop
      (fun _ => ∫ x, x ^ 2 ∂(ferroSegersLaw θ))) :
    TendstoInMeasure P (fun n ω => intervalsEstimator₁ (T n ω)) atTop (fun _ => θ) := by
  have hφ : ContinuousAt (fun q : ℝ × ℝ => 2 * q.1 ^ 2 / q.2)
      ((∫ x, x ∂(ferroSegersLaw θ)), ∫ x, x ^ 2 ∂(ferroSegersLaw θ)) := by
    refine ((continuousAt_fst.pow 2).const_mul 2).div continuousAt_snd ?_
    rw [integral_sq_ferroSegersLaw hθ0]
    positivity
  have h := tendstoInMeasure_comp₂ h1 h2 hφ
  simp only [ferroSegers_moment_ratio hθ0] at h
  refine tendstoInMeasure_of_eventuallyEq h ?_
  filter_upwards [hm, hc] with n hmn hcn ω
  rw [← intervalsEstimator₁_smul (T n ω) hcn, intervalsEstimator₁_eq hmn]

end Estimator

end ExtremeValueTheory
