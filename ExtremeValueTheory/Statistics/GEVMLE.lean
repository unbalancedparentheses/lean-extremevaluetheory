/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVLikelihood
import ExtremeValueTheory.Statistics.GPDJointMLE

/-!
# Consistency of the GEV maximum likelihood estimator, all shapes `ξ > -1`

The support `{1 + ξ (x - μ)/σ > 0}` of the location-scale GEV law depends on all three
parameters, so the log-likelihood must take the value `-∞` at parameters under which an
observation is impossible. We work with the **extended-real log-density**
`gevLogDensityE ξ μ σ x = log(σ⁻¹ h_ξ((x - μ)/σ)) ∈ [-∞, ∞)` (the `ENNReal` logarithm of the
density, `-∞` exactly where the density vanishes) and the extended-real log-likelihood
`gevLogLikE`. Its real part is the real log-density (`toReal_gevLogDensityE`), and on admissible
data it is the real log-likelihood `gevLogLik` (`gevLogLikE_eq_coe`).

## Main results

* `ExtremeValueTheory.gevDensity_eq_exp`: the GEV density uniformly in the shape,
  `h_ξ(z) = exp(-(1 + ξ) s - e^{-s})` with `s = z λ(ξ z) = log(1 + ξ z)/ξ` (`s = z` for `ξ = 0`),
  `λ(t) = log(1 + t)/t` (`log1pDiv`).
* `ExtremeValueTheory.continuousAt_gevDensity`: `(ξ, z) ↦ h_ξ(z)` is continuous on `{ξ > -1}`,
  across `ξ = 0` and across the endpoint `z = -1/ξ` of the support, where the density tends to
  `0` (for `-1 < ξ < 0` because the exponent `-1/ξ - 1` is positive, for `ξ > 0` because
  `t^{1 + ξ} e^{-t} → 0` as `t = (1 + ξ z)^{-1/ξ} → ∞`).
* `ExtremeValueTheory.continuousOn_gevLogDensityE`: `(ξ, μ, σ) ↦ gevLogDensityE ξ μ σ x` is
  continuous (as an `EReal`-valued map) on `{ξ > -1, σ > 0}`.
* `ExtremeValueTheory.gevLogDensityE_le`: the upper envelope
  `log(σ⁻¹ h_ξ(z)) ≤ -log σ + (1 + ξ)²` for `ξ > -1`.
* `ExtremeValueTheory.measure_gevLocScaleCDF_eq_withDensity`: the location-scale GEV law has
  density `σ⁻¹ h_ξ((x - μ)/σ)`; `measure_gevLocScaleCDF_eq_map`: it is the law of
  `μ + σ (T^{-ξ} - 1)/ξ` for a standard exponential `T`.
* `ExtremeValueTheory.gev_params_eq_of_measure_eq`: **identifiability** of the three-parameter
  GEV family: near `μ` both laws have `-log(-log F)` with derivative `1/(σ + ξ (x - μ))`.
* `ExtremeValueTheory.integral_log_gevLocScaleDensity_lt`: the Kullback–Leibler inequality.
* `ExtremeValueTheory.ae_tendsto_gevMLE`: **strong consistency of the GEV MLE** on a compact
  parameter set `K ⊂ {ξ > -1, σ > 0}` (Smith 1985; Bücher–Segers 2017), via the extended-real
  Wald theorem. Maximizers exist (`exists_isMaxOn_gevLogLikE`).

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
* A. Bücher and J. Segers, *On the maximum likelihood estimator for the Generalized Extreme-Value
  distribution*, Extremes 20 (2017).
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001), §3.3.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExtremeValueTheory

/-! ### The density uniformly in the shape, and its continuity -/

section Continuity

variable {ξ z : ℝ}

/-- For `ξ ≠ 0` inside the support, `z λ(ξ z) = log(1 + ξ z)/ξ`. -/
lemma mul_log1pDiv_eq (hξ : ξ ≠ 0) (hu : 0 < 1 + ξ * z) :
    z * log1pDiv (ξ * z) = log (1 + ξ * z) / ξ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [log1pDiv_of_ne (mul_ne_zero hξ hz)]
    field_simp

/-- **The GEV density, uniformly in the shape**: inside the support,
`h_ξ(z) = exp(-(1 + ξ) s - e^{-s})` with `s = z λ(ξ z)` (`= log(1 + ξ z)/ξ`, `= z` for
`ξ = 0`). -/
theorem gevDensity_eq_exp (hu : 0 < 1 + ξ * z) :
    gevDensity ξ z =
      exp (-(1 + ξ) * (z * log1pDiv (ξ * z)) - exp (-(z * log1pDiv (ξ * z)))) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp only [gevDensity, ↓reduceIte, zero_mul, log1pDiv_zero, mul_one, add_zero, ← exp_add]
    congr 1
    ring
  · rw [mul_log1pDiv_eq hξ hu]
    simp only [gevDensity, hξ, hu, ↓reduceIte]
    rw [rpow_def_of_pos hu, rpow_def_of_pos hu, ← exp_add,
      show log (1 + ξ * z) * (-1 / ξ) = -(log (1 + ξ * z) / ξ) by ring]
    congr 1
    field_simp
    ring

private lemma continuousAt_gevDensity_formula {q : ℝ × ℝ} (hq : -1 < q.1 * q.2) :
    ContinuousAt (fun q : ℝ × ℝ => exp (-(1 + q.1) * (q.2 * log1pDiv (q.1 * q.2)) -
      exp (-(q.2 * log1pDiv (q.1 * q.2))))) q := by
  have hs : ContinuousAt (fun q : ℝ × ℝ => q.2 * log1pDiv (q.1 * q.2)) q :=
    continuous_snd.continuousAt.mul
      ((continuousAt_log1pDiv hq).comp (f := fun q : ℝ × ℝ => q.1 * q.2) (by fun_prop))
  exact (((continuousAt_const.add continuous_fst.continuousAt).neg.mul hs).sub
    hs.neg.rexp).rexp

/-- Near the endpoint for `ξ > 0`: with `t = u^{-1/ξ} ≥ 1`,
`u^{-1/ξ - 1} e^{-u^{-1/ξ}} = t^{1 + ξ} e^{-t} ≤ n! t⁻¹ = n! u^{1/ξ}`. -/
private lemma rpow_mul_exp_le {ξ u : ℝ} {n : ℕ} (hξ : 0 < ξ) (hu : 0 < u) (hu1 : u ≤ 1)
    (hn : ξ + 2 ≤ n) :
    u ^ (-1 / ξ - 1) * exp (-u ^ (-1 / ξ)) ≤ n.factorial * u ^ (1 / ξ) := by
  have e1 : u ^ (-1 / ξ - 1) = (u ^ (-1 / ξ)) ^ (1 + ξ) := by
    rw [← rpow_mul hu.le]; congr 1; field_simp; ring
  have e2 : u ^ (1 / ξ) = (u ^ (-1 / ξ))⁻¹ := by
    rw [← rpow_neg_one, ← rpow_mul hu.le]; congr 1; ring
  rw [e1, e2]
  set t := u ^ (-1 / ξ) with ht
  have ht0 : 0 < t := rpow_pos_of_pos hu _
  have ht1 : 1 ≤ t := one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1
    (by rw [neg_div]; exact neg_nonpos.2 (by positivity))
  have h3 : t ^ (1 + ξ) * t = t ^ (ξ + 2) := by
    rw [← rpow_add_one ht0.ne']; congr 1; ring
  have h4 : t ^ (ξ + 2) ≤ t ^ n := by
    rw [← rpow_natCast]; exact rpow_le_rpow_of_exponent_le ht1 hn
  have h5 : t ^ n ≤ n.factorial * exp t := by
    have := pow_div_factorial_le_exp t ht0.le n
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  rw [le_mul_inv_iff₀ ht0, mul_right_comm, h3, exp_neg, mul_inv_le_iff₀ (exp_pos t)]
  linarith

/-- **Continuity of the GEV density in the shape and the argument**: `(ξ, z) ↦ h_ξ(z)` is
continuous at every point with `ξ > -1`, including `ξ = 0` and the endpoint `1 + ξ z = 0` of the
support. -/
theorem continuousAt_gevDensity {q : ℝ × ℝ} (hq : -1 < q.1) :
    ContinuousAt (fun q : ℝ × ℝ => gevDensity q.1 q.2) q := by
  have hcu : Continuous fun q : ℝ × ℝ => 1 + q.1 * q.2 := by fun_prop
  rcases lt_trichotomy (1 + q.1 * q.2) 0 with hneg | hzero | hpos
  · -- outside the support the density vanishes near `q`
    have hξ : q.1 ≠ 0 := fun h => by rw [h, zero_mul, add_zero] at hneg; linarith
    have hev : (fun _ : ℝ × ℝ => (0 : ℝ)) =ᶠ[𝓝 q] fun q => gevDensity q.1 q.2 := by
      filter_upwards [hcu.continuousAt.eventually (gt_mem_nhds hneg),
        continuous_fst.continuousAt.eventually (isOpen_ne.mem_nhds hξ)] with p hp hp1
      simp [gevDensity, hp1, not_lt.2 hp.le]
    exact continuousAt_const.congr hev
  · -- the endpoint of the support: squeeze
    have hξ : q.1 ≠ 0 := fun h => by rw [h, zero_mul, add_zero] at hzero; linarith
    have hval : gevDensity q.1 q.2 = 0 := by simp [gevDensity, hξ, hzero]
    have hmax : ContinuousAt (fun p : ℝ × ℝ => max (1 + p.1 * p.2) 0) q :=
      (hcu.max continuous_const).continuousAt
    rw [ContinuousAt, hval]
    rcases lt_or_gt_of_ne hξ with hξn | hξp
    · -- `-1 < ξ < 0`: `h_ξ(z) ≤ (1 + ξ z)₊ ^ (-1/ξ - 1)`, a positive power
      have he : 0 < -1 / q.1 - 1 := by
        have : 1 < -1 / q.1 := by rw [lt_div_iff_of_neg hξn]; linarith
        linarith
      have hg : Tendsto (fun p : ℝ × ℝ => (max (1 + p.1 * p.2) 0) ^ (-1 / p.1 - 1)) (𝓝 q)
          (𝓝 0) := by
        have hc : ContinuousAt (fun p : ℝ × ℝ => (max (1 + p.1 * p.2) 0) ^ (-1 / p.1 - 1)) q :=
          hmax.rpow ((continuousAt_const.div continuous_fst.continuousAt hξ).sub
            continuousAt_const) (Or.inr he)
        have h0 : (max (1 + q.1 * q.2) 0) ^ (-1 / q.1 - 1) = 0 := by
          rw [hzero, max_self, zero_rpow he.ne']
        have := hc.tendsto
        simp only [h0] at this
        exact this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
        (Eventually.of_forall fun p => gevDensity_nonneg _ _) ?_
      filter_upwards [continuous_fst.continuousAt.eventually (gt_mem_nhds hξn)] with p hp
      simp only [gevDensity, hp.ne, ↓reduceIte]
      split_ifs with hu
      · rw [max_eq_left hu.le]
        exact mul_le_of_le_one_right (rpow_nonneg hu.le _)
          (exp_le_one_iff.2 (neg_nonpos.2 (rpow_nonneg hu.le _)))
      · exact rpow_nonneg (le_max_right _ _) _
    · -- `ξ > 0`: `h_ξ(z) ≤ n! (1 + ξ z)₊ ^ (1/ξ)` near the endpoint
      obtain ⟨n, hn⟩ := exists_nat_gt (2 * q.1 + 2)
      have he : 0 < 1 / q.1 := by positivity
      have hg : Tendsto (fun p : ℝ × ℝ => (n.factorial : ℝ) * (max (1 + p.1 * p.2) 0) ^ (1 / p.1))
          (𝓝 q) (𝓝 0) := by
        have hc : ContinuousAt (fun p : ℝ × ℝ =>
            (n.factorial : ℝ) * (max (1 + p.1 * p.2) 0) ^ (1 / p.1)) q :=
          continuousAt_const.mul (hmax.rpow (continuousAt_const.div continuous_fst.continuousAt
            hξ) (Or.inr he))
        have h0 : (n.factorial : ℝ) * (max (1 + q.1 * q.2) 0) ^ (1 / q.1) = 0 := by
          rw [hzero, max_self, zero_rpow he.ne', mul_zero]
        have := hc.tendsto
        simp only [h0] at this
        exact this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
        (Eventually.of_forall fun p => gevDensity_nonneg _ _) ?_
      filter_upwards [continuous_fst.continuousAt.eventually (lt_mem_nhds hξp),
        continuous_fst.continuousAt.eventually (gt_mem_nhds (show q.1 < 2 * q.1 by linarith)),
        hcu.continuousAt.eventually (gt_mem_nhds (show 1 + q.1 * q.2 < 1 by linarith))]
        with p hp0 hp2 hp1
      simp only [gevDensity, hp0.ne', ↓reduceIte]
      split_ifs with hu
      · rw [max_eq_left hu.le]
        exact rpow_mul_exp_le hp0 hu hp1.le (by linarith)
      · positivity
  · -- inside the support: the uniform formula
    have hev : (fun q : ℝ × ℝ => exp (-(1 + q.1) * (q.2 * log1pDiv (q.1 * q.2)) -
        exp (-(q.2 * log1pDiv (q.1 * q.2))))) =ᶠ[𝓝 q] fun q => gevDensity q.1 q.2 := by
      filter_upwards [hcu.continuousAt.eventually (lt_mem_nhds hpos)] with p hp
      rw [gevDensity_eq_exp hp]
    exact (continuousAt_gevDensity_formula (by linarith)).congr hev

/-- `-a s - e^{-s} ≤ a²` for `a > 0` (the maximum is `a log a - a`). -/
lemma neg_mul_sub_exp_neg_le {a s : ℝ} (ha : 0 < a) : -a * s - exp (-s) ≤ a ^ 2 := by
  have h1 : (-s - log a + 1) * a ≤ exp (-s) := by
    have := add_one_le_exp (-s - log a)
    rw [exp_sub, exp_log ha, le_div_iff₀ ha] at this
    exact this
  have h2 := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos ha) ha.le
  nlinarith

/-- **Upper bound for the GEV density**: `h_ξ(z) ≤ exp((1 + ξ)²)` for `ξ > -1`. -/
theorem gevDensity_le (hξ : -1 < ξ) (z : ℝ) : gevDensity ξ z ≤ exp ((1 + ξ) ^ 2) := by
  by_cases hu : 0 < 1 + ξ * z
  · rw [gevDensity_eq_exp hu]
    exact exp_le_exp.2 (neg_mul_sub_exp_neg_le (by linarith))
  · have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hu
    simp only [gevDensity, hξ0, hu, ↓reduceIte]
    positivity

end Continuity

/-! ### The extended-real log-density -/

section LogDensityE

variable {ξ μ σ x : ℝ}

lemma gevLocScaleDensity_nonneg (hσ : 0 < σ) : 0 ≤ gevLocScaleDensity ξ μ σ x :=
  mul_nonneg (inv_nonneg.2 hσ.le) (gevDensity_nonneg _ _)

lemma measurable_gevLocScaleDensity (ξ μ σ : ℝ) : Measurable (gevLocScaleDensity ξ μ σ) :=
  measurable_const.mul ((measurable_gevDensity ξ).comp (by fun_prop))

/-- The **extended-real GEV log-density** `log(σ⁻¹ h_ξ((x - μ)/σ)) ∈ [-∞, ∞)`, equal to `-∞`
exactly where the density vanishes (off the support). -/
noncomputable def gevLogDensityE (ξ μ σ x : ℝ) : EReal :=
  ENNReal.log (ENNReal.ofReal (gevLocScaleDensity ξ μ σ x))

/-- The **extended-real GEV log-likelihood** `∑ᵢ log(σ⁻¹ h_ξ((xᵢ - μ)/σ)) ∈ [-∞, ∞)`. -/
noncomputable def gevLogLikE {n : ℕ} (ξ μ σ : ℝ) (x : Fin n → ℝ) : EReal :=
  ∑ i, gevLogDensityE ξ μ σ (x i)

lemma gevLogDensityE_of_pos (h : 0 < gevLocScaleDensity ξ μ σ x) :
    gevLogDensityE ξ μ σ x = ((log (gevLocScaleDensity ξ μ σ x) : ℝ) : EReal) :=
  ENNReal.log_ofReal_of_pos h

lemma toReal_gevLogDensityE (hσ : 0 < σ) :
    (gevLogDensityE ξ μ σ x).toReal = log (gevLocScaleDensity ξ μ σ x) := by
  rcases (gevLocScaleDensity_nonneg hσ (ξ := ξ) (μ := μ) (x := x)).eq_or_lt with h | h
  · rw [gevLogDensityE, ← h]; simp
  · rw [gevLogDensityE_of_pos h, EReal.toReal_coe]

lemma gevLogDensityE_ne_bot_iff :
    gevLogDensityE ξ μ σ x ≠ ⊥ ↔ 0 < gevLocScaleDensity ξ μ σ x := by
  simp [gevLogDensityE]

lemma measurable_gevLogDensityE (ξ μ σ : ℝ) : Measurable (gevLogDensityE ξ μ σ) :=
  (measurable_gevLocScaleDensity ξ μ σ).ennreal_ofReal.ennreal_log

/-- On admissible data (every density positive) the extended-real log-likelihood is the real
log-likelihood `gevLogLik`. -/
lemma gevLogLikE_eq_coe {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < gevLocScaleDensity ξ μ σ (x i)) :
    gevLogLikE ξ μ σ x = ((gevLogLik ξ μ σ x : ℝ) : EReal) := by
  rw [gevLogLik, EReal.coe_finsetSum]
  exact Finset.sum_congr rfl fun i _ => gevLogDensityE_of_pos (hx i)

/-- The parameter set `{(ξ, μ, σ) : ξ > -1, σ > 0}`. -/
def gevParamSet : Set (ℝ × ℝ × ℝ) := {p | -1 < p.1 ∧ 0 < p.2.2}

/-- The location-scale density is continuous in `(ξ, μ, σ)` on `{ξ > -1, σ > 0}`. -/
theorem continuousOn_gevLocScaleDensity (x : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => gevLocScaleDensity p.1 p.2.1 p.2.2 x) gevParamSet := by
  intro p hp
  have hσ : p.2.2 ≠ 0 := hp.2.ne'
  have hz : ContinuousAt (fun p : ℝ × ℝ × ℝ => (p.1, (x - p.2.1) / p.2.2)) p :=
    continuous_fst.continuousAt.prodMk ((continuousAt_const.sub
      (continuous_fst.comp continuous_snd).continuousAt).div
        (continuous_snd.comp continuous_snd).continuousAt hσ)
  have hd : ContinuousAt (fun p : ℝ × ℝ × ℝ => gevDensity p.1 ((x - p.2.1) / p.2.2)) p :=
    ContinuousAt.comp (g := fun q : ℝ × ℝ => gevDensity q.1 q.2)
      (f := fun p : ℝ × ℝ × ℝ => (p.1, (x - p.2.1) / p.2.2))
      (continuousAt_gevDensity (q := (p.1, (x - p.2.1) / p.2.2)) hp.1) hz
  exact (((continuous_snd.comp continuous_snd).continuousAt.inv₀ hσ).mul hd).continuousWithinAt

/-- **Continuity of the extended-real GEV log-density in the parameters**: for every `x`,
`(ξ, μ, σ) ↦ gevLogDensityE ξ μ σ x ∈ [-∞, ∞)` is continuous on `{ξ > -1, σ > 0}`, across
`ξ = 0` and across the boundary of the support (where it tends to `-∞`). -/
theorem continuousOn_gevLogDensityE (x : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => gevLogDensityE p.1 p.2.1 p.2.2 x) gevParamSet :=
  ENNReal.continuous_log.comp_continuousOn
    (ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_gevLocScaleDensity x))

/-- **Upper envelope**: for `ξ > -1` and `σ > 0`, `log(σ⁻¹ h_ξ(z)) ≤ -log σ + (1 + ξ)²`. -/
theorem gevLogDensityE_le (hξ : -1 < ξ) (hσ : 0 < σ) (x : ℝ) :
    gevLogDensityE ξ μ σ x ≤ ((-log σ + (1 + ξ) ^ 2 : ℝ) : EReal) := by
  have hb : gevLocScaleDensity ξ μ σ x ≤ σ⁻¹ * exp ((1 + ξ) ^ 2) :=
    mul_le_mul_of_nonneg_left (gevDensity_le hξ _) (inv_nonneg.2 hσ.le)
  have hpos : 0 < σ⁻¹ * exp ((1 + ξ) ^ 2) := by positivity
  calc gevLogDensityE ξ μ σ x ≤ ENNReal.log (ENNReal.ofReal (σ⁻¹ * exp ((1 + ξ) ^ 2))) :=
        ENNReal.log_le_log (ENNReal.ofReal_le_ofReal hb)
    _ = _ := by
        rw [ENNReal.log_ofReal_of_pos hpos, log_mul (inv_pos.2 hσ).ne' (exp_pos _).ne', log_inv,
          log_exp]

end LogDensityE

/-! ### The location-scale law -/

section Law

variable {ξ μ σ : ℝ}

/-- **The location-scale GEV law has density** `σ⁻¹ h_ξ((x - μ)/σ)`. -/
theorem measure_gevLocScaleCDF_eq_withDensity (ξ μ : ℝ) (hσ : 0 < σ) :
    (gevLocScaleCDF ξ μ hσ).measure =
      volume.withDensity (fun x => ENNReal.ofReal (gevLocScaleDensity ξ μ σ x)) := by
  have hF : (fun x => gevFun ξ ((x - μ) / σ)) = ⇑(gevLocScaleCDF ξ μ hσ) :=
    funext fun x => (gevLocScaleCDF_apply ξ μ hσ x).symm
  refine eq_withDensity_of_hasDerivAt_off (F := fun x => gevFun ξ ((x - μ) / σ))
    (c₁ := μ + σ * (-1 / ξ)) (c₂ := μ + σ * (-1 / ξ))
    ((continuous_gevFun ξ).comp (by fun_prop)) ?_ (fun x => ?_) (fun x h _ => ?_)
    (fun x => gevLocScaleDensity_nonneg hσ)
  · rw [hF]; exact (gevLocScaleCDF ξ μ hσ).tendsto_atBot
  · rw [CumulativeDistributionFunction.measure_Iic, gevLocScaleCDF_apply]
  · have hd : HasDerivAt (fun y => (y - μ) / σ) σ⁻¹ x := by
      simpa using ((hasDerivAt_id x).sub_const μ).div_const σ
    have hx : 1 + ξ * ((x - μ) / σ) ≠ 0 ∨ ξ = 0 := by
      by_cases hξ : ξ = 0
      · exact Or.inr hξ
      · refine Or.inl fun h0 => h ?_
        have : ξ * (x - μ) = -σ := by
          field_simp at h0
          linarith
        field_simp
        linarith
    have := (hasDerivAt_gevFun hx).comp x hd
    rw [gevLocScaleDensity, mul_comm]
    exact this

/-- **Exponential representation of the location-scale GEV law**: it is the law of
`μ + σ (T^{-ξ} - 1)/ξ` (of `μ - σ log T` for `ξ = 0`) for a standard exponential `T`. -/
theorem measure_gevLocScaleCDF_eq_map (ξ μ : ℝ) (hσ : 0 < σ) :
    (gevLocScaleCDF ξ μ hσ).measure =
      stdExpMeasure.map (fun t => μ + σ * gevTransform ξ t) := by
  rw [gevLocScaleCDF, CumulativeDistributionFunction.measure_smul_eq_map, measure_gevCDF_eq_map,
    Measure.map_map (by fun_prop) (measurable_gevTransform ξ)]
  congr 1
  funext t
  simp only [Function.comp_apply, AffineIncrEquiv.coefs_fst_mkOfCoefs,
    AffineIncrEquiv.coefs_snd_mkOfCoefs]
  ring

lemma one_add_mul_gevTransform (hξ : ξ ≠ 0) {t : ℝ} (_ht : 0 < t) :
    1 + ξ * gevTransform ξ t = t ^ (-ξ) := by
  simp only [gevTransform, hξ, ↓reduceIte]
  field_simp
  ring

lemma one_add_mul_gevTransform_pos {t : ℝ} (ht : 0 < t) : 0 < 1 + ξ * gevTransform ξ t := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · rw [one_add_mul_gevTransform hξ ht]; exact rpow_pos_of_pos ht _

/-- On the exponential scale, `s = z λ(ξ z) = -log t` at `z = (t^{-ξ} - 1)/ξ`. -/
lemma gevTransform_mul_log1pDiv {t : ℝ} (ht : 0 < t) :
    gevTransform ξ t * log1pDiv (ξ * gevTransform ξ t) = -log t := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [gevTransform, log1pDiv_zero]
  · rw [mul_log1pDiv_eq hξ (one_add_mul_gevTransform_pos ht), one_add_mul_gevTransform hξ ht,
      log_rpow ht]
    field_simp

/-- The log-density at the true parameter, on the exponential scale:
`log(σ⁻¹ h_ξ(z)) = -log σ + (1 + ξ) log t - t` at `x = μ + σ (t^{-ξ} - 1)/ξ`. -/
lemma log_gevLocScaleDensity_transform (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    log (gevLocScaleDensity ξ μ σ (μ + σ * gevTransform ξ t)) =
      -log σ + (1 + ξ) * log t - t := by
  have hz : (μ + σ * gevTransform ξ t - μ) / σ = gevTransform ξ t := by
    field_simp; ring
  rw [gevLocScaleDensity, hz, gevDensity_eq_exp (one_add_mul_gevTransform_pos ht),
    gevTransform_mul_log1pDiv ht, log_mul (inv_pos.2 hσ).ne' (exp_pos _).ne', log_inv, log_exp,
    neg_neg, exp_log ht]
  ring

lemma integrable_stdExpMeasure_iff {f : ℝ → ℝ} (_hf : Measurable f) :
    Integrable f stdExpMeasure ↔ IntegrableOn (fun t => exp (-t) * f t) (Ioi 0) := by
  rw [stdExpMeasure, integrable_withDensity_iff (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), IntegrableOn]
  refine integrable_congr (ae_of_all _ fun t => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (exp_pos _).le, mul_comm]

/-- `∫_0^∞ e^{-t} t^a dt` converges for `a > -1`. -/
lemma integrableOn_exp_neg_mul_rpow {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun t => exp (-t) * t ^ a) (Ioi 0) := by
  have := GammaIntegral_convergent (show 0 < a + 1 by linarith)
  simpa using this

/-- At the true parameter, the log-density is integrable. -/
lemma integrable_log_gevLocScaleDensity_self (hσ : 0 < σ) :
    Integrable (fun x => log (gevLocScaleDensity ξ μ σ x)) (gevLocScaleCDF ξ μ hσ).measure := by
  have hm : Measurable fun x => log (gevLocScaleDensity ξ μ σ x) :=
    (measurable_gevLocScaleDensity ξ μ σ).log
  have hT : Measurable fun t => μ + σ * gevTransform ξ t :=
    measurable_const.add (measurable_const.mul (measurable_gevTransform ξ))
  rw [measure_gevLocScaleCDF_eq_map, integrable_map_measure hm.aestronglyMeasurable
    hT.aemeasurable, integrable_stdExpMeasure_iff (hm.comp hT)]
  have h1 : IntegrableOn (fun t => exp (-t) * t ^ (0 : ℝ)) (Ioi 0) :=
    integrableOn_exp_neg_mul_rpow (by norm_num)
  have h2 : IntegrableOn (fun t => exp (-t) * t ^ (1 : ℝ)) (Ioi 0) :=
    integrableOn_exp_neg_mul_rpow (by norm_num)
  have h3 := integrableOn_log_mul_exp_neg
  refine IntegrableOn.congr_fun (((h1.const_mul (-log σ)).add (h3.const_mul (1 + ξ))).sub h2)
    (fun t ht => ?_) measurableSet_Ioi
  simp only [Function.comp_apply, rpow_zero, rpow_one, Pi.add_apply, Pi.sub_apply]
  rw [log_gevLocScaleDensity_transform hσ ht]
  ring

/-- At the true parameter, the extended-real log-density is a.s. finite. -/
lemma ae_gevLogDensityE_ne_bot (hσ : 0 < σ) :
    ∀ᵐ x ∂(gevLocScaleCDF ξ μ hσ).measure, gevLogDensityE ξ μ σ x ≠ ⊥ := by
  rw [measure_gevLocScaleCDF_eq_withDensity, ae_withDensity_iff
    (measurable_gevLocScaleDensity ξ μ σ).ennreal_ofReal]
  refine ae_of_all _ fun x hx => ?_
  rw [gevLogDensityE_ne_bot_iff]
  exact ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 hx)

end Law

/-! ### Identifiability and the Kullback–Leibler inequality -/

section Ident

variable {ξ μ σ z x : ℝ}

lemma gevFun_zero_right (ξ : ℝ) : gevFun ξ 0 = exp (-1) := by
  by_cases hξ : ξ = 0 <;> simp [gevFun, hξ]

/-- Strictly between `0` and `1`, the GEV distribution function is evaluated inside the
support. -/
lemma mem_support_of_gevFun_mem (h0 : 0 < gevFun ξ z) (h1 : gevFun ξ z < 1) :
    ξ = 0 ∨ 0 < 1 + ξ * z := by
  by_contra hc
  push Not at hc
  by_cases hξ : 0 < ξ <;> simp [gevFun, hc.1, not_lt.2 hc.2, hξ] at h0 h1

lemma eq_zero_of_gevFun_eq (h : gevFun ξ z = exp (-1)) : z = 0 := by
  unfold gevFun at h
  split_ifs at h with h0 hu hp
  · have h2 : exp (-z) = 1 := by have := exp_injective h; linarith
    simpa using h2
  · have h2 : (1 + ξ * z) ^ (-1 / ξ) = 1 := by have := exp_injective h; linarith
    have h3 : 1 + ξ * z = ((1 + ξ * z) ^ (-1 / ξ)) ^ (-ξ) := by
      rw [← rpow_mul hu.le, show -1 / ξ * -ξ = 1 by field_simp, rpow_one]
    rw [h2, one_rpow] at h3
    have : ξ * z = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left h0
  · exact absurd h (exp_pos _).ne
  · have := exp_lt_one_iff.2 (show (-1 : ℝ) < 0 by norm_num)
    linarith

lemma add_mul_pos_of_mem_support (hσ : 0 < σ) (hu : ξ = 0 ∨ 0 < 1 + ξ * ((x - μ) / σ)) :
    0 < σ + ξ * (x - μ) := by
  rcases hu with rfl | hu
  · simpa using hσ
  · have : σ + ξ * (x - μ) = σ * (1 + ξ * ((x - μ) / σ)) := by field_simp
    rw [this]; positivity

/-- Inside the support, `-log(-log H_ξ((x - μ)/σ)) = log(1 + ξ (x - μ)/σ)/ξ` has derivative
`1/(σ + ξ (x - μ))`. -/
lemma hasDerivAt_neg_log_neg_log_gevFun (hσ : 0 < σ) (hu : ξ = 0 ∨ 0 < 1 + ξ * ((x - μ) / σ)) :
    HasDerivAt (fun y => -log (-log (gevFun ξ ((y - μ) / σ)))) (1 / (σ + ξ * (x - μ))) x := by
  have hd : HasDerivAt (fun y => (y - μ) / σ) σ⁻¹ x := by
    simpa using ((hasDerivAt_id x).sub_const μ).div_const σ
  have hpos := add_mul_pos_of_mem_support hσ hu
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have heq : (fun y => -log (-log (gevFun 0 ((y - μ) / σ)))) = fun y => (y - μ) / σ := by
      funext y; simp [gevFun]
    rw [heq]
    simpa using hd
  · have hu' := hu.resolve_left hξ
    have hcu : ContinuousAt (fun y => 1 + ξ * ((y - μ) / σ)) x := by fun_prop
    have heq : (fun y => log (1 + ξ * ((y - μ) / σ)) / ξ) =ᶠ[𝓝 x]
        fun y => -log (-log (gevFun ξ ((y - μ) / σ))) := by
      filter_upwards [hcu.eventually (lt_mem_nhds hu')] with y hy
      simp only [gevFun, hξ, hy, ↓reduceIte, log_exp, neg_neg]
      rw [log_rpow hy]
      ring
    refine HasDerivAt.congr_of_eventuallyEq ?_ heq.symm
    have hd2 : HasDerivAt (fun y => 1 + ξ * ((y - μ) / σ)) (ξ * σ⁻¹) x :=
      (hd.const_mul ξ).const_add 1
    convert (hd2.log hu'.ne').div_const ξ using 1
    have e : 1 + ξ * ((x - μ) / σ) = (σ + ξ * (x - μ)) / σ := by field_simp
    rw [e]
    field_simp

/-- **Identifiability of the three-parameter GEV family**: if the location-scale GEV laws with
parameters `(ξ, μ, σ)` and `(ξ', μ', σ')` coincide, the parameters coincide. Near `x = μ` both
distribution functions lie strictly between `0` and `1`, and `-log(-log F)` has derivative
`1/(σ + ξ (x - μ)) = 1/(σ' + ξ' (x - μ'))`; this affine identity gives `ξ = ξ'`, and
`F(μ) = e^{-1}` gives `μ = μ'`. -/
theorem gev_params_eq_of_measure_eq {ξ' μ' σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ')
    (h : (gevLocScaleCDF ξ μ hσ).measure = (gevLocScaleCDF ξ' μ' hσ').measure) :
    ξ = ξ' ∧ μ = μ' ∧ σ = σ' := by
  have hF : ∀ x, gevFun ξ ((x - μ) / σ) = gevFun ξ' ((x - μ') / σ') := fun x => by
    rw [← gevLocScaleCDF_apply ξ μ hσ, ← gevLocScaleCDF_apply ξ' μ' hσ',
      CumulativeDistributionFunction.apply_eq_measure_Iic,
      CumulativeDistributionFunction.apply_eq_measure_Iic, h]
  have hFc : ContinuousAt (fun x => gevFun ξ ((x - μ) / σ)) μ :=
    ((continuous_gevFun ξ).comp (by fun_prop)).continuousAt
  have hFμ : gevFun ξ ((μ - μ) / σ) = exp (-1) := by rw [sub_self, zero_div, gevFun_zero_right]
  have h01 : 0 < exp (-1 : ℝ) ∧ exp (-1 : ℝ) < 1 :=
    ⟨exp_pos _, exp_lt_one_iff.2 (by norm_num)⟩
  have hev : ∀ᶠ y in 𝓝 μ, 0 < gevFun ξ ((y - μ) / σ) ∧ gevFun ξ ((y - μ) / σ) < 1 := by
    have := hFc.eventually (Ioo_mem_nhds (hFμ ▸ h01.1) (hFμ ▸ h01.2))
    filter_upwards [this] with y hy
    exact hy
  have hV : (fun y => -log (-log (gevFun ξ' ((y - μ') / σ')))) =
      fun y => -log (-log (gevFun ξ ((y - μ) / σ))) := funext fun y => by rw [hF]
  have hlin : ∀ᶠ y in 𝓝 μ, σ + ξ * (y - μ) = σ' + ξ' * (y - μ') := by
    filter_upwards [hev] with y hy
    have hu := mem_support_of_gevFun_mem hy.1 hy.2
    have hu' := mem_support_of_gevFun_mem (hF y ▸ hy.1) (hF y ▸ hy.2)
    have d1 := hasDerivAt_neg_log_neg_log_gevFun hσ hu
    have d2 := hasDerivAt_neg_log_neg_log_gevFun hσ' hu'
    rw [hV] at d2
    have := d1.unique d2
    have p1 := add_mul_pos_of_mem_support hσ hu
    have p2 := add_mul_pos_of_mem_support hσ' hu'
    rw [div_eq_div_iff p1.ne' p2.ne'] at this
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hlin
  have e1 := hball (y := μ) (by simpa using hε)
  have e2 := hball (y := μ + ε / 2) (by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]; linarith)
  have hξ : ξ = ξ' := by
    have : (ξ - ξ') * (ε / 2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hμ : μ = μ' := by
    have := eq_zero_of_gevFun_eq ((hF μ).symm.trans hFμ)
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · linarith
    · linarith
  subst hξ hμ
  exact ⟨rfl, rfl, by linarith⟩

/-- **The Kullback–Leibler inequality for the GEV family.** If the support of the GEV law with
parameters `(ξ, μ, σ)` carries the true law (density positive a.s.), the log-density is
integrable, and the parameters differ from the true `(ξ₀, μ₀, σ₀)`, then the expected
log-density is strictly smaller than at the truth. -/
theorem integral_log_gevLocScaleDensity_lt {ξ₀ μ₀ σ₀ : ℝ} (hσ : 0 < σ) (hσ₀ : 0 < σ₀)
    (hne : ¬ (ξ = ξ₀ ∧ μ = μ₀ ∧ σ = σ₀))
    (hpos : ∀ᵐ x ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure, 0 < gevLocScaleDensity ξ μ σ x)
    (hi : Integrable (fun x => log (gevLocScaleDensity ξ μ σ x))
      (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure) :
    ∫ x, log (gevLocScaleDensity ξ μ σ x) ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure <
      ∫ x, log (gevLocScaleDensity ξ₀ μ₀ σ₀ x) ∂(gevLocScaleCDF ξ₀ μ₀ hσ₀).measure := by
  have hd := integral_eq_one_of_eq_withDensity (measure_gevLocScaleCDF_eq_withDensity ξ μ hσ)
    (fun x => gevLocScaleDensity_nonneg hσ)
    (measurable_gevLocScaleDensity ξ μ σ).aestronglyMeasurable
  refine integral_log_lt_of_density (measurable_gevLocScaleDensity ξ μ σ)
    (measurable_gevLocScaleDensity ξ₀ μ₀ σ₀) (fun x => gevLocScaleDensity_nonneg hσ)
    (fun x => gevLocScaleDensity_nonneg hσ₀) (measure_gevLocScaleCDF_eq_withDensity ξ₀ μ₀ hσ₀)
    hd.1 hd.2 hpos hi (integrable_log_gevLocScaleDensity_self hσ₀) fun hae => hne ?_
  refine gev_params_eq_of_measure_eq hσ hσ₀ ?_
  rw [measure_gevLocScaleCDF_eq_withDensity ξ μ hσ,
    measure_gevLocScaleCDF_eq_withDensity ξ₀ μ₀ hσ₀]
  exact withDensity_congr_ae (hae.mono fun x hx => by simp only; rw [hx])

end Ident

/-! ### Strong consistency of the GEV MLE -/

section MLE

variable {K : Set (ℝ × ℝ × ℝ)}

/-- **Existence of the GEV MLE on a compact parameter set** `K ⊂ {ξ > -1, σ > 0}`, for the
extended-real log-likelihood (which is continuous on `K`). -/
theorem exists_isMaxOn_gevLogLikE (hK : IsCompact K) (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2)
    (hne : K.Nonempty) {n : ℕ} (x : Fin n → ℝ) :
    ∃ θ ∈ K, IsMaxOn (fun p : ℝ × ℝ × ℝ => gevLogLikE p.1 p.2.1 p.2.2 x) K θ := by
  refine hK.exists_isMaxOn hne ?_
  refine (continuousOn_finsetSum_ereal Finset.univ
    (fun i _ => (continuousOn_gevLogDensityE (x i)).mono fun p hp => hKS p hp)
    (fun i _ p hp => ?_)).1
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (gevLogDensityE_le (hKS p hp).1 (hKS p hp).2 (x i))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- **Strong consistency of the GEV maximum likelihood estimator, all shapes `ξ > -1`**
(Smith 1985; Bücher–Segers 2017, Theorem 2). Let `K` be a compact set of parameters
`(ξ, μ, σ)` with `ξ > -1`, `σ > 0`, containing the true parameter `θ₀`, and let `X₀, X₁, …` be
iid with the location-scale GEV law of parameter `θ₀`. Almost surely, every sequence `θ̂ₙ ∈ K`
of approximate maximizers of the extended-real log-likelihood over `K` —
`ℓₙ(θ₀) ≤ ℓₙ(θ̂ₙ) + n εₙ` eventually with `εₙ → 0` (for instance exact maximizers, which exist
by `exists_isMaxOn_gevLogLikE`) — converges to `θ₀`. The support of the GEV law depends on the
parameters; the log-likelihood is `-∞` at parameters under which some observation is
impossible. -/
theorem ae_tendsto_gevMLE (hK : IsCompact K) (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2.2)
    {θ₀ : ℝ × ℝ × ℝ} (hθ₀ : θ₀ ∈ K) (hσ₀ : 0 < θ₀.2.2)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF θ₀.1 θ₀.2.1 hσ₀).measure P)
    (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, ∀ (θhat : ℕ → ℝ × ℝ × ℝ) (ε : ℕ → ℝ), (∀ n, θhat n ∈ K) →
      Tendsto ε atTop (𝓝 0) →
      (∀ᶠ n in atTop, gevLogLikE θ₀.1 θ₀.2.1 θ₀.2.2 (fun i : Fin n => X i ω) ≤
        gevLogLikE (θhat n).1 (θhat n).2.1 (θhat n).2.2 (fun i : Fin n => X i ω) +
          ((n * ε n : ℝ) : EReal)) →
      Tendsto θhat atTop (𝓝 θ₀) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ p ∈ K, -log p.2.2 + (1 + p.1) ^ 2 ≤ C := by
    have hco : ContinuousOn (fun p : ℝ × ℝ × ℝ => -log p.2.2 + (1 + p.1) ^ 2) K := fun p hp =>
      (((continuous_snd.comp continuous_snd).continuousAt.log (hKS p hp).2.ne').neg.add
        (by fun_prop : Continuous fun p : ℝ × ℝ × ℝ => (1 + p.1) ^ 2).continuousAt).continuousWithinAt
    obtain ⟨C, hC⟩ := hK.bddAbove_image hco
    exact ⟨C, fun p hp => hC ⟨p, hp, rfl⟩⟩
  set μ₀ := (gevLocScaleCDF θ₀.1 θ₀.2.1 hσ₀).measure
  set m : K → ℝ → EReal := fun θ x => gevLogDensityE θ.1.1 θ.1.2.1 θ.1.2.2 x
  have hbound : ∀ θ x, m θ x ≤ (fun _ : ℝ => C) x := fun θ x =>
    (gevLogDensityE_le (hKS θ.1 θ.2).1 (hKS θ.1 θ.2).2 x).trans
      (EReal.coe_le_coe_iff.2 (hC θ.1 θ.2))
  have hcont : ∀ x, Continuous fun θ => m θ x := fun x =>
    (continuousOn_gevLogDensityE x).comp_continuous continuous_subtype_val
      fun θ => hKS θ.1 θ.2
  have hmeas : ∀ θ, Measurable (m θ) := fun θ => measurable_gevLogDensityE _ _ _
  have hint₀ : Integrable (fun x => (m ⟨θ₀, hθ₀⟩ x).toReal) μ₀ := by
    simp only [m, toReal_gevLogDensityE hσ₀]
    exact integrable_log_gevLocScaleDensity_self hσ₀
  have hident : ∀ θ : K, θ ≠ ⟨θ₀, hθ₀⟩ → (∀ᵐ x ∂μ₀, m θ x ≠ ⊥) →
      Integrable (fun x => (m θ x).toReal) μ₀ →
      ∫ x, (m θ x).toReal ∂μ₀ < ∫ x, (m ⟨θ₀, hθ₀⟩ x).toReal ∂μ₀ := by
    intro θ hne hfin hi
    simp only [m, toReal_gevLogDensityE (hKS θ.1 θ.2).2, toReal_gevLogDensityE hσ₀] at hi ⊢
    refine integral_log_gevLocScaleDensity_lt (hKS θ.1 θ.2).2 hσ₀
      (fun h => hne (Subtype.ext (Prod.ext h.1 (Prod.ext h.2.1 h.2.2)))) ?_ hi
    filter_upwards [hfin] with x hx
    exact gevLogDensityE_ne_bot_iff.1 hx
  have h₀ : ∀ᵐ x ∂μ₀, m ⟨θ₀, hθ₀⟩ x ≠ ⊥ := ae_gevLogDensityE_ne_bot hσ₀
  filter_upwards [ae_tendsto_of_wald_ereal_of_continuous (θ₀ := ⟨θ₀, hθ₀⟩) hX hind hcont hmeas
    (integrable_const C) hbound h₀ hint₀ hident]
    with ω hω θhat ε hθK hε hθ
  have := hω (fun n => ⟨θhat n, hθK n⟩) ε hε (hθ.mono fun n hn => by
    simp only [gevLogLikE] at hn
    rw [Fin.sum_univ_eq_sum_range (fun i => gevLogDensityE θ₀.1 θ₀.2.1 θ₀.2.2 (X i ω)) n,
      Fin.sum_univ_eq_sum_range
        (fun i => gevLogDensityE (θhat n).1 (θhat n).2.1 (θhat n).2.2 (X i ω)) n] at hn
    exact hn)
  exact (continuous_subtype_val.tendsto _).comp this

end MLE

end ExtremeValueTheory
