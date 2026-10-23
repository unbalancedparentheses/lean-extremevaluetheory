/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.WaldEReal

/-!
# Consistency of the joint GPD maximum likelihood estimator, all shapes `ξ > -1`

For a shape `ξ < 0` the support `[0, -σ/ξ]` of `GPD(ξ, σ)` depends on the parameters, and the
log-likelihood must take the value `-∞` at parameters under which some observation is
impossible. We work with the **extended-real log-density** `gpdLogDensityE ξ σ x ∈ [-∞, ∞)`
(`log g_{ξ,σ}(x)` on the support, `-∞` outside) and the corresponding log-likelihood
`gpdLogLikE`. Its real part is the real log-density `log (gpdDensity ξ σ x)`
(`toReal_gpdLogDensityE`).

## Main results

* `ExtremeValueTheory.log_gpdDensity_eq`: the log-density in the form
  `-log σ - (1 + ξ) (x/σ) λ(ξ x/σ)`, with `λ(t) = log(1 + t)/t` (`λ(0) = 1`, `log1pDiv`)
  continuous on `(-1, ∞)` (`continuousOn_log1pDiv`). This is the continuity of the log-density
  across `ξ = 0`: `(1/ξ + 1) log(1 + ξ x/σ) → x/σ`.
* `ExtremeValueTheory.continuousOn_gpdLogDensityE`: `(ξ, σ) ↦ gpdLogDensityE ξ σ x` is continuous
  (as an `EReal`-valued map) on `{ξ > -1, σ > 0}`. At the boundary of the support the
  log-density tends to `-∞`, because the exponent `-(1/ξ + 1)` is positive for `-1 < ξ < 0`.
* `ExtremeValueTheory.gpdLogDensityE_le`: the upper envelope `log g_{ξ,σ}(x) ≤ -log σ` for
  `ξ > -1`.
* `ExtremeValueTheory.gpd_params_eq_of_gpdMeasure_eq'`: identifiability of the GPD family for
  all shapes.
* `ExtremeValueTheory.integral_log_lt_of_density`: the Kullback–Leibler inequality for densities
  whose supports may differ.
* `ExtremeValueTheory.ae_tendsto_gpdMLE'`: **strong consistency of the joint MLE** on a compact
  parameter set `K ⊂ {ξ > -1, σ > 0}` (in particular on compact subsets of
  `{ξ > -1/2, σ > 0}`, the regular case), via the extended-real Wald theorem
  `ae_tendsto_of_wald_ereal_of_continuous`. Maximizers exist (`exists_isMaxOn_gpdLogLikE`).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExtremeValueTheory

/-! ### The function `log(1 + t)/t` -/

section Log1pDiv

/-- `λ(t) = log(1 + t) / t`, extended by `λ(0) = 1`. -/
noncomputable def log1pDiv (t : ℝ) : ℝ := if t = 0 then 1 else log (1 + t) / t

lemma log1pDiv_zero : log1pDiv 0 = 1 := by simp [log1pDiv]

lemma log1pDiv_of_ne {t : ℝ} (ht : t ≠ 0) : log1pDiv t = log (1 + t) / t := by
  simp [log1pDiv, ht]

lemma log1pDiv_pos {t : ℝ} (ht : -1 < t) : 0 < log1pDiv t := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [log1pDiv_of_ne h.ne]
    exact div_pos_of_neg_of_neg (log_neg (by linarith) (by linarith)) h
  · rw [log1pDiv_zero]; exact one_pos
  · rw [log1pDiv_of_ne h.ne']
    exact div_pos (log_pos (by linarith)) h

/-- `log(1 + t)/t → 1` as `t → 0`: `λ` is continuous at `0`. -/
lemma continuousAt_log1pDiv_zero : ContinuousAt log1pDiv 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, log1pDiv_zero]
  have h := (hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_log (one_ne_zero (α := ℝ))))
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [log1pDiv_of_ne ht, log_one, sub_zero, smul_eq_mul, div_eq_inv_mul]

lemma continuousAt_log1pDiv {t : ℝ} (ht : -1 < t) : ContinuousAt log1pDiv t := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact continuousAt_log1pDiv_zero
  · have hev : (fun s => log (1 + s) / s) =ᶠ[𝓝 t] log1pDiv := by
      filter_upwards [isOpen_ne.mem_nhds h0] with s hs
      rw [log1pDiv_of_ne hs]
    refine ContinuousAt.congr ?_ hev
    exact ((continuousAt_const.add continuousAt_id).log
      (by simp only [Pi.add_apply, id]; linarith)).div continuousAt_id h0

lemma continuousOn_log1pDiv : ContinuousOn log1pDiv (Ioi (-1)) :=
  fun _ ht => (continuousAt_log1pDiv ht).continuousWithinAt

end Log1pDiv

/-! ### The extended-real log-density -/

section LogDensityE

variable {ξ σ x : ℝ}

lemma gpdDensity_pos_of_mem (hσ : 0 < σ) (hx : 0 ≤ x) (hu : 0 < 1 + ξ * x / σ) :
    0 < gpdDensity ξ σ x := by
  unfold gpdDensity
  rw [ite_eq_left ⟨hx, hu⟩]
  split_ifs
  · positivity
  · exact mul_pos (inv_pos.2 hσ) (rpow_pos_of_pos hu _)

lemma gpdDensity_of_not_mem (h : ¬ (0 ≤ x ∧ 0 < 1 + ξ * x / σ)) : gpdDensity ξ σ x = 0 := by
  unfold gpdDensity; rw [ite_eq_right h]

/-- **The GPD log-density, uniformly in the shape**:
`log g_{ξ,σ}(x) = -log σ - (1 + ξ) (x/σ) λ(ξ x/σ)` on the support, with `λ(t) = log(1+t)/t`.
For `ξ ≠ 0` this is `-log σ - (1/ξ + 1) log(1 + ξ x/σ)`, for `ξ = 0` it is `-log σ - x/σ`. -/
theorem log_gpdDensity_eq (hσ : 0 < σ) (hx : 0 ≤ x) (hu : 0 < 1 + ξ * x / σ) :
    log (gpdDensity ξ σ x) = -log σ - (1 + ξ) * (x / σ) * log1pDiv (ξ * (x / σ)) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [log_gpdDensity_zero hσ hx]; simp [log1pDiv_zero]
  rw [log_gpdDensity hσ hξ hx hu]
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  · have hne : ξ * (x / σ) ≠ 0 := mul_ne_zero hξ (div_pos hx0 hσ).ne'
    rw [log1pDiv_of_ne hne, ← mul_div_assoc]
    field_simp

/-- The **extended-real GPD log-density**: `log g_{ξ,σ}(x)` on the support
`{x ≥ 0, 1 + ξ x/σ > 0}` and `-∞` outside. -/
noncomputable def gpdLogDensityE (ξ σ x : ℝ) : EReal :=
  if 0 ≤ x ∧ 0 < 1 + ξ * x / σ then ((log (gpdDensity ξ σ x) : ℝ) : EReal) else ⊥

/-- The **extended-real GPD log-likelihood** `∑ᵢ log g_{ξ,σ}(xᵢ) ∈ [-∞, ∞)`. -/
noncomputable def gpdLogLikE {n : ℕ} (ξ σ : ℝ) (x : Fin n → ℝ) : EReal :=
  ∑ i, gpdLogDensityE ξ σ (x i)

lemma toReal_gpdLogDensityE : (gpdLogDensityE ξ σ x).toReal = log (gpdDensity ξ σ x) := by
  unfold gpdLogDensityE
  split_ifs with h
  · exact EReal.toReal_coe _
  · rw [gpdDensity_of_not_mem h, log_zero, EReal.toReal_bot]

lemma gpdLogDensityE_ne_bot_iff :
    gpdLogDensityE ξ σ x ≠ ⊥ ↔ 0 ≤ x ∧ 0 < 1 + ξ * x / σ := by
  unfold gpdLogDensityE
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => EReal.coe_ne_bot _⟩
  · exact ⟨fun h' => absurd rfl h', fun h' => absurd h' h⟩

lemma measurable_gpdLogDensityE (ξ σ : ℝ) : Measurable (gpdLogDensityE ξ σ) := by
  have hs : MeasurableSet {x : ℝ | 0 ≤ x ∧ 0 < 1 + ξ * x / σ} :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt measurable_const
        (measurable_const.add ((measurable_const.mul measurable_id).div_const σ)))
  exact Measurable.ite hs (measurable_gpdDensity ξ σ).log.coe_real_ereal measurable_const

/-- **Upper envelope**: for `ξ > -1`, `log g_{ξ,σ}(x) ≤ -log σ`. -/
theorem gpdLogDensityE_le (hξ : -1 < ξ) (hσ : 0 < σ) (x : ℝ) :
    gpdLogDensityE ξ σ x ≤ ((-log σ : ℝ) : EReal) := by
  unfold gpdLogDensityE
  split_ifs with h
  · refine EReal.coe_le_coe_iff.2 ?_
    rw [log_gpdDensity_eq hσ h.1 h.2]
    have ht : -1 < ξ * (x / σ) := by rw [← mul_div_assoc]; linarith [h.2]
    have := log1pDiv_pos ht
    have : 0 ≤ (1 + ξ) * (x / σ) * log1pDiv (ξ * (x / σ)) :=
      mul_nonneg (mul_nonneg (by linarith) (div_nonneg h.1 hσ.le)) this.le
    linarith
  · exact bot_le

/-- The parameter set `{ξ > -1, σ > 0}`. -/
def gpdParamSet : Set (ℝ × ℝ) := {p | -1 < p.1 ∧ 0 < p.2}

/-- In the interior of the support, the log-density is a continuous function of the
parameters, across `ξ = 0`. -/
private lemma continuousAt_logDensity_formula (x : ℝ) {p : ℝ × ℝ} (hp : 0 < p.2)
    (hu : -1 < p.1 * (x / p.2)) :
    ContinuousAt (fun q : ℝ × ℝ => -log q.2 - (1 + q.1) * (x / q.2) *
      log1pDiv (q.1 * (x / q.2))) p := by
  have h2 : ContinuousAt (fun q : ℝ × ℝ => x / q.2) p :=
    continuousAt_const.div continuous_snd.continuousAt hp.ne'
  have h3 : ContinuousAt (fun q : ℝ × ℝ => q.1 * (x / q.2)) p :=
    continuous_fst.continuousAt.mul h2
  exact (continuous_snd.continuousAt.log hp.ne').neg.sub
    (((continuousAt_const.add continuous_fst.continuousAt).mul h2).mul
      ((continuousAt_log1pDiv hu).comp (f := fun q : ℝ × ℝ => q.1 * (x / q.2)) h3))

/-- **Continuity of the extended-real log-density in the parameters.** For every `x`, the map
`(ξ, σ) ↦ gpdLogDensityE ξ σ x ∈ [-∞, ∞)` is continuous on `{ξ > -1, σ > 0}`. In the interior
of the support this is the continuity of `-log σ - (1 + ξ)(x/σ) λ(ξ x/σ)`, also across `ξ = 0`;
at the boundary `1 + ξ x/σ = 0` (only for `ξ < 0`) the log-density
`-log σ - (1/ξ + 1) log(1 + ξ x/σ)` tends to `-∞`, since `-(1/ξ + 1) > 0` for `-1 < ξ < 0`. -/
theorem continuousOn_gpdLogDensityE (x : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => gpdLogDensityE p.1 p.2 x) gpdParamSet := by
  rcases lt_or_ge x 0 with hx | hx
  · refine (continuousOn_const (c := (⊥ : EReal))).congr fun p _ => ?_
    simp [gpdLogDensityE, not_le.2 hx]
  intro p hp
  have hp2 : 0 < p.2 := hp.2
  have hcu : ContinuousAt (fun q : ℝ × ℝ => 1 + q.1 * x / q.2) p :=
    continuousAt_const.add ((continuous_fst.continuousAt.mul continuousAt_const).div
      continuous_snd.continuousAt hp2.ne')
  by_cases hu : 0 < 1 + p.1 * x / p.2
  · -- interior of the support
    have hu' : -1 < p.1 * (x / p.2) := by rw [← mul_div_assoc]; linarith
    have hev : (fun q : ℝ × ℝ => (((-log q.2 - (1 + q.1) * (x / q.2) *
        log1pDiv (q.1 * (x / q.2)) : ℝ)) : EReal)) =ᶠ[𝓝 p]
        fun q : ℝ × ℝ => gpdLogDensityE q.1 q.2 x := by
      filter_upwards [continuous_snd.continuousAt.eventually (lt_mem_nhds hp2),
        hcu.eventually (lt_mem_nhds hu)] with q hq2 hqu
      simp only [gpdLogDensityE, hx, hqu, and_self, ↓reduceIte, log_gpdDensity_eq hq2 hx hqu]
    exact ((continuous_coe_real_ereal.continuousAt.comp
      (continuousAt_logDensity_formula x hp2 hu')).congr hev).continuousWithinAt
  · -- boundary or exterior of the support: the log-density tends to `-∞`
    have hval : gpdLogDensityE p.1 p.2 x = ⊥ := by
      simp only [gpdLogDensityE, hu, and_false, ↓reduceIte]
    have hξ : p.1 < 0 := by
      by_contra h
      have : 0 ≤ p.1 * x / p.2 := div_nonneg (mul_nonneg (not_lt.1 h) hx) hp2.le
      exact hu (by linarith)
    have hξ1 : -1 < p.1 := hp.1
    have hc : 1 / p.1 + 1 < 0 := by
      have : 1 / p.1 < -1 := by rw [div_lt_iff_of_neg hξ]; linarith
      linarith
    set κ := -(1 / p.1 + 1) / 2 with hκ
    have hκ0 : 0 < κ := by rw [hκ]; linarith
    rw [ContinuousWithinAt, hval, EReal.tendsto_nhds_bot_iff_real]
    intro b
    set δ := min (1 / 2) (exp ((b - 1 + log (p.2 / 2)) / κ)) with hδ
    have hδ0 : 0 < δ := lt_min (by norm_num) (exp_pos _)
    have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hlogδ : κ * log δ ≤ b - 1 + log (p.2 / 2) := by
      have : log δ ≤ (b - 1 + log (p.2 / 2)) / κ := by
        rw [← log_exp ((b - 1 + log (p.2 / 2)) / κ)]
        exact log_le_log hδ0 (min_le_right _ _)
      rw [le_div_iff₀ hκ0] at this
      linarith
    have hcoef : ContinuousAt (fun q : ℝ × ℝ => 1 / q.1 + 1) p :=
      (continuousAt_const.div continuous_fst.continuousAt hξ.ne).add continuousAt_const
    have hlt : 1 / p.1 + 1 < -κ := by rw [hκ]; linarith
    refine nhdsWithin_le_nhds ?_
    filter_upwards [continuous_snd.continuousAt.eventually (lt_mem_nhds (half_lt_self hp2)),
      hcoef.eventually (gt_mem_nhds hlt),
      hcu.eventually (gt_mem_nhds (lt_of_le_of_lt (not_lt.1 hu) hδ0))] with q hq2 hqc hqu
    unfold gpdLogDensityE
    split_ifs with hsupp
    · have hq2' : 0 < q.2 := (half_pos hp2).trans hq2
      have hq1 : q.1 ≠ 0 := by
        rintro h
        rw [h, div_zero, zero_add] at hqc
        linarith
      rw [log_gpdDensity hq2' hq1 hsupp.1 hsupp.2]
      refine EReal.coe_lt_coe_iff.2 ?_
      have hlogu : log (1 + q.1 * x / q.2) < log δ := log_lt_log hsupp.2 hqu
      have hlogδ0 : log δ < 0 := log_neg hδ0 hδ1
      have hσ : log (p.2 / 2) < log q.2 := log_lt_log (half_pos hp2) hq2
      have : -(1 / q.1 + 1) * log (1 + q.1 * x / q.2) ≤ κ * log (1 + q.1 * x / q.2) := by
        nlinarith
      nlinarith
    · exact EReal.bot_lt_coe b

/-- The log-density at the true parameter, on the exponential scale:
`log g_{ξ,σ}(T(t)) = -log σ - (1 + ξ) t` for `t > 0`. -/
lemma log_gpdDensity_gpdTransform (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    log (gpdDensity ξ σ (gpdTransform ξ σ t)) = -log σ - (1 + ξ) * t := by
  have hT := (gpdTransform_pos (ξ := ξ) hσ ht).le
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [log_gpdDensity_zero hσ hT]
    simp only [gpdTransform, ↓reduceIte]
    field_simp
    ring
  · have hu := one_add_mul_gpdTransform hσ hξ t
    rw [log_gpdDensity hσ hξ hT (hu ▸ exp_pos _), hu, log_exp]
    field_simp

/-- At the true parameter, the log-density is integrable. -/
lemma integrable_log_gpdDensity_self (hσ : 0 < σ) :
    Integrable (fun x => log (gpdDensity ξ σ x)) (gpdMeasure ξ σ) := by
  rw [integrable_gpdMeasure_iff (measurable_gpdDensity ξ σ).log]
  refine ((integrable_const (-log σ)).sub ((integrable_pow_expMeasure 1).const_mul (1 + ξ))).congr
    ?_
  filter_upwards [ae_pos_expMeasure] with t ht
  simp only [Pi.sub_apply, pow_one]
  rw [log_gpdDensity_gpdTransform hσ ht]

/-- At the true parameter, the extended-real log-density is a.s. finite. -/
lemma ae_gpdLogDensityE_ne_bot (hσ : 0 < σ) :
    ∀ᵐ x ∂gpdMeasure ξ σ, gpdLogDensityE ξ σ x ≠ ⊥ := by
  filter_upwards [ae_gpdMeasure hσ] with x hx
  rw [gpdLogDensityE_ne_bot_iff]
  refine ⟨hx.1.le, ?_⟩
  have : 1 + ξ * x / σ = (σ + ξ * x) / σ := by field_simp
  rw [this]; exact div_pos hx.2 hσ

end LogDensityE

/-! ### The Kullback–Leibler inequality and identifiability -/

section KL

variable {α : Type*} {mα : MeasurableSpace α} {ν μ₀ : Measure α}

/-- **The Kullback–Leibler inequality for densities with possibly different supports.** Let
`μ₀ = f₀ · ν` be a probability measure and `f` a probability density with respect to `ν`, with
`f > 0` `μ₀`-a.e. (the support of `f` contains that of `μ₀`, but may be larger). If `log f` and
`log f₀` are `μ₀`-integrable and `f ≠ f₀` on a set of positive `ν`-measure, then
`∫ log f dμ₀ < ∫ log f₀ dμ₀`. -/
theorem integral_log_lt_of_density [IsProbabilityMeasure μ₀] {f f₀ : α → ℝ}
    (hf : Measurable f) (hf₀ : Measurable f₀) (hf0 : ∀ x, 0 ≤ f x) (hf₀0 : ∀ x, 0 ≤ f₀ x)
    (hμ : μ₀ = ν.withDensity fun x => ENNReal.ofReal (f₀ x)) (hfi : Integrable f ν)
    (hf1 : ∫ x, f x ∂ν = 1) (hpos : ∀ᵐ x ∂μ₀, 0 < f x)
    (hi : Integrable (fun x => log (f x)) μ₀) (hi₀ : Integrable (fun x => log (f₀ x)) μ₀)
    (hne : ¬ f =ᵐ[ν] f₀) :
    ∫ x, log (f x) ∂μ₀ < ∫ x, log (f₀ x) ∂μ₀ := by
  have hm₀ : Measurable fun x => ENNReal.ofReal (f₀ x) := hf₀.ennreal_ofReal
  have hlt : ∀ᵐ x ∂ν, ENNReal.ofReal (f₀ x) < ∞ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hpos₀ : ∀ᵐ x ∂μ₀, 0 < f₀ x := by
    rw [hμ, ae_withDensity_iff hm₀]
    exact ae_of_all _ fun x hx => by
      rcases (hf₀0 x).eq_or_lt with h | h
      · exact absurd (by rw [← h, ENNReal.ofReal_zero]) hx
      · exact h
  set r : α → ℝ := fun x => f x / f₀ x
  set q : α → ℝ := fun x => f₀ x * r x
  have hq : ∀ x, 0 ≤ q x ∧ q x ≤ f x := fun x => by
    simp only [q, r]
    rcases (hf₀0 x).eq_or_lt with h | h
    · rw [← h, zero_mul]; exact ⟨le_rfl, hf0 x⟩
    · rw [mul_div_cancel₀ _ h.ne']; exact ⟨hf0 x, le_rfl⟩
  have hsmul : ∀ x, (ENNReal.ofReal (f₀ x)).toReal • r x = q x := fun x => by
    rw [ENNReal.toReal_ofReal (hf₀0 x), smul_eq_mul]
  have hqm : Measurable q := hf₀.mul (hf.div hf₀)
  have hqi : Integrable q ν := hfi.mono' hqm.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hq x).1]; exact (hq x).2)
  have hri : Integrable r μ₀ := by
    rw [hμ, integrable_withDensity_iff_integrable_smul' hm₀ hlt]
    exact hqi.congr (ae_of_all _ fun x => (hsmul x).symm)
  have hrq : ∫ x, r x ∂μ₀ = ∫ x, q x ∂ν := by
    rw [hμ, integral_withDensity_eq_integral_toReal_smul hm₀ hlt]
    simp_rw [hsmul]
  by_contra hge
  have hge := not_lt.1 hge
  -- the nonnegative function `r - 1 - log r` has nonpositive integral
  set h : α → ℝ := fun x => (r x - 1) - (log (f x) - log (f₀ x))
  have hh0 : 0 ≤ᵐ[μ₀] h := by
    filter_upwards [hpos, hpos₀] with x h1 h2
    have := log_le_sub_one_of_pos (div_pos h1 h2)
    rw [log_div h1.ne' h2.ne'] at this
    simp only [Pi.zero_apply, h, r]
    linarith
  have hhi : Integrable h μ₀ := (hri.sub (integrable_const 1)).sub (hi.sub hi₀)
  have hint_h : ∫ x, h x ∂μ₀ = ∫ x, q x ∂ν - 1 - (∫ x, log (f x) ∂μ₀ - ∫ x, log (f₀ x) ∂μ₀) := by
    have hA : Integrable (fun x => r x - 1) μ₀ := hri.sub (integrable_const 1)
    have hB : Integrable (fun x => log (f x) - log (f₀ x)) μ₀ := hi.sub hi₀
    simp only [h]
    rw [integral_sub hA hB,
      integral_sub hri (integrable_const 1), integral_sub hi hi₀, hrq, integral_const,
      probReal_univ, one_smul]
  have hqle : ∫ x, q x ∂ν ≤ 1 := hf1 ▸ integral_mono hqi hfi fun x => (hq x).2
  have hzero : ∫ x, h x ∂μ₀ = 0 :=
    le_antisymm (by rw [hint_h]; linarith) (integral_nonneg_of_ae hh0)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hh0 hhi).1 hzero
  -- hence `f = f₀` `μ₀`-a.e.
  have hff₀ : ∀ᵐ x ∂μ₀, f x = f₀ x := by
    filter_upwards [hae, hpos, hpos₀] with x hx h1 h2
    by_contra hneq
    have := log_lt_sub_one_of_pos (div_pos h1 h2)
      (fun h' => hneq ((div_eq_one_iff_eq h2.ne').1 h'))
    rw [log_div h1.ne' h2.ne'] at this
    simp only [Pi.zero_apply, h, r] at hx
    linarith
  -- and `∫ q dν = 1 = ∫ f dν`, so `f = q` `ν`-a.e.
  have hr1 : ∫ x, r x ∂μ₀ = 1 := by
    rw [integral_congr_ae (g := fun _ => (1 : ℝ)) ?_, integral_const, probReal_univ, one_smul]
    filter_upwards [hff₀, hpos₀] with x h1 h2
    simp only [r, h1, div_self h2.ne']
  have hfq : f =ᵐ[ν] q := by
    have h0 : ∫ x, (f x - q x) ∂ν = 0 := by
      rw [integral_sub hfi hqi, ← hrq, hr1, hf1, sub_self]
    have := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => sub_nonneg.2 (hq x).2)
      (hfi.sub hqi)).1 h0
    filter_upwards [this] with x hx
    simpa [sub_eq_zero] using hx
  refine hne ?_
  have hff₀' : ∀ᵐ x ∂ν, ENNReal.ofReal (f₀ x) ≠ 0 → f x = f₀ x := by
    rw [← ae_withDensity_iff hm₀, ← hμ]; exact hff₀
  filter_upwards [hfq, hff₀'] with x h1 h2
  rcases (hf₀0 x).eq_or_lt with h0 | h0
  · rw [h1]; simp only [q, ← h0, zero_mul]
  · exact h2 (ENNReal.ofReal_pos.2 h0).ne'

end KL

section GPDIdent

variable {ξ σ ξ₀ σ₀ x : ℝ}

/-- The cumulative hazard `-log S(x)` of the GPD has derivative `1 / (σ + ξ x)` inside the
support, for every shape. -/
lemma hasDerivAt_neg_log_gpdSurvival (hσ : 0 < σ) (hu : 0 < 1 + ξ * x / σ) :
    HasDerivAt (fun y => -log (gpdSurvival ξ σ y)) (1 / (σ + ξ * x)) x := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp only [gpdSurvival_of_eq_zero, log_exp, neg_div, neg_neg, zero_mul, add_zero]
    exact (hasDerivAt_id x).div_const σ
  have hcu : ContinuousAt (fun y => 1 + ξ * y / σ) x := by fun_prop
  have heq : (fun y => (1 / ξ) * log (1 + ξ * y / σ)) =ᶠ[𝓝 x]
      fun y => -log (gpdSurvival ξ σ y) := by
    filter_upwards [hcu.eventually (lt_mem_nhds hu)] with y hy
    simp only [gpdSurvival, hξ, ↓reduceIte, max_eq_left hy.le]
    rw [log_rpow hy]
    ring
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq.symm
  have := (((((hasDerivAt_id x).const_mul ξ).div_const σ).const_add 1).log hu.ne').const_mul
    (1 / ξ)
  refine this.congr_deriv ?_
  have : σ + ξ * x ≠ 0 := by
    have : σ + ξ * x = σ * (1 + ξ * x / σ) := by field_simp
    rw [this]; positivity
  simp only [id]
  field_simp

private lemma one_add_pos_of_lt_div (hσ : 0 < σ) (hx : 0 ≤ x) (hxδ : x < σ / (|ξ| + 1)) :
    0 < 1 + ξ * x / σ := by
  have h1 : |ξ| * x ≤ |ξ| * (σ / (|ξ| + 1)) := mul_le_mul_of_nonneg_left hxδ.le (abs_nonneg ξ)
  have h2 : |ξ| * (σ / (|ξ| + 1)) < σ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have h3 : -(|ξ| * x) ≤ ξ * x := by
    have := neg_abs_le ξ
    nlinarith
  have : 1 + ξ * x / σ = (σ + ξ * x) / σ := by field_simp
  rw [this]
  exact div_pos (by linarith) hσ

/-- **Identifiability of the GPD family, all shapes**: `GPD(ξ, σ) = GPD(ξ₀, σ₀)` forces
`ξ = ξ₀` and `σ = σ₀`. Near `0` both laws have cumulative hazard with derivative
`1 / (σ + ξ x)`. -/
theorem gpd_params_eq_of_gpdMeasure_eq' (hσ : 0 < σ) (hσ₀ : 0 < σ₀)
    (h : gpdMeasure ξ σ = gpdMeasure ξ₀ σ₀) : ξ = ξ₀ ∧ σ = σ₀ := by
  have hS : ∀ x, 0 ≤ x → gpdSurvival ξ σ x = gpdSurvival ξ₀ σ₀ x := fun x hx => by
    have := gpdMeasure_Ioi (ξ := ξ) hσ hx
    rw [h, gpdMeasure_Ioi hσ₀ hx] at this
    exact ((ENNReal.ofReal_eq_ofReal_iff (gpdSurvival_nonneg _ _ _)
      (gpdSurvival_nonneg _ _ _)).1 this).symm
  set δ := min (σ / (|ξ| + 1)) (σ₀ / (|ξ₀| + 1))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have heq : ∀ x, 0 < x → x < δ → 1 / (σ + ξ * x) = 1 / (σ₀ + ξ₀ * x) := fun x hx hxδ => by
    have hu := one_add_pos_of_lt_div hσ hx.le (hxδ.trans_le (min_le_left _ _))
    have hu₀ := one_add_pos_of_lt_div hσ₀ hx.le (hxδ.trans_le (min_le_right _ _))
    have hev : (fun y => -log (gpdSurvival ξ σ y)) =ᶠ[𝓝 x]
        fun y => -log (gpdSurvival ξ₀ σ₀ y) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      rw [hS y hy.le]
    exact (hasDerivAt_neg_log_gpdSurvival hσ hu).unique
      ((hasDerivAt_neg_log_gpdSurvival hσ₀ hu₀).congr_of_eventuallyEq hev)
  have hpos : ∀ x, 0 < x → x < δ → 0 < σ + ξ * x ∧ 0 < σ₀ + ξ₀ * x := fun x hx hxδ => by
    have hu := one_add_pos_of_lt_div hσ hx.le (hxδ.trans_le (min_le_left _ _))
    have hu₀ := one_add_pos_of_lt_div hσ₀ hx.le (hxδ.trans_le (min_le_right _ _))
    have e1 : σ + ξ * x = σ * (1 + ξ * x / σ) := by field_simp
    have e2 : σ₀ + ξ₀ * x = σ₀ * (1 + ξ₀ * x / σ₀) := by field_simp
    rw [e1, e2]; exact ⟨by positivity, by positivity⟩
  have key : ∀ x, 0 < x → x < δ → σ + ξ * x = σ₀ + ξ₀ * x := fun x hx hxδ => by
    have := heq x hx hxδ
    obtain ⟨p1, p2⟩ := hpos x hx hxδ
    rw [div_eq_div_iff p1.ne' p2.ne'] at this
    linarith
  have e1 := key (δ / 2) (by positivity) (by linarith)
  have e2 := key (δ / 3) (by positivity) (by linarith)
  have hξ : ξ = ξ₀ := by
    have : (ξ - ξ₀) * (δ / 2 - δ / 3) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h (by linarith)
  exact ⟨hξ, by subst hξ; linarith⟩

/-- **The Kullback–Leibler inequality for the GPD family, all shapes.** If the support of
`GPD(ξ, σ)` carries `GPD(ξ₀, σ₀)` (i.e. `g_{ξ,σ} > 0` a.s. under `GPD(ξ₀, σ₀)`), the
log-densities are integrable and `(ξ, σ) ≠ (ξ₀, σ₀)`, then
`E log g_{ξ,σ}(X) < E log g_{ξ₀,σ₀}(X)`. -/
theorem integral_log_gpdDensity_lt' (hσ : 0 < σ) (hσ₀ : 0 < σ₀) (hne : ¬ (ξ = ξ₀ ∧ σ = σ₀))
    (hpos : ∀ᵐ x ∂gpdMeasure ξ₀ σ₀, 0 < gpdDensity ξ σ x)
    (hi : Integrable (fun x => log (gpdDensity ξ σ x)) (gpdMeasure ξ₀ σ₀)) :
    ∫ x, log (gpdDensity ξ σ x) ∂gpdMeasure ξ₀ σ₀ <
      ∫ x, log (gpdDensity ξ₀ σ₀ x) ∂gpdMeasure ξ₀ σ₀ := by
  refine integral_log_lt_of_density (measurable_gpdDensity ξ σ) (measurable_gpdDensity ξ₀ σ₀)
    (gpdDensity_nonneg hσ ξ) (gpdDensity_nonneg hσ₀ ξ₀) (gpdMeasure_eq_withDensity hσ₀)
    (integrable_gpdDensity hσ) (integral_gpdDensity hσ) hpos hi
    (integrable_log_gpdDensity_self hσ₀) fun hae => hne ?_
  refine gpd_params_eq_of_gpdMeasure_eq' hσ hσ₀ ?_
  rw [gpdMeasure_eq_withDensity hσ, gpdMeasure_eq_withDensity hσ₀]
  exact withDensity_congr_ae (hae.mono fun x hx => by simp only; rw [hx])

end GPDIdent

/-! ### Strong consistency of the joint MLE -/

section JointMLE

variable {K : Set (ℝ × ℝ)}

/-- A finite sum of continuous `EReal`-valued functions that never take the value `⊤` is
continuous. -/
lemma continuousOn_finsetSum_ereal {β ι : Type*} [TopologicalSpace β] {S : Set β}
    (s : Finset ι) {F : ι → β → EReal} (hF : ∀ i ∈ s, ContinuousOn (F i) S)
    (htop : ∀ i ∈ s, ∀ p ∈ S, F i p ≠ ⊤) :
    ContinuousOn (fun p => ∑ i ∈ s, F i p) S ∧ ∀ p ∈ S, ∑ i ∈ s, F i p ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact ⟨continuousOn_const, fun _ _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      (fun i hi => htop i (Finset.mem_insert_of_mem hi))
    have ha1 := hF a (Finset.mem_insert_self a s)
    have ha2 := htop a (Finset.mem_insert_self a s)
    simp only [Finset.sum_insert ha]
    refine ⟨fun p hp => ?_, fun p hp => EReal.add_ne_top (ha2 p hp) (ih2 p hp)⟩
    exact (EReal.continuousAt_add (p := (F a p, ∑ i ∈ s, F i p)) (Or.inl (ha2 p hp))
      (Or.inr (ih2 p hp))).comp_continuousWithinAt
      (f := fun q => (F a q, ∑ i ∈ s, F i q)) ((ha1 p hp).prodMk (ih1 p hp))

private lemma exists_lower_bound_snd (hK : IsCompact K) (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2)
    (hne : K.Nonempty) : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, c ≤ p.2 := by
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
  exact ⟨p₀.2, (hKS p₀ hp₀).2, fun p hp => hmin hp⟩

/-- **Existence of the joint MLE on a compact parameter set** `K ⊂ {ξ > -1, σ > 0}`, for the
extended-real log-likelihood (which is continuous on `K`). -/
theorem exists_isMaxOn_gpdLogLikE (hK : IsCompact K) (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2)
    (hne : K.Nonempty) {n : ℕ} (x : Fin n → ℝ) :
    ∃ θ ∈ K, IsMaxOn (fun p : ℝ × ℝ => gpdLogLikE p.1 p.2 x) K θ := by
  refine hK.exists_isMaxOn hne ?_
  refine (continuousOn_finsetSum_ereal Finset.univ
    (fun i _ => (continuousOn_gpdLogDensityE (x i)).mono fun p hp => hKS p hp)
    (fun i _ p hp => ?_)).1
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (gpdLogDensityE_le (hKS p hp).1 (hKS p hp).2 (x i))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- **Strong consistency of the joint GPD maximum likelihood estimator, all shapes `ξ > -1`.**
Let `K` be a compact set of parameters `(ξ, σ)` with `ξ > -1`, `σ > 0` (for instance a compact
subset of the regular region `{ξ > -1/2, σ > 0}`), containing the true parameter `θ₀`, and let
`X₀, X₁, …` be iid `GPD(θ₀)`. Almost surely, every sequence `θ̂ₙ ∈ K` of approximate maximizers
of the extended-real log-likelihood over `K` — `ℓₙ(θ₀) ≤ ℓₙ(θ̂ₙ) + n εₙ` eventually, with
`εₙ → 0` (for instance exact maximizers, which exist by `exists_isMaxOn_gpdLogLikE`) — converges
to `θ₀`. Shapes `ξ ≤ 0`, where the support `[0, -σ/ξ]` depends on the parameters, are allowed:
the log-likelihood is `-∞` at parameters under which some observation is impossible. -/
theorem ae_tendsto_gpdMLE' (hK : IsCompact K) (hKS : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2)
    {θ₀ : ℝ × ℝ} (hθ₀ : θ₀ ∈ K) (hX : ∀ i, HasLaw (X i) (gpdMeasure θ₀.1 θ₀.2) P)
    (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, ∀ (θhat : ℕ → ℝ × ℝ) (ε : ℕ → ℝ), (∀ n, θhat n ∈ K) → Tendsto ε atTop (𝓝 0) →
      (∀ᶠ n in atTop, gpdLogLikE θ₀.1 θ₀.2 (fun i : Fin n => X i ω) ≤
        gpdLogLikE (θhat n).1 (θhat n).2 (fun i : Fin n => X i ω) + ((n * ε n : ℝ) : EReal)) →
      Tendsto θhat atTop (𝓝 θ₀) := by
  obtain ⟨c, hc, hcK⟩ := exists_lower_bound_snd hK hKS ⟨θ₀, hθ₀⟩
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  set m : K → ℝ → EReal := fun θ x => gpdLogDensityE θ.1.1 θ.1.2 x
  set G : ℝ → ℝ := fun _ => -log c
  have hθ₀S := hKS θ₀ hθ₀
  have hbound : ∀ θ x, m θ x ≤ G x := fun θ x =>
    (gpdLogDensityE_le (hKS θ.1 θ.2).1 (hKS θ.1 θ.2).2 x).trans
      (EReal.coe_le_coe_iff.2 (neg_le_neg (log_le_log hc (hcK θ.1 θ.2))))
  have hcont : ∀ x, Continuous fun θ => m θ x := fun x =>
    (continuousOn_gpdLogDensityE x).comp_continuous continuous_subtype_val
      fun θ => hKS θ.1 θ.2
  have hmeas : ∀ θ, Measurable (m θ) := fun θ => measurable_gpdLogDensityE _ _
  have hint₀ : Integrable (fun x => (m ⟨θ₀, hθ₀⟩ x).toReal) (gpdMeasure θ₀.1 θ₀.2) := by
    simp only [m, toReal_gpdLogDensityE]
    exact integrable_log_gpdDensity_self hθ₀S.2
  have hident : ∀ θ : K, θ ≠ ⟨θ₀, hθ₀⟩ → (∀ᵐ x ∂gpdMeasure θ₀.1 θ₀.2, m θ x ≠ ⊥) →
      Integrable (fun x => (m θ x).toReal) (gpdMeasure θ₀.1 θ₀.2) →
      ∫ x, (m θ x).toReal ∂gpdMeasure θ₀.1 θ₀.2 <
        ∫ x, (m ⟨θ₀, hθ₀⟩ x).toReal ∂gpdMeasure θ₀.1 θ₀.2 := by
    intro θ hne hfin hi
    simp only [m, toReal_gpdLogDensityE] at hi ⊢
    refine integral_log_gpdDensity_lt' (hKS θ.1 θ.2).2 hθ₀S.2
      (fun h => hne (Subtype.ext (Prod.ext h.1 h.2))) ?_ hi
    filter_upwards [hfin] with x hx
    rw [gpdLogDensityE_ne_bot_iff] at hx
    exact gpdDensity_pos_of_mem (hKS θ.1 θ.2).2 hx.1 hx.2
  have h₀ : ∀ᵐ x ∂gpdMeasure θ₀.1 θ₀.2, m ⟨θ₀, hθ₀⟩ x ≠ ⊥ := ae_gpdLogDensityE_ne_bot hθ₀S.2
  filter_upwards [ae_tendsto_of_wald_ereal_of_continuous (θ₀ := ⟨θ₀, hθ₀⟩) hX hind hcont hmeas
    (integrable_const _) hbound h₀ hint₀ hident]
    with ω hω θhat ε hθK hε hθ
  have := hω (fun n => ⟨θhat n, hθK n⟩) ε hε (hθ.mono fun n hn => by
    simp only [gpdLogLikE] at hn
    rw [Fin.sum_univ_eq_sum_range (fun i => gpdLogDensityE θ₀.1 θ₀.2 (X i ω)) n,
      Fin.sum_univ_eq_sum_range (fun i => gpdLogDensityE (θhat n).1 (θhat n).2 (X i ω)) n] at hn
    exact hn)
  exact (continuous_subtype_val.tendsto _).comp this

end JointMLE

/-! Deprecated names from when the all-shape GPD survival function was `gpdSurvival'`. -/

@[deprecated (since := "2026-10-19")] alias hasDerivAt_neg_log_gpdSurvival' := hasDerivAt_neg_log_gpdSurvival

end ExtremeValueTheory
