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
    exact ((continuousAt_const.add continuousAt_id).log (by simp only [Pi.add_apply, id]; linarith)).div continuousAt_id h0

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
      (measurableSet_lt measurable_const (measurable_const.add ((measurable_const.mul measurable_id).div_const σ)))
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

end LogDensityE

end ExtremeValueTheory
