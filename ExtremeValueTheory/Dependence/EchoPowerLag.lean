import ExtremeValueTheory.Dependence.EchoPhaseTransition

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section PowerMoment

variable {α γ : ℝ}

/-- `E[Z^γ; u < Z ≤ R] = α / (α - γ) (u^(γ - α) - R^(γ - α))` for `Z` Pareto(`α`), `1 ≤ u ≤ R`. -/
theorem setIntegral_Ioc_rpow_pareto (hα : 0 < α) (hγα : γ < α) {u R : ℝ} (hu : 1 ≤ u)
    (huR : u ≤ R) :
    ∫ z in Ioc u R, z ^ γ ∂(paretoMeasure 1 α) =
      α / (α - γ) * (u ^ (γ - α) - R ^ (γ - α)) := by
  have hu0 : 0 < u := one_pos.trans_le hu
  have hm : Measurable (paretoPDF 1 α) := (measurable_paretoPDFReal 1 α).ennreal_ofReal
  rw [paretoMeasure, setIntegral_withDensity_eq_setIntegral_toReal_smul (f := paretoPDF 1 α) hm
    (ae_of_all _ fun _ => by simp [paretoPDF]) _ measurableSet_Ioc]
  have e : ∀ z ∈ Ioc u R, (paretoPDF 1 α z).toReal • z ^ γ = α * z ^ (γ - α - 1) := by
    intro z hz
    have hz0 : 0 < z := hu0.trans hz.1
    rw [paretoPDF_of_le (hu.trans hz.1.le), Real.one_rpow, mul_one,
      ENNReal.toReal_ofReal (mul_nonneg hα.le (Real.rpow_pos_of_pos hz0 _).le), smul_eq_mul,
      mul_assoc, ← Real.rpow_add hz0]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioc e, ← intervalIntegral.integral_of_le huR,
    intervalIntegral.integral_const_mul, integral_rpow]
  · have h1 : γ - α - 1 + 1 = γ - α := by ring
    have h2 : γ - α ≠ 0 := by linarith
    rw [h1]
    field_simp
    ring
  · right
    refine ⟨by linarith, fun h0 => ?_⟩
    rw [Set.mem_uIcc] at h0
    rcases h0 with h0 | h0 <;> linarith

/-- **The shape of the critical cluster ratio**:
`φ_β(κ) = (β min(κ, 1) - min(κ, 1)^β) / (β - 1)`. For `V` Pareto(`β`), `β > 1`, `κ ≥ 0`,
`φ_β(κ) = E[min(κ V, 1)]`; it increases from `φ_β(0) = 0` to `φ_β(κ) = 1` for `κ ≥ 1`. -/
noncomputable def echoShape (β κ : ℝ) : ℝ := (β * min κ 1 - min κ 1 ^ β) / (β - 1)

theorem echoShape_of_one_le {β κ : ℝ} (hβ : 1 < β) (hκ : 1 ≤ κ) : echoShape β κ = 1 := by
  rw [echoShape, min_eq_right hκ, Real.one_rpow, mul_one, div_self (by linarith)]

theorem echoShape_zero {β : ℝ} (hβ : 1 < β) : echoShape β 0 = 0 := by
  rw [echoShape, min_eq_left zero_le_one, Real.zero_rpow (by linarith)]
  simp

theorem continuous_echoShape {β : ℝ} (hβ : 1 < β) : Continuous (echoShape β) := by
  unfold echoShape
  refine Continuous.div_const (Continuous.sub (continuous_const.mul
    (continuous_id.min continuous_const)) ?_) _
  exact (continuous_id.min continuous_const).rpow_const fun _ => Or.inr (by linarith)

/-- `φ_β(κ) < 1` for `0 ≤ κ < 1` (Bernoulli's inequality). -/
theorem echoShape_lt_one {β κ : ℝ} (hβ : 1 < β) (hκ0 : 0 ≤ κ) (hκ : κ < 1) :
    echoShape β κ < 1 := by
  rw [echoShape, min_eq_left hκ.le, div_lt_one (by linarith)]
  have := one_add_mul_self_lt_rpow_one_add (s := κ - 1) (by linarith) (by linarith) hβ
  rw [show 1 + (κ - 1) = κ by ring] at this
  linarith

/-- **Truncated moment of the Pareto law.** For `Z` Pareto(`α`), `0 < γ < α`, `u ≥ 1`, `r > 0`:
`E[min(Z^γ, r); Z > u] = r u^(-α) φ_{α/γ}(u^γ / r)`. -/
theorem setIntegral_min_rpow_pareto (hα : 0 < α) (hγ : 0 < γ) (hγα : γ < α) {u r : ℝ}
    (hu : 1 ≤ u) (hr : 0 < r) :
    ∫ z in Ioi u, min (z ^ γ) r ∂(paretoMeasure 1 α) =
      r * u ^ (-α) * echoShape (α / γ) (u ^ γ / r) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hu0 : 0 < u := one_pos.trans_le hu
  have hβ : 1 < α / γ := (one_lt_div hγ).2 hγα
  rcases le_or_gt r (u ^ γ) with hle | hlt
  · rw [echoShape_of_one_le hβ ((one_le_div hr).2 hle), mul_one,
      setIntegral_congr_fun measurableSet_Ioi (g := fun _ => r) fun z hz => min_eq_right
        (hle.trans (Real.rpow_le_rpow hu0.le (le_of_lt hz) hγ.le)),
      setIntegral_const, smul_eq_mul, paretoMeasure_one_real_Ioi hα hu, mul_comm]
  · set R := r ^ (1 / γ) with hR
    have hRγ : R ^ γ = r := by
      rw [hR, ← Real.rpow_mul hr.le, one_div_mul_cancel hγ.ne', Real.rpow_one]
    have huR : u < R := by
      rw [← Real.rpow_lt_rpow_iff hu0.le (Real.rpow_nonneg hr.le _) hγ, hRγ]
      exact hlt
    have hR0 : 0 < R := hu0.trans huR
    have hint : IntegrableOn (fun z => min (z ^ γ) r) (Ioi u) (paretoMeasure 1 α) := by
      refine (integrable_const r).mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi
        fun z hz => ?_)
      · exact ((measurable_id.pow_const γ).min measurable_const).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (le_min (Real.rpow_nonneg (hu0.trans hz).le _) hr.le)]
        exact min_le_right _ _
    rw [← Ioc_union_Ioi_eq_Ioi huR.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self)
      (hint.mono_set (Ioi_subset_Ioi huR.le)),
      setIntegral_congr_fun measurableSet_Ioc (g := fun z => z ^ γ) fun z hz => min_eq_left
        (by rw [← hRγ]; exact Real.rpow_le_rpow (hu0.trans hz.1).le hz.2 hγ.le),
      setIntegral_congr_fun measurableSet_Ioi (g := fun _ => r) fun z hz => min_eq_right
        (by rw [← hRγ]; exact Real.rpow_le_rpow hR0.le (le_of_lt hz) hγ.le),
      setIntegral_const, smul_eq_mul, paretoMeasure_one_real_Ioi hα (hu.trans huR.le),
      setIntegral_Ioc_rpow_pareto hα hγα hu huR.le]
    have hκ : u ^ γ / r < 1 := (div_lt_one hr).2 hlt
    rw [echoShape, min_eq_left hκ.le]
    -- the algebra
    have e1 : u ^ (γ - α) = u ^ γ * u ^ (-α) := by
      rw [sub_eq_add_neg, Real.rpow_add hu0]
    have e2 : R ^ (γ - α) = r * R ^ (-α) := by
      rw [sub_eq_add_neg, Real.rpow_add hR0, hRγ]
    have e3 : R ^ (-α) = r ^ (-(α / γ)) := by
      rw [hR, ← Real.rpow_mul hr.le]
      ring_nf
    have e4 : (u ^ γ / r) ^ (α / γ) = u ^ α * r ^ (-(α / γ)) := by
      rw [Real.div_rpow (Real.rpow_nonneg hu0.le _) hr.le, ← Real.rpow_mul hu0.le,
        mul_div_cancel₀ _ hγ.ne', Real.rpow_neg hr.le, div_eq_mul_inv]
    have e5 : u ^ (-α) * u ^ α = 1 := by
      rw [← Real.rpow_add hu0, neg_add_cancel, Real.rpow_zero]
    rw [e1, e2, e3, e4]
    have hαγ : α - γ ≠ 0 := by linarith
    have hb : α / γ - 1 ≠ 0 := by linarith
    field_simp
    linear_combination (γ * r * r ^ (-(α / γ))) * e5

end PowerMoment

end ExtremeValueTheory
