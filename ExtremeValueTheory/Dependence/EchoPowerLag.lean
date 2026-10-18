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

/-! ### Anticlustering of the echo process for blocks shorter than the echo lag -/

section EchoAC

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}
  (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω) (hLm : Measurable L)
  (hL1 : ∀ z, 1 ≤ L z)

include hα hZ hlaw hLm hL1 in
omit [IsProbabilityMeasure P] in
theorem tsum_measure_echoSource (t : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    ∑' j, P (echoSource L Z t x j) = ENNReal.ofReal (2 * x ^ (-α)) := by
  have hs := hasSum_measureReal_echoSource hα hZ hlaw hLm hL1 (P := P) t hx
  have hfin : ∀ j, P (echoSource L Z t x j) ≠ ∞ := fun j => by
    rw [echoSource_eq, measure_preimage_eq hZ hlaw _ (measurableSet_echoSourceSet hLm x j)]
    have := isProbabilityMeasure_paretoMeasure one_pos hα
    exact measure_ne_top _ _
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hs.summable]
  exact tsum_congr fun j => (ofReal_measureReal (hfin j)).symm

include hα hZ hind hlaw hpos hLm hL1 in
/-- **Two-sided pair bound inside a short window.** If every innovation `z ≥ x` has echo lag
`L(z) > r`, then `P(X_0 > x, X_t > x for some 1 ≤ |t| ≤ r) ≤ (2 r + 1) (2 x^(-α))²`: within the
window, the exceedance at `0` and the other exceedance never come from the same innovation, and
distinct innovations are independent. -/
theorem measureReal_pair_window_le {x : ℝ} (hx : 1 ≤ x) {r : ℕ} (hshort : ∀ z, x ≤ z → r < L z)
    (m : ℕ) (hm : 1 ≤ m) :
    P.real {ω | x < |echoProcess L Z 0 ω| ∧
        ∃ t : ℤ, (m : ℤ) ≤ |t| ∧ |t| ≤ r ∧ x < |echoProcess L Z t ω|} ≤
      (2 * r + 1) * (2 * x ^ (-α)) ^ 2 := by
  set T : Finset ℤ := (Finset.Icc (-(r : ℤ)) r).erase 0
  have hsub : {ω | x < |echoProcess L Z 0 ω| ∧
      ∃ t : ℤ, (m : ℤ) ≤ |t| ∧ |t| ≤ r ∧ x < |echoProcess L Z t ω|} ⊆
      ⋃ t ∈ T, ⋃ j, ⋃ j', echoSource L Z 0 x j ∩ echoSource L Z t x j' := by
    rintro ω ⟨h0, t, h1, h2, h3⟩
    rw [abs_of_nonneg (echoProcess_nonneg hpos _ _)] at h0 h3
    obtain ⟨j, hj⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (by linarith) 0 h0)
    obtain ⟨j', hj'⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (by linarith) t h3)
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at h1
      omega
    refine mem_iUnion₂.2 ⟨t, ?_, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨j', hj, hj'⟩⟩⟩
    simp only [T, Finset.mem_erase, Finset.mem_Icc]
    refine ⟨ht0, ?_, ?_⟩ <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
  have hb : ∀ t ∈ T, P (⋃ j, ⋃ j', echoSource L Z 0 x j ∩ echoSource L Z t x j') ≤
      ENNReal.ofReal (2 * x ^ (-α)) * ENNReal.ofReal (2 * x ^ (-α)) := by
    intro t ht
    simp only [T, Finset.mem_erase, Finset.mem_Icc] at ht
    have hz : ∀ z, x ≤ z → t.natAbs < L z := fun z hz => by
      have := hshort z hz
      omega
    calc _ ≤ ∑' j, ∑' j', P (echoSource L Z 0 x j ∩ echoSource L Z t x j') :=
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => measure_iUnion_le _)
      _ ≤ ∑' j, ∑' j', P (echoSource L Z 0 x j) * P (echoSource L Z t x j') :=
          ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun j' =>
            measure_echoSource_inter_le hind ht.1 hz hLm le_rfl j j'
      _ = _ := by
          simp_rw [ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_mul_right, tsum_measure_echoSource hα hZ hlaw hLm hL1 0 hx,
            tsum_measure_echoSource hα hZ hlaw hLm hL1 t hx]
  have hcard : (T.card : ℝ) ≤ 2 * r + 1 := by
    have : T.card ≤ (Finset.Icc (-(r : ℤ)) r).card := Finset.card_erase_le
    rw [Int.card_Icc] at this
    have h' : ((r : ℤ) + 1 - -(r : ℤ)).toNat = 2 * r + 1 := by omega
    rw [h'] at this
    exact_mod_cast this
  have hP : P (⋃ t ∈ T, ⋃ j, ⋃ j', echoSource L Z 0 x j ∩ echoSource L Z t x j') ≤
      T.card * (ENNReal.ofReal (2 * x ^ (-α)) * ENNReal.ofReal (2 * x ^ (-α))) :=
    (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum hb).trans_eq (by simp))
  have h2 : 0 ≤ 2 * x ^ (-α) := by positivity
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  rw [measureReal_def]
  refine (ENNReal.toReal_mono ?_ hP).trans ?_
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal h2, ENNReal.toReal_natCast]
    rw [sq]
    exact mul_le_mul_of_nonneg_right hcard (mul_nonneg h2 h2)

include hα hZ hind hlaw hpos hLm hL1 in
/-- **Anticlustering for blocks shorter than the echo lag.** For iid Pareto(`α`) innovations and
any measurable echo lag `L ≥ 1`: if `uₙ → ∞`, `rₙ uₙ^(-α) → 0` and eventually every innovation
`z ≥ uₙ` has echo lag `L(z) > rₙ`, then the (two-sided) anticlustering condition holds along
`uₙ`, `rₙ`, already with `m = 1`. -/
theorem antiClusteringAt_echoProcess {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {r : ℕ → ℕ}
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hshort : ∀ᶠ n in atTop, ∀ z, u n ≤ z → r n < L z) :
    AntiClusteringAt P (echoProcess L Z) u r := by
  intro ε hε
  refine ⟨1, ?_⟩
  have hb : Tendsto (fun n => u n ^ (-α)) atTop (𝓝 0) := (tendsto_rpow_neg_atTop hα).comp hu
  have hlim : Tendsto (fun n => 4 * (2 * ((r n : ℝ) * u n ^ (-α)) + u n ^ (-α))) atTop (𝓝 0) := by
    simpa using ((hrb.const_mul 2).add hb).const_mul 4
  filter_upwards [hshort, hu.eventually_ge_atTop 1, hlim.eventually (ge_mem_nhds hε)]
    with n hn hun hεn
  have hb0 : 0 < u n ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
  have hX0 : u n ^ (-α) ≤ P.real {ω | u n < |echoProcess L Z 0 ω|} := by
    rw [← measureReal_lt_of_map_eq hZ hlaw hα 0 hun]
    exact measureReal_mono fun ω hω => lt_of_lt_of_le hω
      ((le_echoProcess 0 ω).trans (le_abs_self _))
  refine (measureReal_pair_window_le hα hZ hind hlaw hpos hLm hL1 hun hn 1 le_rfl).trans ?_
  calc (2 * (r n : ℝ) + 1) * (2 * u n ^ (-α)) ^ 2
      = 4 * (2 * ((r n : ℝ) * u n ^ (-α)) + u n ^ (-α)) * u n ^ (-α) := by ring
    _ ≤ ε * u n ^ (-α) := mul_le_mul_of_nonneg_right hεn hb0.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hX0 hε.le

end EchoAC

end ExtremeValueTheory
