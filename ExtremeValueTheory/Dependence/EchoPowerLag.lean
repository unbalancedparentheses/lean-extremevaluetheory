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

/-! ### The power echo lag `L(z) = ⌊z^γ⌋₊ + 1` -/

section PowLag

variable {α γ : ℝ}

/-- The power echo lag `L(z) = ⌊z^γ⌋₊ + 1` (`≈ z^γ`, and `≥ 1`). -/
noncomputable def powLag (γ z : ℝ) : ℕ := ⌊z ^ γ⌋₊ + 1

theorem measurable_powLag (γ : ℝ) : Measurable (powLag γ) :=
  (Nat.measurable_floor.comp (measurable_id.pow_const γ)).add_const 1

theorem one_le_powLag (γ z : ℝ) : 1 ≤ powLag γ z := Nat.le_add_left 1 _

theorem tendsto_powLag (hγ : 0 < γ) : Tendsto (powLag γ) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_succ _)
    (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hγ))

theorem rpow_lt_powLag (γ z : ℝ) : z ^ γ < powLag γ z := by
  simp only [powLag, Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one _

theorem powLag_le {z : ℝ} (hz : 0 ≤ z) : (powLag γ z : ℝ) ≤ z ^ γ + 1 := by
  simp only [powLag, Nat.cast_add, Nat.cast_one]
  linarith [Nat.floor_le (Real.rpow_nonneg hz γ)]

/-- The tail of the power lag: `P(L(Z) ≥ j + 2) ≤ (j + 1)^(-α/γ)`. -/
theorem measureReal_powLag_le (hα : 0 < α) (hγ : 0 < γ) (j : ℕ) :
    (paretoMeasure 1 α).real {z | j + 1 + 1 ≤ powLag γ z} ≤ ((j : ℝ) + 1) ^ (-(α / γ)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set x : ℝ := ((j : ℝ) + 1) ^ (1 / γ)
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := j.cast_nonneg (α := ℝ); linarith
  have hx : 1 ≤ x := Real.one_le_rpow hj (by positivity)
  calc (paretoMeasure 1 α).real {z | j + 1 + 1 ≤ powLag γ z}
      ≤ (paretoMeasure 1 α).real (Ioi x ∪ {x}) := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
        filter_upwards [ae_one_lt_paretoMeasure (α := α)] with z hz1 hz
        have hz' : j + 1 ≤ ⌊z ^ γ⌋₊ := by simpa [powLag] using hz
        have hle : (j : ℝ) + 1 ≤ z ^ γ := by
          have := (Nat.cast_le (α := ℝ)).2 hz'
          push_cast at this
          exact this.trans (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
        have hxz : x ≤ z := by
          have := Real.rpow_le_rpow (by linarith) hle (by positivity : (0 : ℝ) ≤ 1 / γ)
          rwa [← Real.rpow_mul (by linarith), mul_one_div_cancel hγ.ne', Real.rpow_one] at this
        rcases hxz.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h.symm
    _ ≤ (paretoMeasure 1 α).real (Ioi x) + (paretoMeasure 1 α).real {x} := measureReal_union_le _ _
    _ = ((j : ℝ) + 1) ^ (-(α / γ)) := by
        rw [paretoMeasure_one_real_Ioi hα hx, measureReal_def, paretoMeasure_singleton,
          ENNReal.toReal_zero, add_zero, ← Real.rpow_mul (by linarith)]
        congr 1
        ring

/-- `E[L(Z)] < ∞` for the power lag, when `γ < α`. -/
theorem summable_powLag (hα : 0 < α) (hγ : 0 < γ) (hγα : γ < α) :
    Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ powLag γ z} := by
  refine (summable_nat_add_iff 1).1 ?_
  have hs : Summable fun j : ℕ => ((j : ℝ) + 1) ^ (-(α / γ)) := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2
      (show -(α / γ) < -1 by have := (one_lt_div hγ).2 hγα; linarith))
    simpa using h
  refine hs.of_nonneg_of_le (fun _ => measureReal_nonneg) fun j => ?_
  simpa using measureReal_powLag_le hα hγ j

/-- **Block mass of the power lag.** With `I = E[min(Z^γ, r); Z > u] = r u^(-α) φ_{α/γ}(u^γ / r)`,
`I ≤ E[min(L(Z), r); Z > u] ≤ I + u^(-α)`. -/
theorem echoBlockMass_powLag_bounds (hα : 0 < α) (hγ : 0 < γ) (hγα : γ < α) {u : ℝ}
    (hu : 1 ≤ u) {r : ℕ} (hr : 0 < r) :
    r * u ^ (-α) * echoShape (α / γ) (u ^ γ / r) ≤ echoBlockMass α (powLag γ) u r ∧
      echoBlockMass α (powLag γ) u r ≤
        r * u ^ (-α) * echoShape (α / γ) (u ^ γ / r) + u ^ (-α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hu0 : 0 < u := one_pos.trans_le hu
  have hR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [← setIntegral_min_rpow_pareto hα hγ hγα hu hR]
  have hint1 : IntegrableOn (fun z => min (z ^ γ) (r : ℝ)) (Ioi u) (paretoMeasure 1 α) := by
    refine (integrable_const (r : ℝ)).mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi
      fun z hz => ?_)
    · exact ((measurable_id.pow_const γ).min measurable_const).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (le_min (Real.rpow_nonneg (hu0.trans hz).le _) hR.le)]
      exact min_le_right _ _
  have hint2 := integrable_min_lag hα (measurable_powLag γ) u r
  have hpt : ∀ z ∈ Ioi u, min (z ^ γ) (r : ℝ) ≤ ((min (powLag γ z) r : ℕ) : ℝ) ∧
      ((min (powLag γ z) r : ℕ) : ℝ) ≤ min (z ^ γ) (r : ℝ) + 1 := by
    intro z hz
    have hz0 : 0 ≤ z := (hu0.trans hz).le
    have h1 := rpow_lt_powLag γ z
    have h2 := powLag_le (γ := γ) hz0
    rw [Nat.cast_min]
    constructor
    · exact min_le_min h1.le le_rfl
    · rcases le_total (z ^ γ) r with h | h
      · rw [min_eq_left h]; exact (min_le_left _ _).trans h2
      · rw [min_eq_right h]; linarith [min_le_right (powLag γ z : ℝ) r]
  constructor
  · exact setIntegral_mono_on hint1 hint2 measurableSet_Ioi fun z hz => (hpt z hz).1
  · calc echoBlockMass α (powLag γ) u r
        ≤ ∫ z in Ioi u, (min (z ^ γ) (r : ℝ) + 1) ∂(paretoMeasure 1 α) :=
          setIntegral_mono_on hint2 (hint1.add (integrable_const 1)) measurableSet_Ioi
            fun z hz => (hpt z hz).2
      _ = _ := by
          rw [integral_add hint1 (integrable_const 1), setIntegral_const, smul_eq_mul, mul_one,
            paretoMeasure_one_real_Ioi hα hu]

end PowLag

/-! ### Polynomial scales -/

section Scales

/-- If `a_n ≥ 0` and `log a_n / log n → c > 0`, then `a_n → ∞`. -/
theorem tendsto_atTop_of_log_div_log {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) atTop (𝓝 c)) :
    Tendsto a atTop atTop := by
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n => Real.log (a n)) atTop atTop := by
    refine (h.pos_mul_atTop hc hL).congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    field_simp
  refine (Real.tendsto_exp_atTop.comp hlog).congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  have : a n ≠ 0 := fun h0 => by simp [h0] at hn
  exact Real.exp_log ((ha n).lt_of_ne' this)

/-- If `a_n > 0` and `log a_n / log n → c < 0`, then `a_n → 0`. -/
theorem tendsto_zero_of_log_div_log {a : ℕ → ℝ} (ha : ∀ᶠ n in atTop, 0 < a n) {c : ℝ}
    (hc : c < 0) (h : Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) atTop (𝓝 c)) :
    Tendsto a atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n => Real.log (a n)) atTop atBot := by
    refine (h.neg_mul_atTop hc hL).congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    field_simp
  refine (Real.tendsto_exp_atBot.comp hlog).congr' ?_
  filter_upwards [ha] with n hn
  exact Real.exp_log hn

/-- **The polynomial block regimes.** Let `uₙ → ∞` with `log uₙ / log n → 1 / α` and
`log rₙ / log n → ρ ∈ (0, 1)`. Then `rₙ → ∞`, `rₙ uₙ^(-α) → 0`, and
`log(uₙ^γ / rₙ) / log n → γ / α - ρ`. -/
theorem polyBlocks_scales {α γ ρ : ℝ} (hα : 0 < α) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    (hlu : Tendsto (fun n : ℕ => Real.log (u n) / Real.log n) atTop (𝓝 (1 / α)))
    {r : ℕ → ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hr : Tendsto (fun n : ℕ => Real.log (r n) / Real.log n) atTop (𝓝 ρ)) :
    Tendsto r atTop atTop ∧ Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log (u n ^ γ / r n) / Real.log n) atTop (𝓝 (γ / α - ρ)) := by
  have hrR : Tendsto (fun n => (r n : ℝ)) atTop atTop :=
    tendsto_atTop_of_log_div_log (fun n => Nat.cast_nonneg _) hρ0 hr
  have hrpos : ∀ᶠ n in atTop, (0 : ℝ) < r n := hrR.eventually_gt_atTop 0
  have hupos : ∀ᶠ n in atTop, 0 < u n := hu.eventually_gt_atTop 0
  refine ⟨tendsto_natCast_atTop_iff.1 hrR, ?_, ?_⟩
  · refine tendsto_zero_of_log_div_log ?_ (c := ρ - α * (1 / α)) (by field_simp; linarith) ?_
    · filter_upwards [hrpos, hupos] with n h1 h2
      exact mul_pos h1 (Real.rpow_pos_of_pos h2 _)
    · refine (hr.sub (hlu.const_mul α)).congr' ?_
      filter_upwards [hrpos, hupos, eventually_gt_atTop 1] with n h1 h2 hn
      have hn' : (1 : ℝ) < n := by exact_mod_cast hn
      have hl : Real.log n ≠ 0 := (Real.log_pos hn').ne'
      rw [Real.log_mul h1.ne' (Real.rpow_pos_of_pos h2 _).ne', Real.log_rpow h2]
      field_simp
      ring
  · have := (hlu.const_mul γ).sub hr
    rw [show γ * (1 / α) = γ / α by ring] at this
    refine this.congr' ?_
    filter_upwards [hrpos, hupos, eventually_gt_atTop 1] with n h1 h2 hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hl : Real.log n ≠ 0 := (Real.log_pos hn').ne'
    rw [Real.log_div (Real.rpow_pos_of_pos h2 _).ne' h1.ne', Real.log_rpow h2]
    field_simp

end Scales

/-! ### The power-lag echo process -/

section PowEcho

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α γ : ℝ} {Z : ℤ → Ω → ℝ}
  (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω)

include hα hZ hind hlaw hpos in
/-- **The power-lag echo process has `θ = 1/2 < 1 = ϑ`** (`0 < γ < α`): it is stationary, its
spectral tail process is `Θ_t = 1{t = 0}`, and its extremal index is `1/2`. -/
theorem powEchoProcess_theta_lt_vartheta (hγ : 0 < γ) (hγα : γ < α) :
    HasShiftInvariantWindows P (echoProcess (powLag γ) Z) ∧
      HasSpectralTailProcess P (echoProcess (powLag γ) Z) α (Measure.dirac ()) unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      HasExtremalIndex (fun k : ℕ => echoProcess (powLag γ) Z k) P (1 / 2) :=
  echoProcess_theta_lt_vartheta hα hZ hind hlaw hpos (measurable_powLag γ) (one_le_powLag γ)
    (tendsto_powLag hγ) (summable_powLag hα hγ hγα)

include hα hZ hind hlaw hpos in
/-- **The cluster ratio of the power-lag echo process at every block length**: with
`κₙ = uₙ^γ / rₙ` (echo lag of an exceedance over block length),
`clusterRatio - (1 + φ_{α/γ}(κₙ)) / 2 → 0`, for `uₙ → ∞`, `rₙ → ∞`, `rₙ uₙ^(-α) → 0`. -/
theorem tendsto_clusterRatio_sub_powEchoProcess (hγ : 0 < γ) (hγα : γ < α) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0)) :
    Tendsto (fun n => clusterRatio P (echoProcess (powLag γ) Z) u r n -
      (1 + echoShape (α / γ) (u n ^ γ / r n)) / 2) atTop (𝓝 0) := by
  have h := tendsto_clusterRatio_sub_echoProcess hα hZ hind hlaw hpos (measurable_powLag γ)
    (one_le_powLag γ) hu (hr.eventually_gt_atTop 0) hrb
  set d : ℕ → ℝ := fun n => echoBlockMass α (powLag γ) (u n) (r n) / (r n * u n ^ (-α)) -
    echoShape (α / γ) (u n ^ γ / r n)
  have hrinv : Tendsto (fun n => (1 : ℝ) / r n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_iff.2 hr)
  have hd : Tendsto d atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hrinv
    all_goals
      filter_upwards [hu.eventually_ge_atTop 1, hr.eventually_gt_atTop 0] with n hn hrn
      have hR : (0 : ℝ) < r n := by exact_mod_cast hrn
      have hb : 0 < u n ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
      obtain ⟨h1, h2⟩ := echoBlockMass_powLag_bounds hα hγ hγα hn hrn
      simp only [d]
    · rw [sub_nonneg, le_div_iff₀ (mul_pos hR hb)]
      linarith
    · rw [sub_le_iff_le_add, div_le_iff₀ (mul_pos hR hb)]
      have e : (1 / (r n : ℝ) + echoShape (α / γ) (u n ^ γ / r n)) * (r n * u n ^ (-α)) =
          r n * u n ^ (-α) * echoShape (α / γ) (u n ^ γ / r n) + u n ^ (-α) := by
        field_simp
        ring
      rw [e]
      exact h2
  have := h.add (hd.div_const 2)
  rw [zero_div, add_zero] at this
  refine this.congr fun n => ?_
  simp only [d]
  ring

include hα hZ hind hlaw hpos in
/-- **The cluster ratio along a critical sequence**: if `uₙ^γ / rₙ → κ ≥ 0`, the cluster ratio
tends to `(1 + φ_{α/γ}(κ)) / 2`. -/
theorem tendsto_clusterRatio_powEchoProcess (hγ : 0 < γ) (hγα : γ < α) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0)) {κ : ℝ}
    (hκ : Tendsto (fun n => u n ^ γ / r n) atTop (𝓝 κ)) :
    Tendsto (clusterRatio P (echoProcess (powLag γ) Z) u r) atTop
      (𝓝 ((1 + echoShape (α / γ) κ) / 2)) := by
  have h := tendsto_clusterRatio_sub_powEchoProcess hα hZ hind hlaw hpos hγ hγα hu hr hrb
  have hφ : Tendsto (fun n => (1 + echoShape (α / γ) (u n ^ γ / r n)) / 2) atTop
      (𝓝 ((1 + echoShape (α / γ) κ) / 2)) :=
    ((((continuous_echoShape ((one_lt_div hγ).2 hγα)).tendsto κ).comp hκ).const_add 1).div_const 2
  have := h.add hφ
  rw [zero_add] at this
  exact this.congr fun n => by ring

include hα hZ hind hlaw hpos in
/-- If `uₙ^γ / rₙ → ∞` (blocks shorter than the echo lag), the cluster ratio tends to `1 = ϑ`. -/
theorem tendsto_clusterRatio_powEchoProcess_short (hγ : 0 < γ) (hγα : γ < α) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hκ : Tendsto (fun n => u n ^ γ / r n) atTop atTop) :
    Tendsto (clusterRatio P (echoProcess (powLag γ) Z) u r) atTop (𝓝 1) := by
  have h := (tendsto_clusterRatio_sub_powEchoProcess hα hZ hind hlaw hpos hγ hγα hu hr
    hrb).add_const 1
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [hκ.eventually_ge_atTop 1] with n hn
  rw [echoShape_of_one_le ((one_lt_div hγ).2 hγα) hn]
  ring

include hα hZ hind hlaw hpos in
/-- **Anticlustering fails when the cluster ratio does not tend to `ϑ = 1`.** For the power-lag
echo process, forward anticlustering along `uₙ → ∞`, `rₙ → ∞` would force the escape mass to
vanish and hence the cluster ratio to tend to `ϑ = 1`. -/
theorem not_forwardAntiClusteringAt_powEchoProcess (hγ : 0 < γ) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) {ℓ : ℝ} (hℓ : ℓ ≠ 1)
    (hlim : Tendsto (clusterRatio P (echoProcess (powLag γ) Z) u r) atTop (𝓝 ℓ)) :
    ¬ ForwardAntiClusteringAt P (echoProcess (powLag γ) Z) u r := fun hAC => by
  have h := (hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos (measurable_powLag γ)
    (one_le_powLag γ) (tendsto_powLag hγ)).tendsto_clusterRatio_iff hα
    (measurable_echoProcess hZ (measurable_powLag γ)) measurable_unitSpectral
    (hasShiftInvariantWindows_echoProcess hZ hind hlaw (measurable_powLag γ)) hu hr ℓ
  rw [candidateExtremalIndex_unitSpectral hα] at h
  have := (h.1 hlim).unique (hAC.hasEscapeMass_zero hr)
  simp only [ENNReal.toReal_one] at this
  exact hℓ (by linarith)

include hα hZ hind hlaw hpos in
/-- **Anticlustering holds for blocks shorter than the echo lag**: if eventually
`rₙ ≤ uₙ^γ`, `uₙ → ∞` and `rₙ uₙ^(-α) → 0`, then `AC` holds along `uₙ`, `rₙ`. -/
theorem antiClusteringAt_powEchoProcess (hγ : 0 ≤ γ) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop)
    {r : ℕ → ℕ} (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0))
    (hshort : ∀ᶠ n in atTop, (r n : ℝ) ≤ u n ^ γ) :
    AntiClusteringAt P (echoProcess (powLag γ) Z) u r := by
  refine antiClusteringAt_echoProcess hα hZ hind hlaw hpos (measurable_powLag γ)
    (one_le_powLag γ) hu hrb ?_
  filter_upwards [hshort, hu.eventually_gt_atTop 0] with n hn hu0 z hz
  have := rpow_lt_powLag γ z
  have h2 : u n ^ γ ≤ z ^ γ := Real.rpow_le_rpow hu0.le hz hγ
  exact_mod_cast hn.trans_lt (h2.trans_lt this)

end PowEcho

end ExtremeValueTheory
