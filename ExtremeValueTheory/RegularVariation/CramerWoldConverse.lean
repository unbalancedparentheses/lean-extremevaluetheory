import ExtremeValueTheory.RegularVariation.CramerWold

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

namespace CramerWold

section Converse

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Ω → E}

/-- The normalized law `P(X / x ∈ ·) / V(x)`. -/
noncomputable def scaledLaw (P : Measure Ω) (X : Ω → E) (V : ℝ → ℝ) (x : ℝ) : Measure E :=
  ENNReal.ofReal (V x)⁻¹ • P.map fun ω => x⁻¹ • X ω

instance [IsFiniteMeasure P] (V : ℝ → ℝ) (x : ℝ) : IsFiniteMeasure (scaledLaw P X V x) :=
  ⟨by rw [scaledLaw, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

theorem scaledLaw_apply (hX : Measurable X) (V : ℝ → ℝ) (x : ℝ) {A : Set E}
    (hA : MeasurableSet A) :
    scaledLaw P X V x A = ENNReal.ofReal (V x)⁻¹ * P {ω | x⁻¹ • X ω ∈ A} := by
  have hm : Measurable fun ω => x⁻¹ • X ω := hX.const_smul _
  rw [scaledLaw, Measure.smul_apply, Measure.map_apply hm hA, smul_eq_mul]
  rfl

theorem integral_scaledLaw (hX : Measurable X) {V : ℝ → ℝ} {x : ℝ} (hV : 0 ≤ V x) {g : E → ℝ}
    (hg : Measurable g) :
    ∫ y, g y ∂(scaledLaw P X V x) = (V x)⁻¹ * ∫ ω, g (x⁻¹ • X ω) ∂P := by
  have hm : Measurable fun ω => x⁻¹ • X ω := hX.const_smul _
  rw [scaledLaw, integral_smul_measure, integral_map hm.aemeasurable
    hg.aestronglyMeasurable, smul_eq_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hV)]

theorem scaledLaw_norm_lt (hX : Measurable X) (V : ℝ → ℝ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    scaledLaw P X V x {y | t < ‖y‖} = ENNReal.ofReal (V x)⁻¹ * P {ω | x * t < ‖X ω‖} := by
  rw [scaledLaw_apply hX V x (measurableSet_lt measurable_const continuous_norm.measurable)]
  congr 2
  ext ω
  simp only [mem_ofPred_eq, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hx]
  rw [lt_inv_mul_iff₀ hx]

theorem scaledLaw_linear_lt (hX : Measurable X) (V : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (L : StrongDual ℝ E) (t : ℝ) :
    scaledLaw P X V x {y | t < L y} = ENNReal.ofReal (V x)⁻¹ * P {ω | x * t < L (X ω)} := by
  rw [scaledLaw_apply hX V x (measurableSet_lt measurable_const L.measurable)]
  congr 2
  ext ω
  simp only [mem_ofPred_eq, map_smul, smul_eq_mul]
  rw [lt_inv_mul_iff₀ hx]

omit [MeasurableSpace E] [BorelSpace E] in
/-- In a finite-dimensional space, finitely many linear functionals dominate the norm: if
`t < ‖y‖` with `t ≥ 0`, then `t < lf i y` for some `i`. -/
theorem exists_linear_family_norm [FiniteDimensional ℝ E] :
    ∃ (ι : Type) (_ : Fintype ι) (lf : ι → StrongDual ℝ E),
      ∀ y : E, ∀ t : ℝ, 0 ≤ t → t < ‖y‖ → ∃ i, t < lf i y := by
  set b := Module.finBasis ℝ E
  set B : ℝ := ∑ i, ‖b i‖ + 1
  have hB : 0 < B := by positivity
  let c : Fin (Module.finrank ℝ E) → StrongDual ℝ E := fun i =>
    LinearMap.toContinuousLinearMap (b.coord i)
  have hc : ∀ i y, c i y = b.repr y i := fun i y => by
    simp [c, Module.Basis.coord_apply]
  refine ⟨Fin (Module.finrank ℝ E) × Bool, inferInstance,
    fun p => (if p.2 then B else -B) • c p.1, fun y t ht hty => ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : ∀ i, |b.repr y i| * B ≤ t := fun i => by
    have h1 := hcon (i, true)
    have h2 := hcon (i, false)
    simp only [ite_true, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hc] at h1 h2
    simp only [Bool.false_eq_true, ite_false, neg_mul] at h2
    rcases abs_cases (b.repr y i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  have : ‖y‖ ≤ t := by
    calc ‖y‖ = ‖∑ i, b.repr y i • b i‖ := by rw [b.sum_repr]
      _ ≤ ∑ i, ‖b.repr y i • b i‖ := norm_sum_le _ _
      _ = ∑ i, |b.repr y i| * ‖b i‖ := by simp [norm_smul]
      _ ≤ ∑ i, (t / B) * ‖b i‖ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right ((le_div_iff₀ hB).2 (hle i)) (norm_nonneg _)
      _ = (t / B) * (B - 1) := by rw [← Finset.mul_sum]; simp [B]
      _ ≤ t := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hB]; nlinarith
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Uniform tail bound** from the tails of linear combinations, via the Potter bounds for an
antitone regularly varying normalization `V`. -/
theorem exists_tail_bound [IsProbabilityMeasure P] [FiniteDimensional ℝ E] {α : ℝ} {V : ℝ → ℝ}
    (hα : 0 < α) (hVa : Antitone V) (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L))) :
    ∃ x₁ K : ℝ, 0 < x₁ ∧ 0 < K ∧ (∀ x ≥ x₁, 0 < V x) ∧
      (∀ x ≥ x₁, ∀ y ≥ x₁, V y / V x ≤ 2 * max ((y / x) ^ (-α + α / 2)) ((y / x) ^ (-α - α / 2)))
      ∧ ∀ x ≥ x₁, ∀ t > 0, x₁ ≤ x * t →
        P.real {ω | x * t < ‖X ω‖} ≤ K * max (t ^ (-α + α / 2)) (t ^ (-α - α / 2)) * V x := by
  obtain ⟨ι, _, lf, hlf⟩ := exists_linear_family_norm (E := E)
  obtain ⟨xP, hxP, hVpos, hPot⟩ :=
    hV.potter_bound (a := 0) (Or.inr (hVa.antitoneOn _)) (half_pos hα) one_lt_two
  have hev : ∀ᶠ z in atTop, ∀ i, P.real {ω | z < lf i (X ω)} ≤ (abs (w (lf i)) + 1) * V z := by
    refine eventually_all.2 fun i => ?_
    have hlt : w (lf i) < abs (w (lf i)) + 1 := by linarith [le_abs_self (w (lf i))]
    filter_upwards [(tendsto_order.1 (hw (lf i))).2 _ hlt, hV.eventually_pos] with z hz hVz
    exact ((div_lt_iff₀ hVz).1 hz).le
  obtain ⟨z₀, hz₀⟩ := eventually_atTop.1 hev
  set W : ℝ := ∑ i, (abs (w (lf i)) + 1)
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨max xP z₀, 2 * W + 1, lt_max_of_lt_left hxP, by positivity,
    fun x hx => hVpos x (le_of_max_le_left hx),
    fun x hx y hy => hPot x (le_of_max_le_left hx) y (le_of_max_le_left hy),
    fun x hx t ht hxt => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (lt_max_of_lt_left hxP) hx
  have hxt0 : 0 ≤ x * t := (mul_pos hx0 ht).le
  have hsub : {ω | x * t < ‖X ω‖} ⊆ ⋃ i, {ω | x * t < lf i (X ω)} := fun ω hω => by
    obtain ⟨i, hi⟩ := hlf (X ω) (x * t) hxt0 hω
    exact mem_iUnion.2 ⟨i, hi⟩
  have hVx := hVpos x (le_of_max_le_left hx)
  have hratio := hPot x (le_of_max_le_left hx) (x * t) (le_of_max_le_left hxt)
  rw [mul_div_cancel_left₀ _ hx0.ne', div_le_iff₀ hVx] at hratio
  have hM : 0 ≤ max (t ^ (-α + α / 2)) (t ^ (-α - α / 2)) :=
    le_max_of_le_left (Real.rpow_nonneg ht.le _)
  calc P.real {ω | x * t < ‖X ω‖} ≤ ∑ i, P.real {ω | x * t < lf i (X ω)} :=
        (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)
    _ ≤ ∑ i, (abs (w (lf i)) + 1) * V (x * t) :=
        Finset.sum_le_sum fun i _ => hz₀ (x * t) (le_of_max_le_right hxt) i
    _ = W * V (x * t) := by rw [← Finset.sum_mul]
    _ ≤ W * (2 * max (t ^ (-α + α / 2)) (t ^ (-α - α / 2)) * V x) :=
        mul_le_mul_of_nonneg_left hratio hW
    _ ≤ (2 * W + 1) * max (t ^ (-α + α / 2)) (t ^ (-α - α / 2)) * V x := by
        nlinarith [mul_nonneg hM hVx.le]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Tails of linear combinations at a scaled level: `P(L X > x s) / V(x) → w(L) s^{-α}`. -/
theorem tendsto_linear_mul {α : ℝ} {V : ℝ → ℝ} (hV : IsRegularlyVarying V (-α))
    {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    (L : StrongDual ℝ E) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x => P.real {ω | x * s < L (X ω)} / V x) atTop (𝓝 (w L * s ^ (-α))) := by
  have h1 := (hw L).comp (tendsto_id.atTop_mul_const hs)
  have h2 := hV.tendsto hs
  refine (h1.mul h2).congr' ?_
  filter_upwards [(tendsto_id.atTop_mul_const hs).eventually hV.eventually_pos] with x hx
  simp only [Function.comp_apply, id_eq] at hx ⊢
  rw [mul_comm s x]
  field_simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- The limit function is homogeneous of order `α`: `w (c • L) = c ^ α w (L)`. -/
theorem limit_smul {α : ℝ} {V : ℝ → ℝ} (hV : IsRegularlyVarying V (-α))
    {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    (L : StrongDual ℝ E) {c : ℝ} (hc : 0 < c) : w (c • L) = c ^ α * w L := by
  have h := tendsto_linear_mul hV hw L (inv_pos.2 hc)
  have hset : ∀ x : ℝ, {ω | x * c⁻¹ < L (X ω)} = {ω | x < (c • L) (X ω)} := fun x => by
    ext ω
    simp only [mem_ofPred_eq, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [← div_eq_mul_inv, div_lt_iff₀' hc]
  simp only [hset] at h
  rw [tendsto_nhds_unique (hw (c • L)) h, Real.inv_rpow hc.le, ← Real.rpow_neg hc.le, neg_neg,
    mul_comm]

omit [MeasurableSpace E] [BorelSpace E] in
theorem limit_nonneg {α : ℝ} {V : ℝ → ℝ} (hV : IsRegularlyVarying V (-α))
    {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    (L : StrongDual ℝ E) : 0 ≤ w L :=
  ge_of_tendsto (hw L) (by
    filter_upwards [hV.eventually_pos] with x hx using div_nonneg measureReal_nonneg hx.le)

/-- The weight `min (1, ‖y‖) ^ (2 α)`. -/
noncomputable def weight (α : ℝ) (y : E) : ℝ := min 1 ‖y‖ ^ (2 * α)

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_weight {α : ℝ} (hα : 0 < α) : Continuous (weight (E := E) α) :=
  (continuous_const.min continuous_norm).rpow_const fun _ => Or.inr (by positivity)

omit [MeasurableSpace E] [BorelSpace E] in
theorem weight_nonneg (α : ℝ) (y : E) : 0 ≤ weight α y :=
  Real.rpow_nonneg (le_min zero_le_one (norm_nonneg y)) _

omit [MeasurableSpace E] [BorelSpace E] in
theorem weight_le_one {α : ℝ} (hα : 0 < α) (y : E) : weight α y ≤ 1 :=
  Real.rpow_le_one (le_min zero_le_one (norm_nonneg y)) (min_le_left _ _) (by positivity)

/-- The weighted normalized law `min (1, ‖y‖) ^ (2 α) P(X / x ∈ dy) / V(x)`. -/
noncomputable def weightedLaw (P : Measure Ω) (X : Ω → E) (α : ℝ) (V : ℝ → ℝ) (x : ℝ) :
    Measure E :=
  (scaledLaw P X V x).withDensity fun y => ENNReal.ofReal (weight α y)

omit [MeasurableSpace E] [BorelSpace E] in
theorem setOf_lt_weight_subset {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : 0 < t) :
    {y : E | t < weight α y} ⊆ {y | t ^ (2 * α)⁻¹ < ‖y‖} := fun y hy => by
  by_contra hle
  simp only [mem_ofPred_eq, not_lt] at hy hle
  have h1 : weight α y ≤ (t ^ (2 * α)⁻¹) ^ (2 * α) :=
    Real.rpow_le_rpow (le_min zero_le_one (norm_nonneg y)) ((min_le_right _ _).trans hle)
      (by positivity)
  rw [Real.rpow_inv_rpow ht.le (by positivity)] at h1
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
theorem setOf_lt_weight_eq_empty {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : 1 ≤ t) :
    {y : E | t < weight α y} = ∅ := by
  ext y
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
  exact (weight_le_one hα y).trans ht

theorem max_rpow_eq_of_le_one {α s : ℝ} (hα : 0 < α) (hs : 0 < s) (hs1 : s ≤ 1) :
    max (s ^ (-α + α / 2)) (s ^ (-α - α / 2)) = s ^ (-α - α / 2) :=
  max_eq_right (Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith))

theorem max_rpow_eq_of_one_le {α s : ℝ} (hα : 0 < α) (hs : 1 ≤ s) :
    max (s ^ (-α + α / 2)) (s ^ (-α - α / 2)) = s ^ (-α + α / 2) :=
  max_eq_left (Real.rpow_le_rpow_of_exponent_le hs (by linarith))

/-- **Bounded mass of the weighted laws** (a Karamata-type estimate, from the Potter bounds). -/
theorem exists_weightedLaw_univ_le [IsProbabilityMeasure P] [FiniteDimensional ℝ E]
    (hX : Measurable X) {α : ℝ} {V : ℝ → ℝ}
    (hα : 0 < α) (hVa : Antitone V) (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L))) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ x₂ > 0, ∀ x ≥ x₂, weightedLaw P X α V x univ ≤ C := by
  obtain ⟨x₁, K, hx₁, hK, hVpos, hPot, hT⟩ := exists_tail_bound (X := X) hα hVa hV hw
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (K * t ^ (-(3 / 4 : ℝ)))
  have hFm : Measurable F :=
    (measurable_const.mul (measurable_id.pow_const _)).ennreal_ofReal
  have hFint : IntegrableOn (fun t : ℝ => K * t ^ (-(3 / 4 : ℝ))) (Ioc 0 1) :=
    ((integrableOn_Ioc_iff_integrableOn_Ioo).2
      ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by norm_num))).const_mul K
  refine ⟨(∫⁻ t in Ioc 0 1, F t) + ENNReal.ofReal (2 / V x₁),
    ENNReal.add_ne_top.2 ⟨hFint.lintegral_lt_top.ne, ENNReal.ofReal_ne_top⟩, x₁, hx₁,
    fun x hx => ?_⟩
  have hx0 : 0 < x := hx₁.trans_le hx
  have hVx := hVpos x hx
  set c : ℝ := (x₁ / x) ^ (2 * α)
  set G : ℝ → ℝ≥0∞ := fun t =>
    (Ioc 0 1).indicator F t + (Ioc 0 c).indicator (fun _ => ENNReal.ofReal (V x)⁻¹) t
  have hwm : Measurable (weight (E := E) α) := (continuous_weight hα).measurable
  have hbound : ∀ t ∈ Ioi (0 : ℝ),
      scaledLaw P X V x {y | t < weight α y} ≤ G t := fun t ht => by
    have ht0 : 0 < t := ht
    rcases le_or_gt 1 t with ht1 | ht1
    · rw [setOf_lt_weight_eq_empty hα ht1, measure_empty]; exact bot_le
    set s : ℝ := t ^ (2 * α)⁻¹
    have hs0 : 0 < s := Real.rpow_pos_of_pos ht0 _
    have hs1 : s < 1 := Real.rpow_lt_one ht0.le ht1 (by positivity)
    refine (measure_mono (setOf_lt_weight_subset hα ht0)).trans ?_
    rw [scaledLaw_norm_lt hX V hx0]
    rcases le_or_gt x₁ (x * s) with hxs | hxs
    · have h1 := hT x hx s hs0 hxs
      rw [max_rpow_eq_of_le_one hα hs0 hs1.le] at h1
      have hG : F t ≤ G t := by
        simp only [G, indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, ht1.le⟩)]
        exact le_self_add
      refine le_trans ?_ hG
      rw [← ofReal_measureReal (measure_ne_top _ _), ← ENNReal.ofReal_mul (inv_nonneg.2 hVx.le)]
      refine ENNReal.ofReal_le_ofReal ?_
      have he : s ^ (-α - α / 2) = t ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_mul ht0.le]
        congr 1
        field_simp
        ring
      rw [he] at h1
      calc (V x)⁻¹ * P.real {ω | x * s < ‖X ω‖} ≤ (V x)⁻¹ * (K * t ^ (-(3 / 4 : ℝ)) * V x) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hVx.le)
        _ = K * t ^ (-(3 / 4 : ℝ)) := by field_simp
    · have htc : t ∈ Ioc 0 c := by
        refine ⟨ht0, ?_⟩
        have : s < x₁ / x := by rwa [lt_div_iff₀ hx0, mul_comm]
        have h2 := Real.rpow_lt_rpow hs0.le this (show 0 < 2 * α by positivity)
        rw [Real.rpow_inv_rpow ht0.le (by positivity)] at h2
        exact h2.le
      have hG : ENNReal.ofReal (V x)⁻¹ ≤ G t := by
        simp only [G, indicator_of_mem htc]
        exact le_add_self
      refine le_trans ?_ hG
      calc ENNReal.ofReal (V x)⁻¹ * P {ω | x * s < ‖X ω‖} ≤ ENNReal.ofReal (V x)⁻¹ * 1 :=
            mul_le_mul_right prob_le_one _
        _ = _ := mul_one _
  have hc_le : (V x)⁻¹ * c ≤ 2 / V x₁ := by
    have hq0 : 0 < x₁ / x := div_pos hx₁ hx0
    have hq1 : x₁ / x ≤ 1 := (div_le_one hx0).2 hx
    have hP := hPot x hx x₁ le_rfl
    rw [max_rpow_eq_of_le_one hα hq0 hq1, div_le_iff₀ hVx] at hP
    have hV1 := hVpos x₁ le_rfl
    have hqa : c * (x₁ / x) ^ (-α - α / 2) ≤ 1 := by
      rw [← Real.rpow_add hq0]
      exact Real.rpow_le_one hq0.le hq1 (by linarith)
    rw [inv_mul_eq_div, div_le_div_iff₀ hVx hV1]
    have hcq : 0 ≤ c := Real.rpow_nonneg hq0.le _
    calc c * V x₁ ≤ c * (2 * (x₁ / x) ^ (-α - α / 2) * V x) :=
          mul_le_mul_of_nonneg_left hP hcq
      _ = 2 * (c * (x₁ / x) ^ (-α - α / 2)) * V x := by ring
      _ ≤ 2 * 1 * V x := by gcongr
      _ = 2 * V x := by ring
  rw [weightedLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall fun y => weight_nonneg α y)
      hwm.aemeasurable]
  calc ∫⁻ t in Ioi 0, scaledLaw P X V x {y | t < weight α y}
      ≤ ∫⁻ t in Ioi 0, G t := setLIntegral_mono' measurableSet_Ioi hbound
    _ ≤ ∫⁻ t, G t := setLIntegral_le_lintegral _ _
    _ = (∫⁻ t in Ioc 0 1, F t) + ENNReal.ofReal (V x)⁻¹ * volume (Ioc 0 c) := by
        rw [lintegral_add_left (hFm.indicator measurableSet_Ioc),
          lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioc,
          setLIntegral_const]
    _ ≤ (∫⁻ t in Ioc 0 1, F t) + ENNReal.ofReal (2 / V x₁) := by
        gcongr
        rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (inv_nonneg.2 hVx.le)]
        exact ENNReal.ofReal_le_ofReal hc_le

theorem weightedLaw_le [IsFiniteMeasure P] {α : ℝ} (hα : 0 < α) (V : ℝ → ℝ) (x : ℝ) (A : Set E) :
    weightedLaw P X α V x A ≤ scaledLaw P X V x A := by
  rw [weightedLaw, withDensity_apply' _ A]
  calc ∫⁻ y in A, ENNReal.ofReal (weight α y) ∂scaledLaw P X V x
      ≤ ∫⁻ _ in A, 1 ∂scaledLaw P X V x :=
        lintegral_mono fun y => by simpa using weight_le_one hα y
    _ = scaledLaw P X V x A := by rw [setLIntegral_const, one_mul]

theorem isFiniteMeasure_weightedLaw [IsFiniteMeasure P] {α : ℝ} (hα : 0 < α) (V : ℝ → ℝ)
    (x : ℝ) : IsFiniteMeasure (weightedLaw P X α V x) :=
  ⟨(weightedLaw_le hα V x univ).trans_lt (measure_lt_top _ _)⟩

theorem weightedLaw_one_lt_norm (α : ℝ) (V : ℝ → ℝ) (x : ℝ) :
    weightedLaw P X α V x {y | 1 < ‖y‖} = scaledLaw P X V x {y | 1 < ‖y‖} := by
  have hm : MeasurableSet {y : E | 1 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  rw [weightedLaw, withDensity_apply _ hm]
  rw [setLIntegral_congr_fun hm (g := fun _ => 1) fun y (hy : 1 < ‖y‖) => by
    simp [weight, min_eq_left hy.le]]
  simp

/-- **Lower bound for the weighted masses**, from a non-degenerate linear combination. -/
theorem exists_le_weightedLaw_univ [IsProbabilityMeasure P] (hX : Measurable X) {α : ℝ}
    {V : ℝ → ℝ} (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    {L₀ : StrongDual ℝ E} (hL₀ : w L₀ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in atTop, ENNReal.ofReal c ≤ weightedLaw P X α V x univ := by
  set a : ℝ := (‖L₀‖ + 1)⁻¹
  have ha : 0 < a := by positivity
  set L : StrongDual ℝ E := a • L₀
  have hwL : 0 < w L := by
    rw [limit_smul hV hw L₀ ha]
    exact mul_pos (Real.rpow_pos_of_pos ha _)
      (lt_of_le_of_ne (limit_nonneg hV hw L₀) (Ne.symm hL₀))
  have hLn : ‖L‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, inv_mul_le_iff₀ (by positivity)]
    linarith
  have hsub : {y : E | 1 < L y} ⊆ {y | 1 < ‖y‖} := fun y (hy : 1 < L y) => by
    show 1 < ‖y‖
    calc 1 < L y := hy
      _ ≤ ‖L‖ * ‖y‖ := (le_abs_self _).trans (by simpa using L.le_opNorm y)
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
      _ = ‖y‖ := one_mul _
  refine ⟨w L / 2, half_pos hwL, ?_⟩
  filter_upwards [(tendsto_order.1 (hw L)).1 _ (half_lt_self hwL), hV.eventually_pos,
    eventually_gt_atTop 0] with x hx hVx hx0
  calc ENNReal.ofReal (w L / 2) ≤ ENNReal.ofReal (P.real {ω | x < L (X ω)} / V x) :=
        ENNReal.ofReal_le_ofReal hx.le
    _ = scaledLaw P X V x {y | 1 < L y} := by
        rw [scaledLaw_linear_lt hX V hx0, mul_one, div_eq_inv_mul,
          ENNReal.ofReal_mul (inv_nonneg.2 hVx.le), ofReal_measureReal (measure_ne_top _ _)]
    _ ≤ scaledLaw P X V x {y | 1 < ‖y‖} := measure_mono hsub
    _ = weightedLaw P X α V x {y | 1 < ‖y‖} := (weightedLaw_one_lt_norm α V x).symm
    _ ≤ weightedLaw P X α V x univ := measure_mono (subset_univ _)

end Converse

end CramerWold

end ExtremeValueTheory
