import ExtremeValueTheory.RegularVariation.CramerWold
import Mathlib.MeasureTheory.Measure.Prokhorov

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

omit [MeasurableSpace E] [BorelSpace E] in
/-- A bounded continuous function vanishing near the origin, divided by the weight, is again
bounded continuous. -/
theorem exists_bcf_div_weight {α : ℝ} (hα : 0 < α) (f : E →ᵇ ℝ) (hf : VanishesNearZero f) :
    ∃ h : E →ᵇ ℝ, (∀ y, weight α y * h y = f y) ∧ (∀ y, y ≠ 0 → (weight α y)⁻¹ * f y = h y) ∧
      h 0 = 0 := by
  obtain ⟨r, hr, hfr⟩ := hf
  have hq : ∀ y : E, min 1 r ≤ min 1 (max r ‖y‖) := fun y =>
    min_le_min le_rfl (le_max_left _ _)
  have hq0 : 0 < min 1 r := lt_min one_pos hr
  let g : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => min 1 (max r ‖y‖) ^ (-(2 * α)))
    ((continuous_const.min (continuous_const.max continuous_norm)).rpow_const
      fun y => Or.inl (hq0.trans_le (hq y)).ne')
    (min 1 r ^ (-(2 * α))) fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hq0.le.trans (hq y)) _)]
      exact Real.rpow_le_rpow_of_nonpos hq0 (hq y) (by linarith)
  have key : ∀ y : E, r ≤ ‖y‖ → weight α y * g y = 1 := fun y hy => by
    have hmax : max r ‖y‖ = ‖y‖ := max_eq_right hy
    have hpos : 0 < min 1 ‖y‖ := lt_min one_pos (hr.trans_le hy)
    show min 1 ‖y‖ ^ (2 * α) * min 1 (max r ‖y‖) ^ (-(2 * α)) = 1
    rw [hmax, Real.rpow_neg hpos.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos _).ne']
  refine ⟨f * g, fun y => ?_, fun y _ => ?_, ?_⟩
  · rcases le_or_gt r ‖y‖ with hy | hy
    · rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, mul_left_comm, key y hy, mul_one]
    · rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, hfr y hy, zero_mul, mul_zero]
  · rcases le_or_gt r ‖y‖ with hy | hy
    · have h1 := key y hy
      rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, mul_comm]
      congr 1
      exact (eq_inv_of_mul_eq_one_right h1).symm
    · rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, hfr y hy, mul_zero, zero_mul]
  · rw [BoundedContinuousFunction.coe_mul, Pi.mul_apply, hfr 0 (by simpa using hr), zero_mul]

theorem integral_weightedLaw {α : ℝ} (V : ℝ → ℝ) (x : ℝ) (h : E → ℝ) :
    ∫ y, h y ∂weightedLaw P X α V x = ∫ y, weight α y * h y ∂scaledLaw P X V x := by
  have hm : Measurable fun y : E => (weight α y).toNNReal := by
    refine Measurable.real_toNNReal ?_
    exact (measurable_const.min measurable_norm).pow_const _
  rw [show weightedLaw P X α V x = (scaledLaw P X V x).withDensity
    (fun y => ((weight α y).toNNReal : ℝ≥0∞)) from rfl, integral_withDensity_eq_integral_smul hm]
  congr 1
  funext y
  rw [NNReal.smul_def, Real.coe_toNNReal _ (weight_nonneg α y), smul_eq_mul]

/-- The tail bound in terms of the normalized law. -/
theorem scaledLaw_norm_lt_le (hX : Measurable X) {V : ℝ → ℝ} {x₁ K α : ℝ}
    (hVpos : ∀ x ≥ x₁, 0 < V x)
    (hT : ∀ x ≥ x₁, ∀ t > 0, x₁ ≤ x * t →
        P.real {ω | x * t < ‖X ω‖} ≤ K * max (t ^ (-α + α / 2)) (t ^ (-α - α / 2)) * V x)
    [IsFiniteMeasure P] {x t : ℝ} (hx : x₁ ≤ x) (hx0 : 0 < x) (ht : 0 < t) (hxt : x₁ ≤ x * t) :
    scaledLaw P X V x {y | t < ‖y‖} ≤
      ENNReal.ofReal (K * max (t ^ (-α + α / 2)) (t ^ (-α - α / 2))) := by
  have hVx := hVpos x hx
  rw [scaledLaw_norm_lt hX V hx0, ← ofReal_measureReal (measure_ne_top _ _),
    ← ENNReal.ofReal_mul (inv_nonneg.2 hVx.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (V x)⁻¹ * P.real {ω | x * t < ‖X ω‖}
      ≤ (V x)⁻¹ * (K * max (t ^ (-α + α / 2)) (t ^ (-α - α / 2)) * V x) :=
        mul_le_mul_of_nonneg_left (hT x hx t ht hxt) (inv_nonneg.2 hVx.le)
    _ = K * max (t ^ (-α + α / 2)) (t ^ (-α - α / 2)) := by field_simp

/-- **Existence of limit points** (compactness): along every sequence `u n → ∞` there is a
subsequence along which the normalized laws `P(X / x ∈ ·) / V(x)` converge on sets bounded away
from the origin to a measure `μ` with no atom at the origin and finite away from it. The proof
applies Prokhorov's theorem to the normalized weighted laws
`min (1, ‖y‖) ^ (2 α) P(X / x ∈ dy) / V(x)`. -/
theorem exists_subseq_tendsto [IsProbabilityMeasure P] [FiniteDimensional ℝ E]
    (hX : Measurable X) {α : ℝ} {V : ℝ → ℝ}
    (hα : 0 < α) (hVa : Antitone V) (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    {L₀ : StrongDual ℝ E} (hL₀ : w L₀ ≠ 0) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) :
    ∃ (φ : ℕ → ℕ) (μ : Measure E), StrictMono φ ∧ μ {0} = 0 ∧
      (∀ r > 0, μ {y | r < ‖y‖} < ∞) ∧
      ∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u (φ n))) atTop (𝓝 (∫ y, f y ∂μ)) := by
  obtain ⟨C, hC, x₂, hx₂, hmass⟩ := exists_weightedLaw_univ_le hX hα hVa hV hw
  obtain ⟨c, hc, hlow⟩ := exists_le_weightedLaw_univ (α := α) hX hV hw hL₀
  obtain ⟨x₁, K, hx₁, hK, hVpos, -, hT⟩ := exists_tail_bound (X := X) hα hVa hV hw
  obtain ⟨x₃, hx₃⟩ := eventually_atTop.1 hlow
  set x₀ := max (max x₁ x₂) x₃
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually_ge_atTop x₀)
  set v : ℕ → ℝ := fun n => u (n + N)
  have hv : ∀ n, x₀ ≤ v n := fun n => hN _ (Nat.le_add_left N n)
  have hv1 : ∀ n, x₁ ≤ v n := fun n => (le_max_left _ _).trans ((le_max_left _ _).trans (hv n))
  have hv2 : ∀ n, x₂ ≤ v n := fun n => (le_max_right _ _).trans ((le_max_left _ _).trans (hv n))
  have hv3 : ∀ n, x₃ ≤ v n := fun n => (le_max_right _ _).trans (hv n)
  have hv0 : ∀ n, 0 < v n := fun n => hx₁.trans_le (hv1 n)
  have hfin := fun n => isFiniteMeasure_weightedLaw (P := P) (X := X) hα V (v n)
  let π : ℕ → FiniteMeasure E := fun n => ⟨weightedLaw P X α V (v n), hfin n⟩
  have hπ : ∀ n, ((π n : FiniteMeasure E) : Measure E) = weightedLaw P X α V (v n) :=
    fun n => rfl
  set Cn : ℝ≥0 := C.toNNReal
  set cn : ℝ≥0 := c.toNNReal
  have hcn : 0 < cn := Real.toNNReal_pos.2 hc
  have hmass_le : ∀ n, (π n).mass ≤ Cn := fun n => by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, hπ, ENNReal.coe_toNNReal hC]
    exact hmass _ (hv2 n)
  have hmass_ge : ∀ n, cn ≤ (π n).mass := fun n => by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, hπ]
    exact hx₃ _ (hv3 n)
  have hne : ∀ n, π n ≠ 0 := fun n =>
    (FiniteMeasure.mass_nonzero_iff _).1 (hcn.trans_le (hmass_ge n)).ne'
  let Q : ℕ → ProbabilityMeasure E := fun n => (π n).normalize
  -- tightness of the normalized weighted laws
  have hQle : ∀ n (R : ℝ), 1 ≤ R → ((Q n : ProbabilityMeasure E) : Measure E) {y | R < ‖y‖} ≤
      (cn : ℝ≥0∞)⁻¹ * ENNReal.ofReal (K * R ^ (-α + α / 2)) := fun n R hR => by
    rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (hne n), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul,
      ENNReal.coe_inv (FiniteMeasure.mass_nonzero_iff _ |>.2 (hne n)), hπ]
    gcongr
    · exact hmass_ge n
    · refine (weightedLaw_le hα V _ _).trans ?_
      have h := scaledLaw_norm_lt_le hX hVpos hT (hv1 n) (hv0 n) (one_pos.trans_le hR)
        ((hv1 n).trans (le_mul_of_one_le_right (hv0 n).le hR))
      rwa [max_rpow_eq_of_one_le hα hR] at h
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ range Q} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    have hlim : Tendsto (fun R : ℝ => (cn : ℝ≥0∞)⁻¹ * ENNReal.ofReal (K * R ^ (-α + α / 2)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => K * R ^ (-α + α / 2)) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (show 0 < α - α / 2 by linarith)).const_mul K
          |>.congr' (by
            filter_upwards [eventually_gt_atTop 0] with R hR
            congr 1; ring_nf)
      have h2 := ENNReal.Tendsto.const_mul (a := (cn : ℝ≥0∞)⁻¹) (ENNReal.tendsto_ofReal h1)
        (Or.inr (ENNReal.inv_ne_top.2 (by exact_mod_cast hcn.ne')))
      simpa [ENNReal.ofReal_zero] using h2
    obtain ⟨R, hR⟩ := eventually_atTop.1 ((hlim.eventually (gt_mem_nhds hε)).and
      (eventually_ge_atTop 1))
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
    rintro _ ⟨μ, ⟨n, rfl⟩, rfl⟩
    have hcompl : (Metric.closedBall (0 : E) R)ᶜ = {y | R < ‖y‖} := by
      ext y; simp
    rw [hcompl]
    exact (hQle n R (hR R le_rfl).2).trans (hR R le_rfl).1.le
  have hcomp : IsCompact (Icc cn Cn ×ˢ closure (range Q)) :=
    isCompact_Icc.prod (isCompact_closure_of_isTightMeasureSet htight)
  have hmem : ∀ n, ((π n).mass, Q n) ∈ Icc cn Cn ×ˢ closure (range Q) := fun n =>
    ⟨⟨hmass_ge n, hmass_le n⟩, subset_closure ⟨n, rfl⟩⟩
  obtain ⟨⟨m, Qlim⟩, hmQ, ψ, hψ, hlim⟩ := hcomp.tendsto_subseq hmem
  have hm_lim : Tendsto (fun n => (π (ψ n)).mass) atTop (𝓝 m) :=
    ((continuous_fst.tendsto _).comp hlim)
  have hQ_lim : Tendsto (fun n => Q (ψ n)) atTop (𝓝 Qlim) :=
    ((continuous_snd.tendsto _).comp hlim)
  set ρ : Measure E := m • (Qlim : Measure E)
  set μ : Measure E :=
    (ρ.restrict {0}ᶜ).withDensity fun y => ENNReal.ofReal (weight α y)⁻¹
  refine ⟨fun n => ψ n + N, μ, hψ.add_const N, ?_, ?_, ?_⟩
  · rw [withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_restrict
      (measurableSet_singleton 0), inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]
  · intro r hr
    have hm : MeasurableSet {y : E | r < ‖y‖} :=
      measurableSet_lt measurable_const continuous_norm.measurable
    rw [withDensity_apply _ hm]
    have hb : ∀ y ∈ {y : E | r < ‖y‖},
        ENNReal.ofReal (weight α y)⁻¹ ≤ ENNReal.ofReal ((min 1 r ^ (2 * α))⁻¹) := fun y hy => by
      refine ENNReal.ofReal_le_ofReal (inv_anti₀ (Real.rpow_pos_of_pos (lt_min one_pos hr) _) ?_)
      exact Real.rpow_le_rpow (lt_min one_pos hr).le (min_le_min le_rfl (le_of_lt hy))
        (by positivity)
    calc ∫⁻ y in {y | r < ‖y‖}, ENNReal.ofReal (weight α y)⁻¹ ∂ρ.restrict {0}ᶜ
        ≤ ∫⁻ _ in {y | r < ‖y‖}, ENNReal.ofReal ((min 1 r ^ (2 * α))⁻¹) ∂ρ.restrict {0}ᶜ :=
          setLIntegral_mono measurable_const hb
      _ < ∞ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  · intro f hf
    obtain ⟨h, hwh, hhw, h0⟩ := exists_bcf_div_weight hα f hf
    have hseq : ∀ n, ∫ y, f y ∂scaledLaw P X V (u (ψ n + N)) =
        (π (ψ n)).mass * ∫ y, h y ∂(Q (ψ n) : Measure E) := fun n => by
      have e1 : ∫ y, f y ∂scaledLaw P X V (u (ψ n + N)) =
          ∫ y, h y ∂(π (ψ n) : Measure E) := by
        rw [hπ, integral_weightedLaw]
        simp_rw [hwh]
        rfl
      rw [e1]
      conv_lhs => rw [FiniteMeasure.self_eq_mass_smul_normalize (π (ψ n))]
      rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure, NNReal.smul_def,
        smul_eq_mul]
      rfl
    have hlimit : ∫ y, f y ∂μ = m * ∫ y, h y ∂(Qlim : Measure E) := by
      have hmeas : Measurable fun y : E => ((weight α y)⁻¹).toNNReal :=
        ((continuous_weight hα).measurable.inv).real_toNNReal
      rw [show μ = (ρ.restrict {0}ᶜ).withDensity
          (fun y => (((weight α y)⁻¹).toNNReal : ℝ≥0∞)) from rfl,
        integral_withDensity_eq_integral_smul hmeas]
      have e2 : ∫ y in {0}ᶜ, ((weight α y)⁻¹).toNNReal • f y ∂ρ = ∫ y in {0}ᶜ, h y ∂ρ := by
        refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun y hy => ?_
        rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 (weight_nonneg α y)), smul_eq_mul,
          hhw y hy]
      rw [e2, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        simp only [mem_compl_iff, mem_singleton_iff, not_not] at hy
        rw [hy, h0]]
      rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    rw [hlimit]
    refine (((NNReal.continuous_coe.tendsto _).comp hm_lim).mul ?_).congr fun n => (hseq n).symm
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hQ_lim) h

theorem scaledLaw_real_norm_lt (hX : Measurable X) [IsFiniteMeasure P] {V : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hV : 0 ≤ V x) (t : ℝ) :
    (scaledLaw P X V x).real {y | t < ‖y‖} = (V x)⁻¹ * P.real {ω | x * t < ‖X ω‖} := by
  rw [measureReal_def, scaledLaw_norm_lt hX V hx, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 hV)]
  rfl

theorem scaledLaw_real_linear_lt (hX : Measurable X) [IsFiniteMeasure P] {V : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hV : 0 ≤ V x) (L : StrongDual ℝ E) (t : ℝ) :
    (scaledLaw P X V x).real {y | t < L y} = (V x)⁻¹ * P.real {ω | x * t < L (X ω)} := by
  rw [measureReal_def, scaledLaw_linear_lt hX V hx, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 hV)]
  rfl

theorem vanishesNearZero_normCutoffBCF {t : ℝ} (ht : 0 < t) :
    VanishesNearZero (⇑(normCutoffBCF t : E →ᵇ ℝ)) :=
  ⟨t / 2, half_pos ht, fun y hy => by
    simp [normCutoff_eq_zero ht hy.le]⟩

theorem integral_normCutoffBCF_le (ν : Measure E) [IsFiniteMeasure ν] {t : ℝ} (ht : 0 < t) :
    ∫ y, normCutoffBCF t y ∂ν ≤ ν.real {y | t / 2 < ‖y‖} := by
  have hm : MeasurableSet {y : E | t / 2 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_indicator_one hm]
  refine integral_mono ((normCutoffBCF t).integrable ν) ((integrable_const 1).indicator hm)
    fun y => ?_
  by_cases hy : t / 2 < ‖y‖
  · rw [indicator_of_mem (show y ∈ {y : E | t / 2 < ‖y‖} from hy), Pi.one_apply,
      normCutoffBCF_apply]
    exact_mod_cast normCutoff_le_one t y
  · rw [indicator_of_notMem (show y ∉ {y : E | t / 2 < ‖y‖} from hy), normCutoffBCF_apply,
      normCutoff_eq_zero ht (not_lt.1 hy)]
    simp

/-- `μ {‖y‖ > t} ≤ ∫ normCutoff_t dμ` for a measure finite away from the origin. -/
theorem measure_lt_norm_le_integral_normCutoff {μ : Measure E}
    (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞) {t : ℝ} (ht : 0 < t) :
    μ {y | t < ‖y‖} ≤ ENNReal.ofReal (∫ y, normCutoffBCF t y ∂μ) := by
  have hm : MeasurableSet {y : E | t / 2 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hint : Integrable (fun y => normCutoffBCF t y) μ := by
    have hsupp : Function.support (fun y => normCutoffBCF t y) ⊆ {y : E | t / 2 < ‖y‖} :=
      fun y hy => by
        by_contra h'
        exact hy (by simp [normCutoff_eq_zero ht (not_lt.1 h')])
    exact (integrableOn_iff_integrable_of_support_subset hsupp).1
      (Measure.integrableOn_of_bounded (hμ _ (half_pos ht)).ne
        (normCutoffBCF t).continuous.aestronglyMeasurable (M := ‖normCutoffBCF t‖)
        (ae_of_all _ fun y => (normCutoffBCF t).norm_coe_le_norm y))
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => by
    simp only [normCutoffBCF_apply, Pi.zero_apply]; exact NNReal.coe_nonneg _)]
  rw [← lintegral_indicator_one (measurableSet_lt measurable_const continuous_norm.measurable)]
  refine lintegral_mono fun y => ?_
  by_cases hy : t < ‖y‖
  · rw [indicator_of_mem (show y ∈ {y : E | t < ‖y‖} from hy), Pi.one_apply,
      normCutoffBCF_apply, normCutoff_eq_one ht hy.le]
    simp
  · rw [indicator_of_notMem (show y ∉ {y : E | t < ‖y‖} from hy)]
    exact bot_le

/-- **Tail bound for limit points**: a limit point `μ` of the normalized laws satisfies
`μ {‖y‖ > t} ≤ W t ^ (-α)` for a finite constant `W` independent of the sequence. -/
theorem exists_limit_tail_le [IsProbabilityMeasure P] [FiniteDimensional ℝ E]
    (hX : Measurable X) {α : ℝ} {V : ℝ → ℝ} (hV : IsRegularlyVarying V (-α))
    {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L))) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ {u : ℕ → ℝ}, Tendsto u atTop atTop → ∀ {μ : Measure E},
      (∀ r > 0, μ {y | r < ‖y‖} < ∞) →
      (∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u n)) atTop (𝓝 (∫ y, f y ∂μ))) →
      ∀ t > 0, μ {y | t < ‖y‖} ≤ ENNReal.ofReal (t ^ (-α)) * W := by
  obtain ⟨ι, _, lf, hlf⟩ := exists_linear_family_norm (E := E)
  set S : ℝ := ∑ i, w (lf i)
  refine ⟨ENNReal.ofReal ((2 : ℝ) ^ α * S), ENNReal.ofReal_ne_top,
    fun {u} hu {μ} hμ hconv t ht => ?_⟩
  have ht2 : 0 < t / 2 := half_pos ht
  have hlim := hconv _ (vanishesNearZero_normCutoffBCF ht)
  have hR : Tendsto (fun n => ∑ i, P.real {ω | u n * (t / 2) < lf i (X ω)} / V (u n)) atTop
      (𝓝 (∑ i, w (lf i) * (t / 2) ^ (-α))) :=
    tendsto_finsetSum _ fun i _ => (tendsto_linear_mul hV hw (lf i) ht2).comp hu
  have hle : ∀ᶠ n in atTop, ∫ y, normCutoffBCF t y ∂scaledLaw P X V (u n) ≤
      ∑ i, P.real {ω | u n * (t / 2) < lf i (X ω)} / V (u n) := by
    filter_upwards [hu.eventually hV.eventually_pos, hu.eventually_gt_atTop 0] with n hVn hun
    refine (integral_normCutoffBCF_le _ ht).trans ?_
    rw [scaledLaw_real_norm_lt hX hun hVn.le, ← Finset.sum_div, inv_mul_eq_div]
    gcongr
    have hsub : {ω | u n * (t / 2) < ‖X ω‖} ⊆ ⋃ i, {ω | u n * (t / 2) < lf i (X ω)} :=
      fun ω hω => by
        obtain ⟨i, hi⟩ := hlf (X ω) _ (mul_pos hun ht2).le hω
        exact mem_iUnion.2 ⟨i, hi⟩
    exact (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)
  have hint_le := le_of_tendsto_of_tendsto hlim hR hle
  refine (measure_lt_norm_le_integral_normCutoff hμ ht).trans ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  refine ENNReal.ofReal_le_ofReal (hint_le.trans_eq ?_)
  rw [← Finset.sum_mul, Real.div_rpow ht.le zero_le_two, Real.rpow_neg zero_le_two,
    Real.rpow_neg ht.le]
  simp only [S]
  field_simp

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_halfSpace_subset_norm (L : StrongDual ℝ E) {t : ℝ} (ht : 0 < t) :
    ∃ r > 0, {y : E | t < L y} ⊆ {y | r < ‖y‖} :=
  ⟨(‖t⁻¹ • L‖ + 1)⁻¹, by positivity, by
    rw [setOf_lt_apply_eq ht L]; exact setOf_one_lt_apply_subset _⟩

/-- **Half-spaces for limit points**: a limit point `μ` of the normalized laws satisfies
`μ {L > s} = w (L) s ^ (-α)` for every continuous linear functional `L` and every `s > 0`. -/
theorem limit_halfSpace [IsProbabilityMeasure P] (hX : Measurable X) {α : ℝ} {V : ℝ → ℝ}
    (hα : 0 < α) (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {μ : Measure E}
    (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞)
    (hconv : ∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u n)) atTop (𝓝 (∫ y, f y ∂μ)))
    (L : StrongDual ℝ E) {s : ℝ} (hs : 0 < s) :
    μ {y | s < L y} = ENNReal.ofReal (w L * s ^ (-α)) := by
  have hfinL : ∀ t > 0, μ {y | t < L y} ≠ ∞ := fun t ht => by
    obtain ⟨r, hr, hsub⟩ := exists_halfSpace_subset_norm L ht
    exact ((measure_mono hsub).trans_lt (hμ r hr)).ne
  -- good levels
  have hgood : ∀ t > 0, μ {y | L y = t} = 0 → μ {y | t < L y} = ENNReal.ofReal (w L * t ^ (-α)) :=
    fun t ht hnull => by
      obtain ⟨r, hr, hsub⟩ := exists_halfSpace_subset_norm L ht
      have hAm : MeasurableSet {y : E | t < L y} := measurableSet_lt measurable_const L.measurable
      have hfr : μ (frontier {y : E | t < L y}) = 0 :=
        measure_mono_null ((frontier_lt_subset_eq continuous_const L.continuous).trans
          fun y (hy : t = L y) => (show L y = t from hy.symm)) hnull
      have key := tendsto_measureReal_of_vanishesNearZero (μs := fun n => scaledLaw P X V (u n))
        (fun n => inferInstance) hμ hconv hAm hr (fun y hy => (show r < ‖y‖ from hsub hy).le) hfr
      have hlim : Tendsto (fun n => (scaledLaw P X V (u n)).real {y | t < L y}) atTop
          (𝓝 (w L * t ^ (-α))) := by
        refine ((tendsto_linear_mul hV hw L ht).comp hu).congr' ?_
        filter_upwards [hu.eventually hV.eventually_pos, hu.eventually_gt_atTop 0] with n hVn hun
        rw [scaledLaw_real_linear_lt hX hun hVn.le, Function.comp_apply, inv_mul_eq_div]
      have hreal := tendsto_nhds_unique key hlim
      rw [← ofReal_measureReal (hfinL t ht), hreal]
  -- the countable set of bad levels above `s / 2`
  set ρ := μ.restrict {y | s / 2 < L y}
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.2 (hfinL _ (half_pos hs))
  have hcount := Measure.countable_meas_level_set_pos (μ := ρ) L.measurable
  have hnull : ∀ t, s / 2 < t → t ∉ {t : ℝ | 0 < ρ {y | L y = t}} → μ {y | L y = t} = 0 :=
    fun t ht hN => by
      simp only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] at hN
      rw [Measure.restrict_apply (measurableSet_eq_fun L.measurable measurable_const)] at hN
      rwa [inter_eq_left.2 (show {x : E | L x = t} ⊆ {y | s / 2 < L y} from
        fun y (hy : L y = t) => (show s / 2 < L y by rw [hy]; exact ht))] at hN
  have hdense := hcount.dense_compl ℝ
  have hex : ∀ k : ℕ, ∃ t ∈ {t : ℝ | 0 < ρ {y | L y = t}}ᶜ,
      t ∈ Ioo s (s + 1 / ((k : ℝ) + 1)) := fun k =>
    hdense.exists_between (lt_add_of_pos_right s (by positivity))
  choose t htN ht using hex
  have ht_pos : ∀ k, 0 < t k := fun k => hs.trans (ht k).1
  have hval : ∀ k, μ {y | t k < L y} = ENNReal.ofReal (w L * t k ^ (-α)) := fun k =>
    hgood _ (ht_pos k) (hnull _ (by linarith [(ht k).1]) (htN k))
  have hwL : 0 ≤ w L := limit_nonneg hV hw L
  have ht_lim : Tendsto t atTop (𝓝 s) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun k => (ht k).1.le) (fun k => (ht k).2.le)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add s
  have hval_lim : Tendsto (fun k => ENNReal.ofReal (w L * t k ^ (-α))) atTop
      (𝓝 (ENNReal.ofReal (w L * s ^ (-α)))) :=
    ENNReal.tendsto_ofReal (((Real.continuousAt_rpow_const _ _ (Or.inl hs.ne')).tendsto.comp
      ht_lim).const_mul _)
  refine le_antisymm ?_ ?_
  · -- upper bound by continuity from below
    have hU : {y : E | s < L y} = ⋃ k : ℕ, {y | s + 1 / ((k : ℝ) + 1) < L y} := by
      ext y
      simp only [mem_ofPred_eq, mem_iUnion]
      refine ⟨fun hy => ?_, fun ⟨k, hk⟩ => lt_trans (by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith) hk⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨k, by linarith⟩
    have hmono : Monotone fun k : ℕ => {y : E | s + 1 / ((k : ℝ) + 1) < L y} := by
      intro i j hij y hy
      simp only [mem_ofPred_eq] at hy ⊢
      refine lt_of_le_of_lt ?_ hy
      gcongr
    rw [hU]
    refine le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) fun k => ?_
    calc μ {y | s + 1 / ((k : ℝ) + 1) < L y} ≤ μ {y | t k < L y} :=
          measure_mono fun y (hy : _ < _) => lt_trans (ht k).2 hy
      _ = ENNReal.ofReal (w L * t k ^ (-α)) := hval k
      _ ≤ ENNReal.ofReal (w L * s ^ (-α)) := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs (ht k).1.le
            (by linarith)) hwL)
  · refine le_of_tendsto' hval_lim fun k => ?_
    rw [← hval k]
    exact measure_mono fun y (hy : _ < _) => lt_trans (ht k).1 hy

/-- Spheres are null for a measure homogeneous of order `-α` and finite away from the origin. -/
theorem measure_norm_eq_zero_of_map_smul {μ : Measure E} {α : ℝ}
    (hhom : ∀ t > 0, μ.map (fun y => t • y) = ENNReal.ofReal (t ^ α) • μ)
    (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞) {c : ℝ} (hc : 0 < c) : μ {y | ‖y‖ = c} = 0 := by
  have hr : 0 < c / 4 := by positivity
  have hfin : IsFiniteMeasure (μ.restrict {y | c / 4 < ‖y‖}) :=
    isFiniteMeasure_restrict.2 (hμ _ hr).ne
  have hcount := Measure.countable_meas_level_set_pos (μ := μ.restrict {y | c / 4 < ‖y‖})
    (continuous_norm.measurable (α := E))
  obtain ⟨t, ht, hct⟩ := (hcount.dense_compl ℝ).exists_between (show c / 2 < c by linarith)
  have ht0 : 0 < t := lt_trans (half_pos hc) hct.1
  have hνt : μ.restrict {y | c / 4 < ‖y‖} {y | ‖y‖ = t} = 0 := by
    simpa using ht
  have hμt : μ {y | ‖y‖ = t} = 0 := by
    rw [Measure.restrict_apply (measurableSet_eq_fun continuous_norm.measurable
      measurable_const)] at hνt
    rwa [inter_eq_left.2 (show {y : E | ‖y‖ = t} ⊆ {y | c / 4 < ‖y‖} from
      fun y (hy : ‖y‖ = t) => (show c / 4 < ‖y‖ by rw [hy]; linarith [hct.1]))] at hνt
  have hpre : {y : E | ‖y‖ = c} = (fun y => (t / c) • y) ⁻¹' {y | ‖y‖ = t} := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos ht0 hc)]
    rw [div_mul_eq_mul_div, div_eq_iff hc.ne']
    exact ⟨fun hy => by rw [hy], fun hy => mul_left_cancel₀ ht0.ne' hy⟩
  have := congrArg (fun ν : Measure E => ν {y | ‖y‖ = t}) (hhom _ (div_pos ht0 hc))
  simp only [Measure.map_apply (measurable_const_smul _)
    (measurableSet_eq_fun continuous_norm.measurable measurable_const), Measure.smul_apply,
    smul_eq_mul, hμt, mul_zero] at this
  rw [hpre, this]

/-- **The converse Cramér–Wold device for non-integer indices**, normalized form
([BDM02, Theorem 1.1 (i)]). Let `X` be a random vector in a finite-dimensional real normed space
and `V` an antitone function regularly varying with index `-α`, `α > 0` not an integer, such that
`P(L X > x) / V(x) → w(L)` for every continuous linear functional `L`, with `w(L₀) ≠ 0` for some
`L₀`. Then `X` is regularly varying with index `α`; moreover
`P(‖X‖ > x) / V(x) → κ > 0` and the exponent measure gives mass `w(L) / κ` to `{L > 1}`. -/
theorem isRegVarVector_of_tendsto_linear_of_antitone [IsProbabilityMeasure P]
    [FiniteDimensional ℝ E] (hX : Measurable X) {α : ℝ} (hα : 0 < α) (hαZ : ∀ k : ℤ, α ≠ k)
    {V : ℝ → ℝ} (hVa : Antitone V) (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    {L₀ : StrongDual ℝ E} (hL₀ : w L₀ ≠ 0) :
    ∃ (μ : Measure E) (κ : ℝ), 0 < κ ∧ IsRegVarVector P X α μ ∧
      Tendsto (fun x => P.real {ω | x < ‖X ω‖} / V x) atTop (𝓝 κ) ∧
      ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ENNReal.ofReal (w L / κ) := by
  obtain ⟨W, hW, htail⟩ := exists_limit_tail_le hX hV hw
  -- any two limit points coincide
  have huniq : ∀ {u u' : ℕ → ℝ}, Tendsto u atTop atTop → Tendsto u' atTop atTop →
      ∀ {μ μ' : Measure E}, μ {0} = 0 → μ' {0} = 0 →
      (∀ r > 0, μ {y | r < ‖y‖} < ∞) → (∀ r > 0, μ' {y | r < ‖y‖} < ∞) →
      (∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u n)) atTop (𝓝 (∫ y, f y ∂μ))) →
      (∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u' n)) atTop (𝓝 (∫ y, f y ∂μ'))) →
      μ = μ' := by
    intro u u' hu hu' μ μ' h0 h0' hfin hfin' hc hc'
    refine ext_of_halfSpace_of_tail hα hαZ hW hW (htail hu hfin hc) (htail hu' hfin' hc') h0 h0'
      fun L => ?_
    rw [limit_halfSpace hX hα hV hw hu hfin hc L one_pos,
      limit_halfSpace hX hα hV hw hu' hfin' hc' L one_pos]
  -- a limit point along `n ↦ n`
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨φ, μ, hφ, hμ0, hμfin, hμconv⟩ :=
    exists_subseq_tendsto hX hα hVa hV hw hL₀ hnat
  have hφu : Tendsto (fun n => ((φ n : ℕ) : ℝ)) atTop atTop := hnat.comp hφ.tendsto_atTop
  -- full convergence
  have hconv : ∀ f : E →ᵇ ℝ, VanishesNearZero f →
      Tendsto (fun x => ∫ y, f y ∂scaledLaw P X V x) atTop (𝓝 (∫ y, f y ∂μ)) := by
    intro f hf
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ψ, μ', hψ, hμ'0, hμ'fin, hμ'conv⟩ :=
      exists_subseq_tendsto hX hα hVa hV hw hL₀ hns
    have : μ' = μ := huniq (hns.comp hψ.tendsto_atTop) hφu hμ'0 hμ0 hμ'fin hμfin hμ'conv hμconv
    exact ⟨ψ, this ▸ hμ'conv f hf⟩
  have hμhalf : ∀ L : StrongDual ℝ E, ∀ s > 0, μ {y | s < L y} = ENNReal.ofReal (w L * s ^ (-α)) :=
    fun L s hs => limit_halfSpace hX hα hV hw hφu hμfin hμconv L hs
  have hμt := htail hφu hμfin hμconv
  -- homogeneity
  have hhom : ∀ t > 0, μ.map (fun y => t • y) = ENNReal.ofReal (t ^ α) • μ := by
    intro t ht
    have hsm : Measurable fun y : E => t • y := measurable_const_smul t
    have hpre : ∀ s : ℝ, (fun y : E => t • y) ⁻¹' {y | s < ‖y‖} = {y | s / t < ‖y‖} := fun s => by
      ext y
      simp only [mem_preimage, mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      rw [div_lt_iff₀ ht, mul_comm]
    refine ext_of_halfSpace_of_tail hα hαZ (C := ENNReal.ofReal (t ^ α) * W)
      (C' := ENNReal.ofReal (t ^ α) * W) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW) (fun s hs => ?_) (fun s hs => ?_) ?_ ?_
      fun L => ?_
    · rw [Measure.map_apply hsm (measurableSet_lt measurable_const continuous_norm.measurable),
        hpre]
      refine (hμt _ (div_pos hs ht)).trans_eq ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
      congr 2
      rw [Real.div_rpow hs.le ht.le, Real.rpow_neg ht.le, div_inv_eq_mul]
    · rw [Measure.smul_apply, smul_eq_mul, mul_comm (ENNReal.ofReal (s ^ (-α))), mul_assoc]
      exact mul_le_mul_right (by rw [mul_comm]; exact hμt s hs) _
    · rw [Measure.map_apply hsm (measurableSet_singleton 0)]
      convert hμ0 using 2
      ext y; simp [ht.ne']
    · rw [Measure.smul_apply, hμ0, smul_zero]
    · have hpre' : (fun y : E => t • y) ⁻¹' {y | 1 < L y} = {y | t⁻¹ < L y} := by
        ext y
        simp only [mem_preimage, mem_ofPred_eq, map_smul, smul_eq_mul]
        rw [inv_lt_iff_one_lt_mul₀' ht]
      rw [Measure.map_apply hsm (measurableSet_lt measurable_const L.measurable), hpre',
        hμhalf L _ (inv_pos.2 ht), Measure.smul_apply, smul_eq_mul,
        hμhalf L 1 one_pos, Real.one_rpow, mul_one, ← ENNReal.ofReal_mul
          (Real.rpow_nonneg ht.le _), Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv,
        mul_comm]
  -- the norm tail
  have hsphere : μ {y | ‖y‖ = 1} = 0 := measure_norm_eq_zero_of_map_smul hhom hμfin one_pos
  have hA : MeasurableSet {y : E | 1 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hfr : μ (frontier {y : E | 1 < ‖y‖}) = 0 :=
    measure_mono_null ((frontier_lt_subset_eq continuous_const continuous_norm).trans
      fun y (hy : 1 = ‖y‖) => (show ‖y‖ = 1 from hy.symm)) hsphere
  set κ := μ.real {y | 1 < ‖y‖}
  have hκlim : Tendsto (fun x => P.real {ω | x < ‖X ω‖} / V x) atTop (𝓝 κ) := by
    have key := tendsto_measureReal_of_vanishesNearZero (μs := fun x => scaledLaw P X V x)
      (fun x => inferInstance) hμfin hconv hA one_pos (fun y (hy : 1 < ‖y‖) => hy.le) hfr
    refine key.congr' ?_
    filter_upwards [hV.eventually_pos, eventually_gt_atTop 0] with x hVx hx
    rw [scaledLaw_real_norm_lt hX hx hVx.le, mul_one, inv_mul_eq_div]
  set a : ℝ := (‖L₀‖ + 1)⁻¹
  have ha : 0 < a := by positivity
  have hwL : 0 < w (a • L₀) := by
    rw [limit_smul hV hw L₀ ha]
    exact mul_pos (Real.rpow_pos_of_pos ha _)
      (lt_of_le_of_ne (limit_nonneg hV hw L₀) (Ne.symm hL₀))
  have hLn : ‖a • L₀‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, inv_mul_le_iff₀ (by positivity)]
    linarith
  have hsub : {y : E | 1 < (a • L₀) y} ⊆ {y | 1 < ‖y‖} := fun y (hy : 1 < (a • L₀) y) => by
    show 1 < ‖y‖
    calc 1 < (a • L₀) y := hy
      _ ≤ ‖a • L₀‖ * ‖y‖ := (le_abs_self _).trans (by simpa using (a • L₀).le_opNorm y)
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
      _ = ‖y‖ := one_mul _
  have hκ : 0 < κ := by
    have h1 : ENNReal.ofReal (w (a • L₀)) ≤ μ {y | 1 < ‖y‖} := by
      have := hμhalf (a • L₀) 1 one_pos
      rw [Real.one_rpow, mul_one] at this
      rw [← this]
      exact measure_mono hsub
    have h2 := ENNReal.toReal_mono (hμfin 1 one_pos).ne h1
    rw [ENNReal.toReal_ofReal hwL.le] at h2
    exact hwL.trans_le h2
  have hRV : IsRegularlyVarying (fun x => P.real {ω | x < ‖X ω‖}) (-α) :=
    IsRegularlyVarying.of_tendsto_div hV hκlim hκ
  refine ⟨ENNReal.ofReal κ⁻¹ • μ, κ, hκ, ⟨hRV, by rw [Measure.smul_apply, hμ0, smul_zero],
    fun r hr => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμfin r hr), fun f hf => ?_⟩, hκlim,
    fun L => ?_⟩
  · rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hκ.le), smul_eq_mul]
    have hinv := hκlim.inv₀ hκ.ne'
    refine (hinv.mul (hconv f hf)).congr' ?_
    filter_upwards [hV.eventually_pos, hRV.eventually_pos] with x hVx hPx
    rw [integral_scaledLaw hX hVx.le f.continuous.measurable, inv_div]
    field_simp
  · rw [Measure.smul_apply, smul_eq_mul, hμhalf L 1 one_pos, Real.one_rpow, mul_one,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hκ.le), inv_mul_eq_div]

/-- **The converse Cramér–Wold device for non-integer indices** ([BDM02, Theorem 1.1 (i)];
[BL09]). Let `X` be a random vector in a finite-dimensional real normed space and suppose that
for some function `V` regularly varying with index `-α`, `α > 0` **not an integer**, the tails of
all linear combinations satisfy `P(L X > x) / V(x) → w(L)` for every continuous linear functional
`L`, with `w` not identically zero. Then `X` is multivariate regularly varying with index `α`.
For integer `α` the statement fails ([HL06]). -/
theorem isRegVarVector_of_tendsto_linear [IsProbabilityMeasure P] [FiniteDimensional ℝ E]
    (hX : Measurable X) {α : ℝ} (hα : 0 < α) (hαZ : ∀ k : ℤ, α ≠ k)
    {V : ℝ → ℝ} (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    (hw0 : ∃ L, w L ≠ 0) : ∃ μ : Measure E, IsRegVarVector P X α μ := by
  obtain ⟨L₀, hL₀⟩ := hw0
  have hpos : 0 < w L₀ := lt_of_le_of_ne (limit_nonneg hV hw L₀) (Ne.symm hL₀)
  set V₀ : ℝ → ℝ := fun x => P.real {ω | x < L₀ (X ω)}
  have hV₀a : Antitone V₀ := fun x y hxy =>
    measureReal_mono fun ω (hω : y < L₀ (X ω)) => lt_of_le_of_lt hxy hω
  have hV₀ : IsRegularlyVarying V₀ (-α) := IsRegularlyVarying.of_tendsto_div hV (hw L₀) hpos
  have hw₀ : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V₀ x) atTop (𝓝 (w L / w L₀)) := fun L => by
    refine ((hw L).div (hw L₀) hpos.ne').congr' ?_
    filter_upwards [hV.eventually_pos] with x hVx
    simp only [V₀, Pi.div_apply]
    rw [div_div_div_cancel_right₀ hVx.ne']
  obtain ⟨μ, -, -, hμ, -⟩ := isRegVarVector_of_tendsto_linear_of_antitone hX hα hαZ hV₀a hV₀ hw₀
    (L₀ := L₀) (by rw [div_self hpos.ne']; exact one_ne_zero)
  exact ⟨μ, hμ⟩

end Converse

end CramerWold

end ExtremeValueTheory
