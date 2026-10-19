/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.MaxStable.Basic
import ExtremeValueTheory.CDFBridge
import ExtremeValueTheory.DomainOfAttraction.Quantile

/-!
# Marginals, Fréchet bounds and the unit Fréchet standardization of a law on `ℝ^ι`

Preliminaries for the multivariate domain of attraction (`Multivariate/DomainOfAttraction.lean`).
For a probability law `μ` on `ι → ℝ` with joint distribution function `F(x) = μ (Iic x)` and
marginals `F_i(t) = μ {x | x i ≤ t}`:

* `marginal μ i`: the marginal `F_i` as a `CumulativeDistributionFunction` (the c.d.f. of the image
  measure);
* `one_sub_sum_le_measureReal_Iic`: the lower Fréchet (Bonferroni) bound
  `F(x) ≥ 1 - ∑_i (1 - F_i(x_i))`;
* `abs_measureReal_Iic_sub_le`: the Lipschitz bound `|F(x) - F(y)| ≤ ∑_i |F_i(x_i) - F_i(y_i)|`;
  in particular `F` is continuous at every point where all marginals are continuous
  (`continuousAt_measureReal_Iic`), and `F(x)` only depends on the marginal values `F_i(x_i)`;
* `frechetStandardization μ`: the image of `μ` under `x ↦ (-1 / log F_i(x_i))_i`. For continuous
  marginals it has unit Fréchet marginals (`frechetStandardization_measure_le`) and its
  distribution function at `y` is `F(t)` for any `t` with `F_i(t_i) = exp (-1 / y_i)`
  (`measureReal_Iic_frechetStandardization`); this is the reduction to standardized margins of
  [dHF, §6.1.1] and [Res87, Proposition 5.10].

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Chapter 6 [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Chapter 5 [Res87].
-/

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace ExtremeValueTheory

variable {ι : Type*}

section Marginals

/-- The `i`-th marginal distribution function `t ↦ μ {x | x i ≤ t}` of a probability law on
`ι → ℝ`: the c.d.f. of the image of `μ` under the `i`-th coordinate. -/
noncomputable def marginal (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (i : ι) :
    CumulativeDistributionFunction :=
  CumulativeDistributionFunction.ofMeasure (μ.map fun x ↦ x i)

variable {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ]

lemma measurableSet_apply_le (i : ι) (t : ℝ) : MeasurableSet {x : ι → ℝ | x i ≤ t} :=
  measurableSet_le (measurable_pi_apply i) measurable_const

lemma marginal_apply (i : ι) (t : ℝ) : marginal μ i t = μ.real {x | x i ≤ t} := by
  change cdf (μ.map fun x ↦ x i) t = _
  rw [cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply (measurable_pi_apply i) measurableSet_Iic]
  rfl

lemma marginal_mono (i : ι) : Monotone (marginal μ i) := (marginal μ i).mono'

/-- The marginal survival function: `μ {x | t < x i} = 1 - F_i(t)`. -/
lemma measureReal_lt_apply (i : ι) (t : ℝ) : μ.real {x | t < x i} = 1 - marginal μ i t := by
  rw [marginal_apply, show {x : ι → ℝ | t < x i} = {x | x i ≤ t}ᶜ by ext; simp,
    probReal_compl_eq_one_sub (measurableSet_apply_le i t)]

lemma measureReal_Iic_le_marginal (x : ι → ℝ) (i : ι) : μ.real (Iic x) ≤ marginal μ i (x i) := by
  rw [marginal_apply]
  exact measureReal_mono fun z hz ↦ hz i

/-- The mass of a coordinate strip is bounded by the increment of the marginal. -/
lemma measureReal_strip_le (i : ι) (a b : ℝ) :
    μ.real {z | a < z i ∧ z i ≤ b} ≤ |marginal μ i b - marginal μ i a| := by
  rcases le_total a b with hab | hab
  · have : {z : ι → ℝ | a < z i ∧ z i ≤ b} = {z | z i ≤ b} \ {z | z i ≤ a} := by
      ext; simp [and_comm]
    rw [this, measureReal_sdiff (μ := μ) (s₁ := {z : ι → ℝ | z i ≤ b})
      (s₂ := {z : ι → ℝ | z i ≤ a}) (fun z hz ↦ le_trans hz hab) (measurableSet_apply_le i a),
      marginal_apply, marginal_apply]
    exact le_abs_self _
  · have : {z : ι → ℝ | a < z i ∧ z i ≤ b} = ∅ := by
      ext z; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro h; linarith
    rw [this, measureReal_empty]
    exact abs_nonneg _

variable [Fintype ι]

/-- `F(x) ≤ F(y) + ∑_i μ {y_i < z_i ≤ x_i}`. -/
lemma measureReal_Iic_le_add_sum (x y : ι → ℝ) :
    μ.real (Iic x) ≤ μ.real (Iic y) + ∑ i, μ.real {z | y i < z i ∧ z i ≤ x i} := by
  have hsub : Iic x ⊆ Iic y ∪ ⋃ i, {z : ι → ℝ | y i < z i ∧ z i ≤ x i} := by
    intro z hz
    by_cases h : z ∈ Iic y
    · exact Or.inl h
    · right
      simp only [mem_Iic, Pi.le_def, not_forall, not_le] at h
      obtain ⟨i, hi⟩ := h
      exact mem_iUnion.2 ⟨i, hi, hz i⟩
  calc μ.real (Iic x) ≤ μ.real (Iic y ∪ ⋃ i, {z : ι → ℝ | y i < z i ∧ z i ≤ x i}) :=
        measureReal_mono hsub
    _ ≤ μ.real (Iic y) + μ.real (⋃ i, {z : ι → ℝ | y i < z i ∧ z i ≤ x i}) :=
        measureReal_union_le _ _
    _ ≤ _ := by gcongr; exact measureReal_iUnion_fintype_le _

/-- **The Lipschitz bound**: `|F(x) - F(y)| ≤ ∑_i |F_i(x_i) - F_i(y_i)|`. In particular `F(x)`
only depends on the marginal values `F_i(x_i)`. -/
theorem abs_measureReal_Iic_sub_le (x y : ι → ℝ) :
    |μ.real (Iic x) - μ.real (Iic y)| ≤ ∑ i, |marginal μ i (x i) - marginal μ i (y i)| := by
  rw [abs_sub_le_iff]
  constructor
  · have h1 := measureReal_Iic_le_add_sum (μ := μ) x y
    have h2 : ∑ i, μ.real {z | y i < z i ∧ z i ≤ x i} ≤
        ∑ i, |marginal μ i (x i) - marginal μ i (y i)| :=
      Finset.sum_le_sum fun i _ ↦ measureReal_strip_le i _ _
    linarith
  · have h1 := measureReal_Iic_le_add_sum (μ := μ) y x
    have h2 : ∑ i, μ.real {z | x i < z i ∧ z i ≤ y i} ≤
        ∑ i, |marginal μ i (x i) - marginal μ i (y i)| :=
      Finset.sum_le_sum fun i _ ↦ (measureReal_strip_le i _ _).trans_eq (abs_sub_comm _ _)
    linarith

/-- The joint distribution function is continuous at every point at which all marginals are
continuous. -/
theorem continuousAt_measureReal_Iic {x : ι → ℝ}
    (hx : ∀ i, ContinuousAt (marginal μ i) (x i)) :
    ContinuousAt (fun y ↦ μ.real (Iic y)) x := by
  have hsum : Tendsto (fun y : ι → ℝ ↦ ∑ i, |marginal μ i (y i) - marginal μ i (x i)|) (𝓝 x)
      (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ fun i _ ↦
      (((hx i).tendsto.comp ((continuous_apply i).tendsto x)).sub_const
        (marginal μ i (x i))).abs
    simpa using this
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) (fun y ↦ ?_) hsum)
  rw [Real.dist_eq]
  exact abs_measureReal_Iic_sub_le y x

/-- **The lower Fréchet (Bonferroni) bound**: `F(x) ≥ 1 - ∑_i (1 - F_i(x_i))`. -/
theorem one_sub_sum_le_measureReal_Iic (x : ι → ℝ) :
    1 - ∑ i, (1 - marginal μ i (x i)) ≤ μ.real (Iic x) := by
  have hc : (Iic x)ᶜ ⊆ ⋃ i, {z : ι → ℝ | x i < z i} := by
    intro z hz
    simp only [mem_compl_iff, mem_Iic, Pi.le_def, not_forall, not_le] at hz
    obtain ⟨i, hi⟩ := hz
    exact mem_iUnion.2 ⟨i, hi⟩
  have h1 := (measureReal_mono (μ := μ) hc).trans (measureReal_iUnion_fintype_le _)
  rw [probReal_compl_eq_one_sub measurableSet_Iic] at h1
  simp only [measureReal_lt_apply] at h1
  linarith

end Marginals

section NullSets

variable {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ]

lemma measure_eq_zero_of_measureReal_le_zero {s : Set (ι → ℝ)} (h : μ.real s ≤ 0) : μ s = 0 :=
  (measureReal_eq_zero_iff).1 (le_antisymm h measureReal_nonneg)

/-- A continuous marginal has no atoms. -/
lemma measure_apply_eq_eq_zero {i : ι} (hc : Continuous (marginal μ i)) (r : ℝ) :
    μ {z | z i = r} = 0 := by
  refine measure_eq_zero_of_measureReal_le_zero ?_
  have hle : ∀ s < r, μ.real {z : ι → ℝ | z i = r} ≤ marginal μ i r - marginal μ i s := by
    intro s hs
    refine (measureReal_mono (μ := μ) (show {z : ι → ℝ | z i = r} ⊆ {z | s < z i ∧ z i ≤ r} from
      fun z (hz : z i = r) ↦ ⟨hz ▸ hs, hz.le⟩)).trans
      ((measureReal_strip_le i s r).trans_eq (abs_of_nonneg ?_))
    exact sub_nonneg.2 (marginal_mono i hs.le)
  have ht : Tendsto (fun s ↦ marginal μ i r - marginal μ i s) (𝓝[<] r) (𝓝 0) := by
    have := ((hc.tendsto r).mono_left (nhdsWithin_le_nhds (s := Iio r))).const_sub
      (marginal μ i r)
    simpa using this
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall hle)

/-- With a continuous marginal, `{z | t < z_i, F_i(z_i) ≤ F_i(t)}` is a null set (the flat pieces
of `F_i` carry no mass). -/
lemma measure_lt_and_marginal_le_eq_zero {i : ι} (hc : Continuous (marginal μ i)) (t : ℝ) :
    μ {z | t < z i ∧ marginal μ i (z i) ≤ marginal μ i t} = 0 := by
  set g := marginal μ i
  rcases (g.apply_le_one t).lt_or_eq with h1 | h1
  · obtain ⟨M, hM⟩ := (g.tendsto_atTop.eventually (lt_mem_nhds h1)).exists
    set S := {s | g s ≤ g t}
    have hSbdd : BddAbove S := ⟨M, fun s (hs : g s ≤ g t) ↦ by
      by_contra hcon
      have := marginal_mono (μ := μ) i (not_le.1 hcon).le
      change g M ≤ g s at this
      linarith⟩
    have htS : t ∈ S := le_refl (g t)
    have hclosed : IsClosed S := isClosed_le hc continuous_const
    have hs0 : sSup S ∈ S := hclosed.csSup_mem ⟨t, htS⟩ hSbdd
    have hts : t ≤ sSup S := le_csSup hSbdd htS
    refine measure_eq_zero_of_measureReal_le_zero ?_
    refine (measureReal_mono (μ := μ) (show {z : ι → ℝ | t < z i ∧ g (z i) ≤ g t} ⊆
      {z | t < z i ∧ z i ≤ sSup S} from fun z hz ↦ ⟨hz.1, le_csSup hSbdd hz.2⟩)).trans ((measureReal_strip_le i t (sSup S)).trans_eq ?_)
    have : g (sSup S) = g t := le_antisymm hs0 (marginal_mono i hts)
    rw [this, sub_self, abs_zero]
  · refine measure_mono_null (show {z : ι → ℝ | t < z i ∧ g (z i) ≤ g t} ⊆ {z | t < z i} from
      fun z hz ↦ hz.1) ?_
    refine measure_eq_zero_of_measureReal_le_zero ?_
    rw [measureReal_lt_apply, h1, sub_self]

/-- With a continuous marginal, `{z | F_i(z_i) = 1}` is a null set. -/
lemma measure_marginal_eq_one_eq_zero {i : ι} (hc : Continuous (marginal μ i)) :
    μ {z | marginal μ i (z i) = 1} = 0 := by
  set g := marginal μ i
  set S := {s | g s = 1}
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine measure_mono_null (fun z (hz : g (z i) = 1) ↦ ?_) measure_empty
    have : z i ∈ S := hz
    rw [hS] at this
    exact this
  obtain ⟨m, hm⟩ := (g.tendsto_atBot.eventually (gt_mem_nhds zero_lt_one)).exists
  have hSbdd : BddBelow S := ⟨m, fun s (hs : g s = 1) ↦ by
    by_contra hcon
    have := marginal_mono (μ := μ) i (not_le.1 hcon).le
    change g s ≤ g m at this
    linarith⟩
  have hclosed : IsClosed S := isClosed_eq hc continuous_const
  have hr : sInf S ∈ S := hclosed.csInf_mem hS hSbdd
  have hsub : {z : ι → ℝ | g (z i) = 1} ⊆ {z | sInf S < z i} ∪ {z | z i = sInf S} := by
    intro z (hz : g (z i) = 1)
    rcases (csInf_le hSbdd (show z i ∈ S from hz)).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  refine measure_mono_null hsub (measure_union_null ?_ (measure_apply_eq_eq_zero hc _))
  refine measure_eq_zero_of_measureReal_le_zero ?_
  rw [measureReal_lt_apply]
  have : g (sInf S) = 1 := hr
  rw [this, sub_self]

end NullSets

section Standardization

variable {μ : Measure (ι → ℝ)} [IsProbabilityMeasure μ]

/-- The unit Fréchet transform `x ↦ (-1 / log F_i(x_i))_i`. -/
noncomputable def frechetTransform (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (x : ι → ℝ) : ι → ℝ :=
  fun i ↦ -1 / Real.log (marginal μ i (x i))

lemma measurable_frechetTransform : Measurable (frechetTransform μ) :=
  measurable_pi_iff.2 fun i ↦ (measurable_const.div (Real.measurable_log.comp
    ((marginal_mono (μ := μ) i).measurable.comp (measurable_pi_apply i))) :
      Measurable fun x : ι → ℝ ↦ -1 / Real.log (marginal μ i (x i)))

/-- The **unit Fréchet standardization** of `μ`: the law of `(-1 / log F_i(X_i))_i` for `X ∼ μ`.
For continuous marginals, its marginals are unit Fréchet (`frechetStandardization_measure_le`). -/
noncomputable def frechetStandardization (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] :
    Measure (ι → ℝ) :=
  μ.map (frechetTransform μ)

instance : IsProbabilityMeasure (frechetStandardization μ) := by
  unfold frechetStandardization; infer_instance

/-- `-1 / log g ≤ y` whenever `0 ≤ g ≤ exp (-1 / y)`. -/
lemma neg_one_div_log_le {g y : ℝ} (hy : 0 < y) (hg0 : 0 ≤ g) (hg : g ≤ Real.exp (-1 / y)) :
    -1 / Real.log g ≤ y := by
  rcases hg0.lt_or_eq with hg0 | rfl
  · have hlog : Real.log g ≤ -1 / y := (Real.log_le_iff_le_exp hg0).2 hg
    have hneg : Real.log g < 0 := hlog.trans_lt (div_neg_of_neg_of_pos (by norm_num) hy)
    rw [div_le_iff_of_neg hneg]
    have := mul_le_mul_of_nonneg_left hlog hy.le
    rwa [mul_div_cancel₀ _ hy.ne'] at this
  · simp [hy.le]

/-- Conversely, `-1 / log g ≤ y` and `0 ≤ g < 1` give `g ≤ exp (-1 / y)`. -/
lemma le_exp_of_neg_one_div_log_le {g y : ℝ} (hy : 0 < y) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (h : -1 / Real.log g ≤ y) : g ≤ Real.exp (-1 / y) := by
  rcases hg0.lt_or_eq with hg0 | rfl
  · have hneg : Real.log g < 0 := Real.log_neg hg0 hg1
    rw [div_le_iff_of_neg hneg] at h
    rw [← Real.log_le_iff_le_exp hg0, le_div_iff₀ hy]
    linarith
  · exact (Real.exp_pos _).le

variable [Fintype ι]

/-- The key identity behind the standardization: for `y > 0` and `t` with `F_i(t_i) = exp (-1/y_i)`
for `i ∈ s`, the events `{-1 / log F_i(X_i) ≤ y_i ∀ i ∈ s}` and `{X_i ≤ t_i ∀ i ∈ s}` have the same
probability (continuous marginals). -/
theorem measureReal_frechetTransform_le_eq (hc : ∀ i, Continuous (marginal μ i)) (s : Set ι)
    {y t : ι → ℝ} (hy : ∀ i ∈ s, 0 < y i)
    (ht : ∀ i ∈ s, marginal μ i (t i) = Real.exp (-1 / y i)) :
    μ.real {x | ∀ i ∈ s, frechetTransform μ x i ≤ y i} = μ.real {x | ∀ i ∈ s, x i ≤ t i} := by
  set A := {x | ∀ i ∈ s, frechetTransform μ x i ≤ y i}
  set B := {x : ι → ℝ | ∀ i ∈ s, x i ≤ t i}
  have hBA : B ⊆ A := fun x hx i hi ↦ neg_one_div_log_le (hy i hi) ((marginal μ i).apply_nonneg _)
    ((ht i hi) ▸ marginal_mono i (hx i hi))
  have hnull : μ (A \ B) = 0 := by
    have hsub : A \ B ⊆ ⋃ i, ({z | t i < z i ∧ marginal μ i (z i) ≤ marginal μ i (t i)} ∪
        {z | marginal μ i (z i) = 1}) := by
      rintro x ⟨hxA, hxB⟩
      simp only [B, mem_ofPred_eq, not_forall, not_le] at hxB
      obtain ⟨i, hi, hlt⟩ := hxB
      refine mem_iUnion.2 ⟨i, ?_⟩
      rcases ((marginal μ i).apply_le_one (x i)).lt_or_eq with h1 | h1
      · refine Or.inl ⟨hlt, ?_⟩
        rw [ht i hi]
        exact le_exp_of_neg_one_div_log_le (hy i hi) ((marginal μ i).apply_nonneg _) h1 (hxA i hi)
      · exact Or.inr h1
    exact measure_mono_null hsub (measure_iUnion_null fun i ↦ measure_union_null
      (measure_lt_and_marginal_le_eq_zero (hc i) _) (measure_marginal_eq_one_eq_zero (hc i)))
  have hle : μ A ≤ μ B := by
    calc μ A ≤ μ (B ∪ A \ B) := measure_mono (by rw [union_sdiff_cancel hBA])
      _ ≤ μ B + μ (A \ B) := measure_union_le _ _
      _ = μ B := by rw [hnull, add_zero]
  rw [measureReal_def, measureReal_def, le_antisymm hle (measure_mono hBA)]

/-- **The standardized distribution function**: for continuous marginals, `y > 0` and any `t` with
`F_i(t_i) = exp (-1 / y_i)`, `P(Y ≤ y) = F(t)` for the unit Fréchet standardization `Y`. -/
theorem measureReal_Iic_frechetStandardization (hc : ∀ i, Continuous (marginal μ i))
    {y t : ι → ℝ} (hy : ∀ i, 0 < y i) (ht : ∀ i, marginal μ i (t i) = Real.exp (-1 / y i)) :
    (frechetStandardization μ).real (Iic y) = μ.real (Iic t) := by
  rw [frechetStandardization, measureReal_def, Measure.map_apply measurable_frechetTransform
    measurableSet_Iic, ← measureReal_def]
  have := measureReal_frechetTransform_le_eq hc univ (fun i _ ↦ hy i) (fun i _ ↦ ht i)
  simp only [mem_univ, forall_const] at this
  convert this using 2 <;> ext <;> simp [Pi.le_def]

omit [Fintype ι] in
/-- Every value in `(0, 1)` is attained by a continuous marginal. -/
lemma exists_marginal_eq (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] {i : ι}
    (hc : Continuous (marginal μ i)) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ t, marginal μ i t = u := by
  obtain ⟨a, ha⟩ := ((marginal μ i).tendsto_atBot.eventually (gt_mem_nhds hu0)).exists
  obtain ⟨b, hb⟩ := ((marginal μ i).tendsto_atTop.eventually (lt_mem_nhds hu1)).exists
  exact mem_range_of_exists_le_of_exists_ge hc ⟨a, ha.le⟩ ⟨b, hb.le⟩

/-- **Unit Fréchet marginals of the standardization**: `P(Y_i ≤ y) = exp (-1 / y)` for `y > 0`. -/
theorem frechetStandardization_measure_le (hc : ∀ i, Continuous (marginal μ i)) (i : ι) {y : ℝ}
    (hy : 0 < y) :
    frechetStandardization μ {x | x i ≤ y} = ENNReal.ofReal (Real.exp (-y⁻¹)) := by
  obtain ⟨t, ht⟩ := exists_marginal_eq μ (hc i) (Real.exp_pos (-1 / y))
    (Real.exp_lt_one_iff.2 (div_neg_of_neg_of_pos (by norm_num) hy))
  have key := measureReal_frechetTransform_le_eq hc {i} (y := fun _ ↦ y) (t := fun _ ↦ t)
    (fun _ _ ↦ hy) (fun j hj ↦ by rw [mem_singleton_iff.1 hj]; exact ht)
  simp only [mem_singleton_iff, forall_eq] at key
  rw [frechetStandardization, Measure.map_apply measurable_frechetTransform
    (measurableSet_apply_le i y), ← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def]
  change ENNReal.ofReal (μ.real {x | frechetTransform μ x i ≤ y}) = _
  rw [key, ← marginal_apply, ht, neg_div, one_div]

end Standardization

end ExtremeValueTheory
