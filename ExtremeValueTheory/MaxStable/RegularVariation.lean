/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.MaxStable.Uniqueness
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Simple max-stable vectors are regularly varying

PLACEHOLDER
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace ExtremeValueTheory

variable {ι : Type*}

/-! ### Convergence on lower-orthant complements propagates to boxes -/

section Boxes

/-- The closed lower orthant `{x | ∀ i, x i ≤ b i}`. -/
def lowerOrthant (b : ι → ℝ≥0∞) : Set (ι → ℝ≥0∞) := {x | ∀ i, x i ≤ b i}

lemma compl_exceedSet (b : ι → ℝ≥0∞) : (exceedSet b)ᶜ = lowerOrthant b := by
  ext; simp [exceedSet, lowerOrthant]

lemma exceedSet_antitone {d e : ι → ℝ≥0∞} (h : d ≤ e) : exceedSet e ⊆ exceedSet d :=
  fun _ ⟨i, hi⟩ ↦ ⟨i, (h i).trans_lt hi⟩

/-- The box `{x | ∀ i, c i ≠ 0 → c i < x i} ∩ {x | x ≤ b} ∩ {x | ∃ i, δ i < x i}`. -/
def boxSet (δ c b : ι → ℝ≥0∞) : Set (ι → ℝ≥0∞) :=
  upperOrthant c ∩ lowerOrthant b ∩ exceedSet δ

lemma boxSet_inter (δ c b c' b' : ι → ℝ≥0∞) :
    boxSet δ c b ∩ boxSet δ c' b' = boxSet δ (c ⊔ c') (b ⊓ b') := by
  have hU : upperOrthant c ∩ upperOrthant c' = upperOrthant (c ⊔ c') := by
    ext x
    simp only [upperOrthant, mem_inter_iff, mem_ofPred_eq]
    rw [← forall_and]
    refine forall_congr' fun i ↦ ?_
    by_cases h : c i = 0 <;> by_cases h' : c' i = 0 <;> simp [h, h']
  have hL : lowerOrthant b ∩ lowerOrthant b' = lowerOrthant (b ⊓ b') := by
    ext x; simp [lowerOrthant, forall_and]
  rw [boxSet, boxSet, boxSet, ← hU, ← hL]
  ext x; simp only [mem_inter_iff]; tauto

variable [Fintype ι]

lemma measurableSet_boxSet (δ c b : ι → ℝ≥0∞) : MeasurableSet (boxSet δ c b) := by
  refine ((measurableSet_upperOrthant c).inter ?_).inter (measurableSet_exceedSet δ)
  rw [← compl_exceedSet]
  exact (measurableSet_exceedSet b).compl

/-- A box is the difference of two upper-orthant–exceedance sets. -/
lemma boxSet_eq_diff (δ c b : ι → ℝ≥0∞) :
    boxSet δ c b = (upperOrthant c ∩ exceedSet (δ ⊓ b)) \ (upperOrthant c ∩ exceedSet b) := by
  ext x
  simp only [boxSet, lowerOrthant, exceedSet, mem_inter_iff, mem_diff, mem_ofPred_eq,
    Pi.inf_apply]
  constructor
  · rintro ⟨⟨hU, hL⟩, i, hi⟩
    exact ⟨⟨hU, i, inf_lt_iff.2 (Or.inl hi)⟩, fun ⟨_, j, hj⟩ ↦ (hL j).not_gt hj⟩
  · rintro ⟨⟨hU, i, hi⟩, hn⟩
    have hL : ∀ j, x j ≤ b j := fun j ↦ not_lt.1 fun hj ↦ hn ⟨hU, j, hj⟩
    refine ⟨⟨hU, hL⟩, i, ?_⟩
    rcases inf_lt_iff.1 hi with h | h
    · exact h
    · exact absurd h (hL i).not_gt

variable {α : Type*} {l : Filter α} {μs : α → Measure (ι → ℝ≥0∞)} {ν : Measure (ι → ℝ≥0∞)}

/-- **Inclusion–exclusion for limits**: if finite measures `μs a` converge to `ν` on all complements
of lower orthants `{x | ∃ i, d i < x i}` (`d i ∈ (0, ∞]`), they converge on all the sets
`{x | ∀ i ∈ K, c i < x i} ∩ {x | ∃ i, d i < x i}`. -/
theorem tendsto_measureReal_upperSet_inter_exceedSet
    (hfin : ∀ a (d : ι → ℝ≥0∞), (∀ i, d i ≠ 0) → μs a (exceedSet d) ≠ ∞)
    (hνfin : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → ν (exceedSet d) ≠ ∞)
    (hconv : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) →
      Tendsto (fun a ↦ (μs a).real (exceedSet d)) l (𝓝 (ν.real (exceedSet d))))
    (K : Finset ι) (c : ι → ℝ≥0∞) (hc : ∀ i ∈ K, c i ≠ 0) (d : ι → ℝ≥0∞) (hd : ∀ i, d i ≠ 0) :
    Tendsto (fun a ↦ (μs a).real (upperSet K c ∩ exceedSet d)) l
      (𝓝 (ν.real (upperSet K c ∩ exceedSet d))) := by
  classical
  induction K using Finset.induction_on generalizing d with
  | empty => simpa [upperSet_empty] using hconv d hd
  | insert j K hj ih =>
    have hcK : ∀ i ∈ K, c i ≠ 0 := fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
    set e : ι → ℝ≥0∞ := Function.update (fun _ ↦ ∞) j (c j) with he_def
    have he : ∀ i, e i ≠ 0 := fun i ↦ by
      by_cases hij : i = j
      · subst hij; simpa [he_def] using hc i (Finset.mem_insert_self i K)
      · simp [he_def, Function.update_of_ne hij]
    have hde : ∀ i, (d ⊓ e) i ≠ 0 := fun i ↦
      (lt_inf_iff.2 ⟨pos_iff_ne_zero.2 (hd i), pos_iff_ne_zero.2 (he i)⟩).ne'
    have hY : MeasurableSet (upperSet K c ∩ exceedSet e) :=
      (measurableSet_upperSet K c).inter (measurableSet_exceedSet e)
    have key (m : Measure (ι → ℝ≥0∞))
        (hm : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → m (exceedSet d) ≠ ∞) :
        m.real (upperSet (insert j K) c ∩ exceedSet d) =
          m.real (upperSet K c ∩ exceedSet d) + m.real (upperSet K c ∩ exceedSet e) -
            m.real (upperSet K c ∩ exceedSet (d ⊓ e)) := by
      have h := measureReal_union_add_inter (μ := m) (s := upperSet K c ∩ exceedSet d) hY
        (ne_top_of_le_ne_top (hm d hd) (measure_mono inter_subset_right))
        (ne_top_of_le_ne_top (hm e he) (measure_mono inter_subset_right))
      have hXY : (upperSet K c ∩ exceedSet d) ∪ (upperSet K c ∩ exceedSet e) =
          upperSet K c ∩ exceedSet (d ⊓ e) := by
        rw [← exceedSet_union, inter_union_distrib_left]
      have hXY' : (upperSet K c ∩ exceedSet d) ∩ (upperSet K c ∩ exceedSet e) =
          upperSet (insert j K) c ∩ exceedSet d := by
        rw [upperSet_insert, ← exceedSet_update_top j (c j), ← he_def]
        ext x; simp only [mem_inter_iff]; tauto
      rw [hXY, hXY'] at h
      linarith
    simp_rw [key _ (hfin _), key ν hνfin]
    exact ((ih hcK d hd).add (ih hcK e he)).sub (ih hcK _ hde)

/-- Convergence on lower-orthant complements gives convergence on boxes. -/
theorem tendsto_measureReal_boxSet
    (hfin : ∀ a (d : ι → ℝ≥0∞), (∀ i, d i ≠ 0) → μs a (exceedSet d) ≠ ∞)
    (hνfin : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → ν (exceedSet d) ≠ ∞)
    (hconv : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) →
      Tendsto (fun a ↦ (μs a).real (exceedSet d)) l (𝓝 (ν.real (exceedSet d))))
    {δ : ι → ℝ≥0∞} (hδ : ∀ i, δ i ≠ 0) (c : ι → ℝ≥0∞) {b : ι → ℝ≥0∞} (hb : ∀ i, b i ≠ 0) :
    Tendsto (fun a ↦ (μs a).real (boxSet δ c b)) l (𝓝 (ν.real (boxSet δ c b))) := by
  classical
  have hδb : ∀ i, (δ ⊓ b) i ≠ 0 := fun i ↦
    (lt_inf_iff.2 ⟨pos_iff_ne_zero.2 (hδ i), pos_iff_ne_zero.2 (hb i)⟩).ne'
  have hsub : upperOrthant c ∩ exceedSet b ⊆ upperOrthant c ∩ exceedSet (δ ⊓ b) :=
    inter_subset_inter_right _ (exceedSet_antitone inf_le_right)
  have hmeas : MeasurableSet (upperOrthant c ∩ exceedSet b) :=
    (measurableSet_upperOrthant c).inter (measurableSet_exceedSet b)
  have key (m : Measure (ι → ℝ≥0∞))
      (hm : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → m (exceedSet d) ≠ ∞) :
      m.real (boxSet δ c b) = m.real (upperOrthant c ∩ exceedSet (δ ⊓ b)) -
        m.real (upperOrthant c ∩ exceedSet b) := by
    rw [boxSet_eq_diff, measureReal_sdiff hsub hmeas
      (ne_top_of_le_ne_top (hm _ hδb) (measure_mono inter_subset_right))]
  simp_rw [key _ (hfin _), key ν hνfin, upperOrthant_eq_upperSet]
  have hc : ∀ i ∈ Finset.univ.filter fun i ↦ c i ≠ 0, c i ≠ 0 := fun i hi ↦ by simpa using hi
  exact (tendsto_measureReal_upperSet_inter_exceedSet hfin hνfin hconv _ c hc _ hδb).sub
    (tendsto_measureReal_upperSet_inter_exceedSet hfin hνfin hconv _ c hc _ hb)

/-- Finite intersections of boxes are boxes. -/
lemma exists_biInter_boxSet_eq (δ : ι → ℝ≥0∞) (s : ℕ → (ι → ℝ≥0∞) × (ι → ℝ≥0∞))
    (hs : ∀ k i, (s k).2 i ≠ 0) {u : Finset ℕ} (hu : u.Nonempty) :
    ∃ c b : ι → ℝ≥0∞, (∀ i, b i ≠ 0) ∧ ⋂ k ∈ u, boxSet δ (s k).1 (s k).2 = boxSet δ c b := by
  classical
  induction hu using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨(s a).1, (s a).2, hs a, by simp⟩
  | cons a u ha hu ih =>
    obtain ⟨c, b, hb, hcb⟩ := ih
    refine ⟨(s a).1 ⊔ c, (s a).2 ⊓ b, fun i ↦ ?_, ?_⟩
    · exact (lt_inf_iff.2 ⟨pos_iff_ne_zero.2 (hs a i), pos_iff_ne_zero.2 (hb i)⟩).ne'
    · rw [Finset.cons_eq_insert, Finset.set_biInter_insert, hcb, boxSet_inter]

/-- Convergence on lower-orthant complements gives convergence on finite unions of boxes. -/
theorem tendsto_measureReal_iUnion_boxSet
    (hfin : ∀ a (d : ι → ℝ≥0∞), (∀ i, d i ≠ 0) → μs a (exceedSet d) ≠ ∞)
    (hνfin : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → ν (exceedSet d) ≠ ∞)
    (hconv : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) →
      Tendsto (fun a ↦ (μs a).real (exceedSet d)) l (𝓝 (ν.real (exceedSet d))))
    {δ : ι → ℝ≥0∞} (hδ : ∀ i, δ i ≠ 0) (s : ℕ → (ι → ℝ≥0∞) × (ι → ℝ≥0∞))
    (hs : ∀ k i, (s k).2 i ≠ 0) (n : ℕ) :
    Tendsto (fun a ↦ (μs a).real (⋃ k ∈ Finset.range n, boxSet δ (s k).1 (s k).2)) l
      (𝓝 (ν.real (⋃ k ∈ Finset.range n, boxSet δ (s k).1 (s k).2))) := by
  have hmeas : ∀ k ∈ Finset.range n, MeasurableSet (boxSet δ (s k).1 (s k).2) :=
    fun k _ ↦ measurableSet_boxSet _ _ _
  have hfin' (m : Measure (ι → ℝ≥0∞))
      (hm : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → m (exceedSet d) ≠ ∞) :
      ∀ k ∈ Finset.range n, m (boxSet δ (s k).1 (s k).2) ≠ ∞ :=
    fun k _ ↦ ne_top_of_le_ne_top (hm δ hδ) (measure_mono inter_subset_right)
  simp_rw [measureReal_biUnion_eq_sum_powerset hmeas (hfin' _ (hfin _)),
    measureReal_biUnion_eq_sum_powerset hmeas (hfin' ν hνfin)]
  refine tendsto_finsetSum _ fun u hu ↦ ?_
  obtain ⟨c, b, hb, hcb⟩ := exists_biInter_boxSet_eq δ s hs (Finset.mem_filter.1 hu).2
  simp_rw [hcb]
  exact (tendsto_measureReal_boxSet hfin hνfin hconv hδ c hb).const_mul _

end Boxes

/-! ### Real and extended coordinates -/

section Coordinates

/-- Coordinatewise `ENNReal.ofReal`. -/
noncomputable def ofRealVec (y : ι → ℝ) : ι → ℝ≥0∞ := fun i ↦ ENNReal.ofReal (y i)

/-- Coordinatewise `ENNReal.toReal`. -/
noncomputable def toRealVec (w : ι → ℝ≥0∞) : ι → ℝ := fun i ↦ (w i).toReal

lemma measurable_ofRealVec : Measurable (ofRealVec (ι := ι)) :=
  Measurable.of_eval fun i ↦ ENNReal.measurable_ofReal.comp (measurable_pi_apply i)

lemma measurable_toRealVec : Measurable (toRealVec (ι := ι)) :=
  Measurable.of_eval fun i ↦ ENNReal.measurable_toReal.comp (measurable_pi_apply i)

lemma ofRealVec_toRealVec {w : ι → ℝ≥0∞} (hw : ∀ i, w i ≠ ∞) : ofRealVec (toRealVec w) = w :=
  funext fun i ↦ ENNReal.ofReal_toReal (hw i)

/-- An exceedance set in real coordinates is the decreasing intersection of the exceedance sets
at the truncated thresholds `min (d i, n + 1)`. -/
lemma ofRealVec_mem_exceedSet_iff [Fintype ι] (y : ι → ℝ) (d : ι → ℝ≥0∞) :
    ofRealVec y ∈ exceedSet d ↔
      ∀ n : ℕ, ofRealVec y ∈ exceedSet fun i ↦ d i ⊓ ((n : ℝ≥0∞) + 1) := by
  constructor
  · rintro ⟨i, hi⟩ n
    exact ⟨i, inf_le_left.trans_lt hi⟩
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_gt (∑ i, |y i|)
    obtain ⟨i, hi⟩ := h n
    refine ⟨i, ?_⟩
    have hy : y i < (n : ℝ) + 1 := by
      have := Finset.single_le_sum (f := fun j ↦ |y j|) (fun j _ ↦ abs_nonneg (y j))
        (Finset.mem_univ i)
      linarith [le_abs_self (y i)]
    have hy' : ENNReal.ofReal (y i) < (n : ℝ≥0∞) + 1 := by
      rw [show ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) by
        rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one]]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hy
    rcases inf_lt_iff.1 hi with h' | h'
    · exact h'
    · exact absurd h' (not_lt.2 hy'.le)

end Coordinates

/-! ### The tails of a simple max-stable vector -/

section Tails

variable [Fintype ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ι → ℝ} {H : Measure (ι → ℝ≥0∞)}

/-- `x (1 - exp (-a / x)) → a` as `x → ∞`. -/
lemma tendsto_mul_one_sub_exp {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun x : ℝ ↦ x * (1 - Real.exp (-(x⁻¹ * a)))) atTop (𝓝 a) := by
  have hlow : Tendsto (fun x : ℝ ↦ a / (1 + a / x)) atTop (𝓝 a) := by
    have := (tendsto_const_nhds (x := a)).div ((tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := a)).div_atTop tendsto_id)) (by norm_num)
    rw [add_zero, div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    set u := x⁻¹ * a with hu
    have hu0 : 0 ≤ u := mul_nonneg (inv_nonneg.2 hx.le) ha
    have h1 := Real.add_one_le_exp u
    have h2 : Real.exp (-u) * Real.exp u = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 : Real.exp (-u) * (1 + u) ≤ 1 := by nlinarith [Real.exp_pos (-u)]
    have e : a / (1 + a / x) = x * u / (1 + u) := by
      rw [hu]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have := Real.add_one_le_exp (-(x⁻¹ * a))
    have e : x * (x⁻¹ * a) = a := by field_simp
    nlinarith

variable (hX : Measurable X) (hS : HasSpectralMeasure (P.map X) H)
include hX hS

/-- **The joint tail at finite thresholds**: `P(∃ i, X i / x > d i) = 1 - exp (-Φ(d) / x)` with
`Φ(d) = ∫ max_i w i / d i dH(w)`, for `d ∈ (0, ∞)^ι`. -/
lemma measureReal_exceedSet_of_ne_top {x : ℝ} (hx : 0 < x) {d : ι → ℝ≥0∞} (hd0 : ∀ i, d i ≠ 0)
    (hdtop : ∀ i, d i ≠ ∞) :
    P.real {ω | ofRealVec (x⁻¹ • X ω) ∈ exceedSet d} =
      1 - Real.exp (-(x⁻¹ * (∫⁻ w, ⨆ i, w i / d i ∂H).toReal)) := by
  set y : ι → ℝ := fun i ↦ x * (d i).toReal with hydef
  have hy : ∀ i, 0 < y i := fun i ↦ mul_pos hx (ENNReal.toReal_pos (hd0 i) (hdtop i))
  have hset : {ω | ofRealVec (x⁻¹ • X ω) ∈ exceedSet d} = (X ⁻¹' Iic y)ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, exceedSet, ofRealVec, Pi.smul_apply, smul_eq_mul, mem_compl_iff,
      mem_preimage, mem_Iic, Pi.le_def, not_forall, not_le, hydef]
    refine exists_congr fun i ↦ ?_
    rw [ENNReal.lt_ofReal_iff_toReal_lt (hdtop i), inv_mul_eq_div, lt_div_iff₀ hx, mul_comm]
  have hint : ∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂H =
      (ENNReal.ofReal x)⁻¹ * ∫⁻ w, ⨆ i, w i / d i ∂H := by
    rw [← lintegral_const_mul _ (Measurable.iSup fun i ↦ (measurable_pi_apply i).div_const _)]
    refine lintegral_congr fun w ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun i ↦ ?_
    rw [hydef, ENNReal.ofReal_mul hx.le, ENNReal.ofReal_toReal (hdtop i), div_eq_mul_inv,
      div_eq_mul_inv, ENNReal.mul_inv (Or.inr (hdtop i)) (Or.inl ENNReal.ofReal_ne_top),
      mul_left_comm]
  rw [hset, probReal_compl_eq_one_sub (hX measurableSet_Iic),
    ← map_measureReal_apply hX measurableSet_Iic, measureReal_def, hS y hy,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, hint, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hx.le]

/-- **The joint tail**: `P(∃ i, X i / x > d i) = 1 - exp (-Φ(d) / x)` for `d ∈ (0, ∞]^ι`, for a
finite spectral measure `H` on the sup-norm sphere. -/
theorem measureReal_exceedSet [IsFiniteMeasure H] (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) {x : ℝ}
    (hx : 0 < x) {d : ι → ℝ≥0∞} (hd0 : ∀ i, d i ≠ 0) :
    P.real {ω | ofRealVec (x⁻¹ • X ω) ∈ exceedSet d} =
      1 - Real.exp (-(x⁻¹ * (∫⁻ w, ⨆ i, w i / d i ∂H).toReal)) := by
  have hle := ae_le_one_of_ae_iSup_eq_one hH
  have hnt := ae_ne_top_of_ae_le_one hle
  have hfin := lintegral_apply_ne_top_of_le_one hle
  set dn : ℕ → ι → ℝ≥0∞ := fun n i ↦ d i ⊓ ((n : ℝ≥0∞) + 1) with hdn
  set A : ℕ → Set Ω := fun n ↦ {ω | ofRealVec (x⁻¹ • X ω) ∈ exceedSet (dn n)} with hA
  have hXs : Measurable fun ω ↦ x⁻¹ • X ω := hX.const_smul x⁻¹
  have hXx : Measurable fun ω ↦ ofRealVec (x⁻¹ • X ω) := measurable_ofRealVec.comp hXs

  have hAm (n : ℕ) : MeasurableSet (A n) := hXx (measurableSet_exceedSet _)
  have hanti : Antitone A := fun m n hmn ω hω ↦
    exceedSet_antitone (fun i ↦ inf_le_inf_left _ (by gcongr)) hω
  have hinter : ⋂ n, A n = {ω | ofRealVec (x⁻¹ • X ω) ∈ exceedSet d} := by
    ext ω
    simp only [mem_iInter, hA, hdn, mem_ofPred_eq]
    exact (ofRealVec_mem_exceedSet_iff _ d).symm
  have h1 : Tendsto (fun n ↦ P.real (A n)) atTop
      (𝓝 (P.real {ω | ofRealVec (x⁻¹ • X ω) ∈ exceedSet d})) := by
    have := tendsto_measure_iInter_atTop (μ := P) (fun n ↦ (hAm n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hinter] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  have hΦ : Tendsto (fun n ↦ ∫⁻ w, ⨆ i, w i / dn n i ∂H) atTop
      (𝓝 (∫⁻ w, ⨆ i, w i / d i ∂H)) := by
    rw [lintegral_iSup_div_eq_iInf hnt hfin hd0]
    exact tendsto_atTop_iInf fun m n hmn ↦ lintegral_mono (antitone_iSup_div_inf d hmn)
  have hΦr := (ENNReal.tendsto_toReal (lintegral_iSup_div_ne_top (fun i ↦ measurable_pi_apply i)
    hfin hd0)).comp hΦ
  have h2 : Tendsto (fun n ↦ P.real (A n)) atTop
      (𝓝 (1 - Real.exp (-(x⁻¹ * (∫⁻ w, ⨆ i, w i / d i ∂H).toReal)))) := by
    have hcont : Continuous fun t : ℝ ↦ 1 - Real.exp (-(x⁻¹ * t)) := by fun_prop
    refine ((hcont.tendsto _).comp hΦr).congr fun n ↦ ?_
    simp only [Function.comp_apply, hA]
    rw [measureReal_exceedSet_of_ne_top hX hS hx (fun i ↦ inf_add_one_ne_zero (hd0 i) n)
      (fun i ↦ inf_add_one_ne_top _ n)]
  exact tendsto_nhds_unique h1 h2

end Tails

/-! ### The exponent measure in real coordinates and the scaled laws -/

section Exponent

variable [Fintype ι] {H : Measure (ι → ℝ≥0∞)}

/-- The closed nonnegative orthant of `ℝ^ι`. -/
def posOrthant : Set (ι → ℝ) := {y | ∀ i, 0 ≤ y i}

lemma measurableSet_posOrthant : MeasurableSet (posOrthant (ι := ι)) := by
  have : posOrthant (ι := ι) = ⋂ i, {y | 0 ≤ y i} := by ext; simp [posOrthant]
  rw [this]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)

/-- The exponent measure `ν_H` of a spectral measure, in real coordinates. -/
noncomputable def spectralExponentMeasureReal (H : Measure (ι → ℝ≥0∞)) : Measure (ι → ℝ) :=
  (spectralExponentMeasure H).map toRealVec

lemma measurableSet_forall_ne_top : MeasurableSet {x : ι → ℝ≥0∞ | ∀ i, x i ≠ ∞} := by
  have : {x : ι → ℝ≥0∞ | ∀ i, x i ≠ ∞} = ⋂ i, (fun x : ι → ℝ≥0∞ ↦ x i) ⁻¹' {∞}ᶜ := by
    ext; simp
  rw [this]
  exact MeasurableSet.iInter fun i ↦ (measurableSet_singleton ∞).compl.preimage
    (measurable_pi_apply i)

lemma ae_spectralExponentMeasure_ne_top [SFinite H] (hH : ∀ᵐ w ∂H, ∀ i, w i ≠ ∞) :
    ∀ᵐ x ∂spectralExponentMeasure H, ∀ i, x i ≠ ∞ := by
  rw [spectralExponentMeasure, ae_map_iff measurable_coneMap.aemeasurable
    measurableSet_forall_ne_top]
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hH] with p hp i
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp i)

lemma map_ofRealVec_spectralExponentMeasureReal [SFinite H] (hH : ∀ᵐ w ∂H, ∀ i, w i ≠ ∞) :
    (spectralExponentMeasureReal H).map ofRealVec = spectralExponentMeasure H := by
  rw [spectralExponentMeasureReal, Measure.map_map measurable_ofRealVec measurable_toRealVec]
  conv_rhs => rw [← Measure.map_id (μ := spectralExponentMeasure H)]
  exact Measure.map_congr ((ae_spectralExponentMeasure_ne_top hH).mono fun x hx ↦
    ofRealVec_toRealVec hx)

lemma spectralExponentMeasureReal_preimage [SFinite H] (hH : ∀ᵐ w ∂H, ∀ i, w i ≠ ∞)
    {A : Set (ι → ℝ≥0∞)} (hA : MeasurableSet A) :
    spectralExponentMeasureReal H (ofRealVec ⁻¹' A) = spectralExponentMeasure H A := by
  rw [← Measure.map_apply measurable_ofRealVec hA, map_ofRealVec_spectralExponentMeasureReal hH]

lemma spectralExponentMeasureReal_compl_posOrthant :
    spectralExponentMeasureReal H posOrthantᶜ = 0 := by
  rw [spectralExponentMeasureReal, Measure.map_apply measurable_toRealVec
    measurableSet_posOrthant.compl]
  convert measure_empty (μ := spectralExponentMeasure H)
  ext x
  simp [posOrthant, toRealVec]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ι → ℝ}

/-- The scaled law `x P(X / x ∈ ·)`. -/
noncomputable def scaledLaw (P : Measure Ω) (X : Ω → ι → ℝ) (x : ℝ) : Measure (ι → ℝ) :=
  ENNReal.ofReal x • P.map fun ω ↦ x⁻¹ • X ω

instance [IsFiniteMeasure P] (x : ℝ) : IsFiniteMeasure (scaledLaw P X x) :=
  ⟨by
    rw [scaledLaw, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

lemma scaledLaw_apply (hX : Measurable X) (x : ℝ) {A : Set (ι → ℝ)} (hA : MeasurableSet A) :
    scaledLaw P X x A = ENNReal.ofReal x * P {ω | x⁻¹ • X ω ∈ A} := by
  have hXs : Measurable fun ω ↦ x⁻¹ • X ω := hX.const_smul x⁻¹
  rw [scaledLaw, Measure.smul_apply, Measure.map_apply hXs hA, smul_eq_mul]
  rfl

lemma scaledLaw_real_preimage (hX : Measurable X) {x : ℝ} (hx : 0 ≤ x) {A : Set (ι → ℝ≥0∞)}
    (hA : MeasurableSet A) :
    (scaledLaw P X x).real (ofRealVec ⁻¹' A) = x * P.real {ω | ofRealVec (x⁻¹ • X ω) ∈ A} := by
  rw [measureReal_def, scaledLaw_apply hX x (measurable_ofRealVec hA), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hx]
  rfl

lemma scaledLaw_compl_posOrthant (hX : Measurable X) (h : IsSimpleMaxStable (P.map X)) {x : ℝ}
    (hx : 0 < x) : scaledLaw P X x posOrthantᶜ = 0 := by
  rw [scaledLaw_apply hX x measurableSet_posOrthant.compl]
  have hpos := ae_of_ae_map hX.aemeasurable h.ae_forall_pos
  have : P {ω | x⁻¹ • X ω ∈ posOrthantᶜ} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hpos] with ω hω
    simp only [mem_ofPred_eq, mem_compl_iff, posOrthant, Pi.smul_apply, smul_eq_mul, not_not]
    exact fun i ↦ mul_nonneg (inv_nonneg.2 hx.le) (hω i).le
  rw [this, mul_zero]

variable [IsProbabilityMeasure P] (hX : Measurable X) (hS : HasSpectralMeasure (P.map X) H)
include hX hS

/-- **The scaled laws converge on lower-orthant complements**:
`x P(∃ i, X i / x > d i) → ν_H {x | ∃ i, x i > d i}`. -/
theorem tendsto_scaledLaw_exceedSet [IsFiniteMeasure H] (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
    {d : ι → ℝ≥0∞} (hd0 : ∀ i, d i ≠ 0) :
    Tendsto (fun x ↦ ((scaledLaw P X x).map ofRealVec).real (exceedSet d)) atTop
      (𝓝 ((spectralExponentMeasure H).real (exceedSet d))) := by
  rw [measureReal_def, spectralExponentMeasure_exceedSet hd0]
  refine (tendsto_mul_one_sub_exp ENNReal.toReal_nonneg).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [map_measureReal_apply measurable_ofRealVec (measurableSet_exceedSet d),
    scaledLaw_real_preimage hX hx.le (measurableSet_exceedSet d),
    measureReal_exceedSet hX hS hH hx hd0]

end Exponent

/-! ### Open sets are exhausted by rational boxes -/

section Geometry

/-- The box with rational lower corner `p.1` and upper corner `p.2` (lower coordinates `≤ 0` are
unconstrained), intersected with `{x | ∃ i, δ i < x i}`. -/
noncomputable def ratBox (δ : ι → ℝ≥0∞) (p : (ι → ℚ) × (ι → ℚ)) : Set (ι → ℝ≥0∞) :=
  boxSet δ (fun i ↦ ENNReal.ofReal (p.1 i)) (fun i ↦ ENNReal.ofReal (p.2 i))

variable [Fintype ι]

/-- Every point of an open set `G` in the nonnegative orthant lies in a rational box whose trace on
the orthant is contained in `G`. -/
lemma exists_ratBox {G : Set (ι → ℝ)} (hG : IsOpen G) (δ : ι → ℝ≥0∞) {y : ι → ℝ} (hyG : y ∈ G)
    (hyQ : y ∈ posOrthant) (hyO : ofRealVec y ∈ exceedSet δ) :
    ∃ p : (ι → ℚ) × (ι → ℚ), (∀ i, 0 < (p.2 i : ℝ)) ∧ ofRealVec y ∈ ratBox δ p ∧
      ∀ z ∈ posOrthant, ofRealVec z ∈ ratBox δ p → z ∈ G := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hG y hyG
  choose q₁ hq₁ using fun i ↦ exists_rat_btwn (show y i - ε / 2 < y i by linarith)
  choose q₂ hq₂ using fun i ↦ exists_rat_btwn (show y i < y i + ε / 2 by linarith)
  have hq₂pos : ∀ i, 0 < (q₂ i : ℝ) := fun i ↦ (hyQ i).trans_lt (hq₂ i).1
  refine ⟨(q₁, q₂), hq₂pos, ⟨⟨fun i hi ↦ ?_, fun i ↦ ?_⟩, hyO⟩, ?_⟩
  · have hq : 0 < (q₁ i : ℝ) := ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 hi)
    exact (ENNReal.ofReal_lt_ofReal_iff (hq.trans (hq₁ i).2)).2 (hq₁ i).2
  · exact ENNReal.ofReal_le_ofReal (hq₂ i).1.le
  · rintro z hzQ ⟨⟨hzU, hzL⟩, -⟩
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, abs_lt]
    have hup : z i ≤ q₂ i := (ENNReal.ofReal_le_ofReal_iff (hq₂pos i).le).1 (hzL i)
    have hlow : (q₁ i : ℝ) ≤ z i := by
      by_cases hq : 0 < (q₁ i : ℝ)
      · exact (ENNReal.ofReal_lt_ofReal_iff'.1 (hzU i (ENNReal.ofReal_pos.2 hq).ne')).1.le
      · exact (not_lt.1 hq).trans (hzQ i)
    constructor <;> linarith [(hq₁ i).1, (hq₂ i).2]

end Geometry

/-! ### Weak convergence of the scaled laws -/

section Weak

variable [Fintype ι] {H : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure H]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ι → ℝ}

/-- `b⁻¹ a = (a / b)` as a real ratio, for `a ≤ b < ∞`. -/
lemma inv_mul_eq_ofReal_div {a b : ℝ≥0∞} (hab : a ≤ b) (hb : b ≠ ∞) :
    b⁻¹ * a = ENNReal.ofReal (a.toReal / b.toReal) := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [nonpos_iff_eq_zero.1 hab]
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hb0 hb),
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top hb hab), ENNReal.ofReal_toReal hb, div_eq_mul_inv,
    mul_comm]

variable (hX : Measurable X) (hS : HasSpectralMeasure (P.map X) H)
  (h : IsSimpleMaxStable (P.map X)) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
include hX hS h hH

/-- **The liminf condition on open sets** for the scaled laws conditioned on
`O = {x | ∃ i, δ i < x i}`: `ν_H(G | O) ≤ liminf_x P(X / x ∈ G | X / x ∈ O)`. -/
theorem le_liminf_cond_scaledLaw {δ : ι → ℝ≥0∞} (hδ : ∀ i, δ i ≠ 0) {G : Set (ι → ℝ)}
    (hG : IsOpen G) :
    (spectralExponentMeasureReal H (ofRealVec ⁻¹' exceedSet δ))⁻¹ *
        spectralExponentMeasureReal H (ofRealVec ⁻¹' exceedSet δ ∩ G) ≤
      liminf (fun x ↦ (scaledLaw P X x (ofRealVec ⁻¹' exceedSet δ))⁻¹ *
        scaledLaw P X x (ofRealVec ⁻¹' exceedSet δ ∩ G)) atTop := by
  have hle := ae_le_one_of_ae_iSup_eq_one hH
  have hnt := ae_ne_top_of_ae_le_one hle
  set ν := spectralExponentMeasure H with hν
  set νE := spectralExponentMeasureReal H with hνE
  set O := ofRealVec ⁻¹' exceedSet δ with hO
  have hνfin : ∀ d : ι → ℝ≥0∞, (∀ i, d i ≠ 0) → ν (exceedSet d) ≠ ∞ :=
    fun d hd ↦ spectralExponentMeasure_exceedSet_ne_top hle hd
  have hνEO : νE O ≠ ∞ := by
    rw [hO, spectralExponentMeasureReal_preimage hnt (measurableSet_exceedSet δ)]
    exact hνfin δ hδ
  rcases eq_or_ne (νE O) 0 with h0 | hνEO0'
  · rw [measure_mono_null inter_subset_left h0, mul_zero]
    exact zero_le
  have hνEO0 : νE.real O ≠ 0 := (ENNReal.toReal_pos hνEO0' hνEO).ne'
  -- the countable family of rational boxes inside `G`
  set T : Set ((ι → ℚ) × (ι → ℚ)) := {p | (∀ i, 0 < (p.2 i : ℝ)) ∧
    ∀ z ∈ posOrthant, ofRealVec z ∈ ratBox δ p → z ∈ G} with hT
  have hcover : ∀ y ∈ O ∩ G, y ∈ posOrthant → ∃ p ∈ T, ofRealVec y ∈ ratBox δ p := by
    rintro y ⟨hyO, hyG⟩ hyQ
    obtain ⟨p, hp, hyp, hpG⟩ := exists_ratBox hG δ hyG hyQ hyO
    exact ⟨p, ⟨hp, hpG⟩, hyp⟩
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · have : νE (O ∩ G) = 0 := by
      refine measure_mono_null (t := posOrthantᶜ) ?_ spectralExponentMeasureReal_compl_posOrthant
      intro y hy hyQ
      obtain ⟨p, hp, -⟩ := hcover y hy hyQ
      rw [hTe] at hp
      exact hp
    rw [this, mul_zero]
    exact zero_le
  obtain ⟨e, he⟩ := (Set.to_countable T).exists_eq_range hTne
  have heT : ∀ k, e k ∈ T := fun k ↦ he ▸ mem_range_self k
  set s : ℕ → (ι → ℝ≥0∞) × (ι → ℝ≥0∞) :=
    fun k ↦ (fun i ↦ ENNReal.ofReal ((e k).1 i), fun i ↦ ENNReal.ofReal ((e k).2 i)) with hs_def
  have hs : ∀ k i, (s k).2 i ≠ 0 := fun k i ↦ (ENNReal.ofReal_pos.2 ((heT k).1 i)).ne'
  set F : ℕ → Set (ι → ℝ≥0∞) := fun n ↦ ⋃ k ∈ Finset.range n, boxSet δ (s k).1 (s k).2
    with hF
  have hFm : ∀ n, MeasurableSet (F n) := fun n ↦
    Finset.measurableSet_biUnion _ fun k _ ↦ measurableSet_boxSet _ _ _
  set FE : ℕ → Set (ι → ℝ) := fun n ↦ ofRealVec ⁻¹' F n with hFE
  have hFEm : ∀ n, MeasurableSet (FE n) := fun n ↦ measurable_ofRealVec (hFm n)
  have hFE_O : ∀ n, FE n ⊆ O := fun n y hy ↦ by
    simp only [hFE, hF, mem_preimage, mem_iUnion] at hy
    obtain ⟨k, -, hk⟩ := hy
    exact hk.2
  have hFE_G : ∀ n, FE n ∩ posOrthant ⊆ O ∩ G := fun n y ⟨hy, hyQ⟩ ↦ by
    refine ⟨hFE_O n hy, ?_⟩
    simp only [hFE, hF, mem_preimage, mem_iUnion] at hy
    obtain ⟨k, -, hk⟩ := hy
    exact (heT k).2 y hyQ hk
  have hmono : Monotone fun n ↦ FE n ∩ posOrthant := by
    intro m n hmn y ⟨hy, hyQ⟩
    refine ⟨?_, hyQ⟩
    simp only [hFE, hF, mem_preimage, mem_iUnion, Finset.mem_range] at hy ⊢
    obtain ⟨k, hk, hk'⟩ := hy
    exact ⟨k, hk.trans_le hmn, hk'⟩
  have hunion : ⋃ n, FE n ∩ posOrthant = O ∩ G ∩ posOrthant := by
    refine subset_antisymm (iUnion_subset fun n ↦ subset_inter (hFE_G n) inter_subset_right) ?_
    rintro y ⟨hy, hyQ⟩
    obtain ⟨p, hp, hyp⟩ := hcover y hy hyQ
    obtain ⟨k, rfl⟩ := he ▸ hp
    refine mem_iUnion.2 ⟨k + 1, ?_, hyQ⟩
    simp only [hFE, hF, mem_preimage, mem_iUnion]
    exact ⟨k, Finset.mem_range.2 k.lt_succ_self, hyp⟩
  have hνsup : νE (O ∩ G) = ⨆ n, νE (FE n) := by
    rw [← measure_inter_conull (t := posOrthant) (by
      simpa using spectralExponentMeasureReal_compl_posOrthant (H := H)), ← hunion,
      hmono.measure_iUnion]
    exact iSup_congr fun n ↦ measure_inter_conull (by
      simpa using spectralExponentMeasureReal_compl_posOrthant (H := H))
  rw [hνsup, ENNReal.mul_iSup]
  refine iSup_le fun n ↦ ?_
  -- convergence of the conditional mass of `FE n`
  set μs : ℝ → Measure (ι → ℝ≥0∞) := fun x ↦ (scaledLaw P X x).map ofRealVec with hμs
  have hμsfin : ∀ x (d : ι → ℝ≥0∞), (∀ i, d i ≠ 0) → μs x (exceedSet d) ≠ ∞ :=
    fun x d _ ↦ measure_ne_top _ _
  have hconv := fun d hd ↦ tendsto_scaledLaw_exceedSet hX hS hH (d := d) hd
  have hR1 : Tendsto (fun x ↦ (scaledLaw P X x).real (FE n)) atTop (𝓝 (νE.real (FE n))) := by
    have hlim : νE.real (FE n) = ν.real (F n) := by
      rw [measureReal_def, measureReal_def, hFE, spectralExponentMeasureReal_preimage hnt (hFm n)]
    rw [hlim]
    refine (tendsto_measureReal_iUnion_boxSet (μs := μs) hμsfin hνfin hconv hδ s hs n).congr
      fun x ↦ ?_
    simp only [hμs]
    exact map_measureReal_apply measurable_ofRealVec (hFm n)
  have hR2 : Tendsto (fun x ↦ (scaledLaw P X x).real O) atTop (𝓝 (νE.real O)) := by
    have hlim : νE.real O = ν.real (exceedSet δ) := by
      rw [measureReal_def, measureReal_def, hO,
        spectralExponentMeasureReal_preimage hnt (measurableSet_exceedSet δ)]
    rw [hlim]
    refine (hconv δ hδ).congr fun x ↦ ?_
    exact map_measureReal_apply measurable_ofRealVec (measurableSet_exceedSet δ)

  have htend : Tendsto (fun x ↦ (scaledLaw P X x O)⁻¹ * scaledLaw P X x (FE n)) atTop
      (𝓝 ((νE O)⁻¹ * νE (FE n))) := by
    rw [inv_mul_eq_ofReal_div (measure_mono (hFE_O n)) hνEO]
    refine (ENNReal.tendsto_ofReal (hR1.div hR2 hνEO0)).congr fun x ↦ ?_
    rw [inv_mul_eq_ofReal_div (measure_mono (hFE_O n)) (measure_ne_top _ _)]
    rfl
  rw [← htend.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  calc scaledLaw P X x (FE n) = scaledLaw P X x (FE n ∩ posOrthant) :=
        (measure_inter_conull (by simpa using scaledLaw_compl_posOrthant hX h hx)).symm
    _ ≤ _ := measure_mono (hFE_G n)

end Weak

/-! ### Convergence of integrals -/

section Integrals

variable [Fintype ι] {H : Measure (ι → ℝ≥0∞)}

/-- `∫ f dm = m(O) ∫ f dm[|O]` when `m` lives on the orthant and `f` vanishes on the orthant
outside `O`. -/
lemma integral_eq_measureReal_mul_integral_cond {m : Measure (ι → ℝ)} {O : Set (ι → ℝ)}
    (hO : MeasurableSet O) (hOfin : m O ≠ ∞) (hm : m posOrthantᶜ = 0) {f : (ι → ℝ) → ℝ}
    (hf : ∀ y ∈ posOrthant, y ∉ O → f y = 0) :
    ∫ y, f y ∂m = m.real O * ∫ y, f y ∂m[|O] := by
  have hae : ∀ᵐ y ∂m, y ∈ posOrthant :=
    (measure_eq_zero_iff_ae_notMem.1 hm).mono fun y hy ↦ not_not.1 hy
  have h1 : ∫ y in O, f y ∂m = ∫ y, f y ∂m :=
    setIntegral_eq_integral_of_ae_compl_eq_zero (hae.mono fun y hy hyO ↦ hf y hy hyO)
  rw [← h1, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.toReal_inv]
  rcases eq_or_ne (m O) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  · rw [measureReal_def, mul_inv_cancel₀ (ENNReal.toReal_pos h0 hOfin).ne', one_mul]

/-- The exponent measure of `{x | ∃ i, c < x i}` is `H(univ) / c` for `H` on the sphere. -/
lemma spectralExponentMeasure_exceedSet_const [Countable ι] [SFinite H]
    (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) {c : ℝ≥0∞} (hc0 : c ≠ 0) :
    spectralExponentMeasure H (exceedSet fun _ ↦ c) = c⁻¹ * H univ := by
  rw [spectralExponentMeasure_exceedSet fun _ ↦ hc0, ← lintegral_const]
  exact lintegral_congr_ae (hH.mono fun w hw ↦ by dsimp only; rw [← ENNReal.iSup_div, hw, one_div])

lemma measure_univ_ne_zero_of_hasSpectralMeasure [Nonempty ι] {μ : Measure (ι → ℝ)}
    (h : IsSimpleMaxStable μ) (hS : HasSpectralMeasure μ H) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1) :
    H univ ≠ 0 := by
  intro h0
  have := hS.measure_univ_toReal hH
  rw [h0, ENNReal.toReal_zero] at this
  linarith [h.one_le_extremalCoefficient]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ι → ℝ} [IsFiniteMeasure H]
  (hX : Measurable X) (hS : HasSpectralMeasure (P.map X) H)
  (h : IsSimpleMaxStable (P.map X)) (hH : ∀ᵐ w ∂H, ⨆ i, w i = 1)
include hX hS h hH

/-- **Vague convergence of the scaled laws to the exponent measure**: `∫ f d(x P(X / x ∈ ·)) →
∫ f dν_H` for every bounded continuous `f` vanishing near the origin. -/
theorem tendsto_integral_scaledLaw [Nonempty ι] {f : (ι → ℝ) →ᵇ ℝ} (hf : VanishesNearZero f) :
    Tendsto (fun x ↦ ∫ y, f y ∂scaledLaw P X x) atTop
      (𝓝 (∫ y, f y ∂spectralExponentMeasureReal H)) := by
  have hle := ae_le_one_of_ae_iSup_eq_one hH
  have hnt := ae_ne_top_of_ae_le_one hle
  obtain ⟨r, hr, hfr⟩ := hf
  set δ : ι → ℝ≥0∞ := fun _ ↦ ENNReal.ofReal (r / 2) with hδdef
  have hδ0 : ENNReal.ofReal (r / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (half_pos hr)).ne'
  have hδ : ∀ i, δ i ≠ 0 := fun _ ↦ hδ0
  set O := ofRealVec ⁻¹' exceedSet δ with hO
  have hOm : MeasurableSet O := measurable_ofRealVec (measurableSet_exceedSet δ)
  set νE := spectralExponentMeasureReal H with hνE
  have hνEOeq : νE O = spectralExponentMeasure H (exceedSet δ) :=
    spectralExponentMeasureReal_preimage hnt (measurableSet_exceedSet δ)
  have hνEO : νE O ≠ ∞ := hνEOeq ▸ spectralExponentMeasure_exceedSet_ne_top hle hδ
  have hνEO0 : νE O ≠ 0 := by
    rw [hνEOeq, spectralExponentMeasure_exceedSet_const hH hδ0]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
      (measure_univ_ne_zero_of_hasSpectralMeasure h hS hH)
  have hf0 : ∀ y ∈ posOrthant, y ∉ O → f y = 0 := by
    intro y hyQ hyO
    refine hfr y ?_
    have hy : ∀ i, y i ≤ r / 2 := fun i ↦ by
      by_contra hc
      exact hyO ⟨i, (ENNReal.ofReal_lt_ofReal_iff (by linarith [not_le.1 hc])).2 (not_le.1 hc)⟩
    calc ‖y‖ ≤ r / 2 := (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hyQ i)]; exact hy i
      _ < r := half_lt_self hr
  -- the masses of `O`
  have hR2 : Tendsto (fun x ↦ (scaledLaw P X x).real O) atTop (𝓝 (νE.real O)) := by
    have hlim : νE.real O = (spectralExponentMeasure H).real (exceedSet δ) := by
      rw [measureReal_def, measureReal_def, hνEOeq]
    rw [hlim]
    refine (tendsto_scaledLaw_exceedSet hX hS hH hδ).congr fun x ↦ ?_
    exact map_measureReal_apply measurable_ofRealVec (measurableSet_exceedSet δ)
  have hev : ∀ᶠ x in atTop, scaledLaw P X x O ≠ 0 := by
    filter_upwards [hR2.eventually (lt_mem_nhds (ENNReal.toReal_pos hνEO0 hνEO))] with x hx
    exact fun h0 ↦ by simp [measureReal_def, h0] at hx
  -- weak convergence of the conditional laws
  let PM : ℝ → ProbabilityMeasure (ι → ℝ) := fun x ↦
    if hx : scaledLaw P X x O ≠ 0 then ⟨(scaledLaw P X x)[|O], cond_isProbabilityMeasure hx⟩
    else ⟨Measure.dirac 0, inferInstance⟩
  let PMlim : ProbabilityMeasure (ι → ℝ) :=
    ⟨νE[|O], cond_isProbabilityMeasure_of_finite hνEO0 hνEO⟩
  have hPMeq : ∀ᶠ x in atTop, (PM x : Measure (ι → ℝ)) = (scaledLaw P X x)[|O] :=
    hev.mono fun x hx ↦ by simp [PM, hx]
  have hT : Tendsto PM atTop (𝓝 PMlim) := by
    refine tendsto_of_forall_isOpen_le_liminf' fun G hG ↦ ?_
    have key := le_liminf_cond_scaledLaw hX hS h hH hδ hG
    have e1 : ((PMlim : ProbabilityMeasure (ι → ℝ)) : Measure (ι → ℝ)) G =
        (νE O)⁻¹ * νE (O ∩ G) := cond_apply hOm _ G
    rw [e1]
    refine key.trans (le_of_eq (liminf_congr ?_))
    filter_upwards [hPMeq] with x hx
    rw [hx, cond_apply hOm]
  have hI := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT f
  rw [integral_eq_measureReal_mul_integral_cond hOm hνEO
    spectralExponentMeasureReal_compl_posOrthant hf0]
  have hI' : Tendsto (fun x ↦ ∫ y, f y ∂(scaledLaw P X x)[|O]) atTop
      (𝓝 (∫ y, f y ∂νE[|O])) := by
    refine hI.congr' ?_
    filter_upwards [hPMeq] with x hx
    rw [hx]
  refine (hR2.mul hI').congr' ?_
  · filter_upwards
 [eventually_gt_atTop 0] with x hx
    exact (integral_eq_measureReal_mul_integral_cond hOm (measure_ne_top _ _)
      (scaledLaw_compl_posOrthant hX h hx) hf0).symm

end Integrals

end ExtremeValueTheory
