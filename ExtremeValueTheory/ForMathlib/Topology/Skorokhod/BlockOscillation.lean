/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Modulus
public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Measurable

/-!
# Block oscillation of functions on the unit interval

For `x : I → E` and `m > 0` the *block oscillation*
`blockOscillation x m = max_{i < m} sup_{u ∈ [i/m, (i+1)/m]} edist (x u) (x (i/m))`
is the largest deviation of `x` on a block of the grid of mesh `1/m` from its value at the left
end of the block. It controls both conditions of the tightness criterion in the Skorokhod space
([Billingsley, *Convergence of Probability Measures*, Theorem 13.2][billingsley1999]):

* the càdlàg modulus: `w'_x(δ) ≤ 2 · blockOscillation x m` for `δ < 1/m`
  (`cadlagModulus_le_two_mul_blockOscillation`), using the grid as a `δ`-sparse partition;
* the sup norm: `edist (x t) (x 0) ≤ m · blockOscillation x m`
  (`edist_apply_le_mul_blockOscillation`).

Unlike the càdlàg modulus, the block oscillation is a Borel function on `D([0, 1], E)`
(`SkorokhodSpace.measurable_blockOscillation`): by right-continuity the supremum over a block can
be taken over its rational points and its right end.

## Main definitions

* `unitInterval.gridPt m i`: the grid point `i / m` of `I`.
* `blockOscillation x m`: the block oscillation.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

@[expose] public section

open Filter Set Topology unitInterval
open scoped ENNReal

/-- The grid point `i / m` of the unit interval. -/
noncomputable def unitInterval.gridPt (m i : ℕ) : I := Set.projIcc 0 1 zero_le_one ((i : ℝ) / m)

lemma unitInterval.coe_gridPt {m i : ℕ} (hi : i ≤ m) : (gridPt m i : ℝ) = i / m := by
  unfold gridPt
  rw [Set.projIcc_of_mem _ ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    div_le_one_of_le₀ (by exact_mod_cast hi) (Nat.cast_nonneg _)⟩]

lemma unitInterval.gridPt_zero (m : ℕ) : gridPt m 0 = 0 := by
  ext; rw [coe_gridPt (Nat.zero_le _)]; simp

lemma unitInterval.gridPt_self {m : ℕ} (hm : 0 < m) : gridPt m m = 1 := by
  ext; rw [coe_gridPt le_rfl]; simp [(Nat.cast_pos.2 hm).ne']

variable {E : Type*}

section PseudoEMetricSpace

variable [PseudoEMetricSpace E]

/-- The block oscillation: the largest deviation of `x` on a block `[i/m, (i+1)/m]` from its
value at the left end. -/
noncomputable def blockOscillation (x : I → E) (m : ℕ) : ℝ≥0∞ :=
  ⨆ (i : ℕ) (_ : i < m) (u : I) (_ : (i : ℝ) / m ≤ u ∧ (u : ℝ) ≤ (i + 1) / m),
    edist (x u) (x (unitInterval.gridPt m i))

lemma le_blockOscillation (x : I → E) {m i : ℕ} (hi : i < m) {u : I} (hu₁ : (i : ℝ) / m ≤ u)
    (hu₂ : (u : ℝ) ≤ (i + 1) / m) :
    edist (x u) (x (gridPt m i)) ≤ blockOscillation x m := by
  unfold blockOscillation
  exact le_iSup_of_le i (le_iSup_of_le hi (le_iSup_of_le u (le_iSup_of_le ⟨hu₁, hu₂⟩ le_rfl)))

lemma edist_gridPt_le_mul_blockOscillation (x : I → E) {m : ℕ} :
    ∀ j ≤ m, edist (x (gridPt m j)) (x 0) ≤ j * blockOscillation x m := by
  intro j
  induction j with
  | zero => intro _; simp [gridPt_zero]
  | succ j ih =>
    intro hj
    have hstep : edist (x (gridPt m (j + 1))) (x (gridPt m j)) ≤ blockOscillation x m := by
      refine le_blockOscillation x (by omega) ?_ ?_
      · rw [coe_gridPt hj]
        exact div_le_div_of_nonneg_right (by push_cast; linarith) (Nat.cast_nonneg _)
      · rw [coe_gridPt hj]; push_cast; rfl
    calc edist (x (gridPt m (j + 1))) (x 0)
        ≤ edist (x (gridPt m (j + 1))) (x (gridPt m j)) + edist (x (gridPt m j)) (x 0) :=
          edist_triangle _ _ _
      _ ≤ blockOscillation x m + j * blockOscillation x m := add_le_add hstep (ih (by omega))
      _ = ((j + 1 : ℕ) : ℝ≥0∞) * blockOscillation x m := by push_cast; ring

/-- Every point of `I` lies in a block `[i/m, (i+1)/m]` with `i < m`. -/
lemma exists_block {m : ℕ} (hm : 0 < m) (t : I) :
    ∃ i < m, (i : ℝ) / m ≤ t ∧ (t : ℝ) ≤ (i + 1) / m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  rcases lt_or_ge (⌊(m : ℝ) * t⌋₊) m with h | h
  · refine ⟨_, h, ?_, ?_⟩
    · rw [div_le_iff₀ hm', mul_comm]
      exact Nat.floor_le (by have := t.2.1; positivity)
    · rw [le_div_iff₀ hm', mul_comm]
      exact (Nat.lt_floor_add_one _).le
  · have ht : (t : ℝ) = 1 := by
      refine le_antisymm t.2.2 ?_
      by_contra h'
      push Not at h'
      have : (m : ℝ) * t < m := by nlinarith
      exact (not_lt.2 h) ((Nat.floor_lt (by have := t.2.1; positivity)).2 this)
    refine ⟨m - 1, by omega, ?_, ?_⟩
    · rw [ht, div_le_one hm']
      exact_mod_cast Nat.sub_le m 1
    · rw [ht, le_div_iff₀ hm', one_mul]
      have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]

/-- The deviation of `x` from its initial value is at most `m` times the block oscillation. -/
theorem edist_apply_le_mul_blockOscillation (x : I → E) {m : ℕ} (hm : 0 < m) (t : I) :
    edist (x t) (x 0) ≤ m * blockOscillation x m := by
  obtain ⟨i, hi, h₁, h₂⟩ := exists_block hm t
  calc edist (x t) (x 0) ≤ edist (x t) (x (gridPt m i)) + edist (x (gridPt m i)) (x 0) :=
        edist_triangle _ _ _
    _ ≤ blockOscillation x m + i * blockOscillation x m :=
        add_le_add (le_blockOscillation x hi h₁ h₂)
          (edist_gridPt_le_mul_blockOscillation x i hi.le)
    _ = ((i + 1 : ℕ) : ℝ≥0∞) * blockOscillation x m := by push_cast; ring
    _ ≤ m * blockOscillation x m := by gcongr; exact_mod_cast hi

/-- The càdlàg modulus is at most twice the block oscillation, for `δ` below the mesh. -/
theorem cadlagModulus_le_two_mul_blockOscillation (x : I → E) {m : ℕ} (hm : 0 < m) {δ : ℝ}
    (hδ : δ < 1 / m) : cadlagModulus x δ ≤ 2 * blockOscillation x m := by
  classical
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set R : Finset I := (Finset.range (m + 1)).image (gridPt m) with hR
  have hmemR {j : ℕ} (hj : j ≤ m) : gridPt m j ∈ R :=
    Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))
  have hsparse : IsSparsePartition δ R := by
    refine ⟨gridPt_zero m ▸ hmemR (Nat.zero_le _), gridPt_self hm ▸ hmemR le_rfl, ?_⟩
    intro r hr r' hr' hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hr'
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hij : i ≠ j := fun h ↦ hne (h ▸ rfl)
    rw [Subtype.dist_eq, coe_gridPt hi', coe_gridPt hj', Real.dist_eq, ← sub_div, abs_div,
      abs_of_pos hm']
    refine hδ.trans_le (div_le_div_of_nonneg_right ?_ hm'.le)
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  refine (iInf₂_le R hsparse).trans ?_
  unfold cellOscillation
  refine iSup₂_le fun s t ↦ iSup₂_le fun hst h ↦ ?_
  rcases eq_or_lt_of_le s.2.2 with hs | hs
  · have hst' : s = t := le_antisymm hst (by
      rw [← Subtype.coe_le_coe, hs]; exact t.2.2)
    rw [hst', edist_self]; exact bot_le
  set i := ⌊(m : ℝ) * s⌋₊ with hi
  have him : i < m := (Nat.floor_lt (by have := s.2.1; positivity)).2 (by nlinarith)
  have h₁ : (i : ℝ) / m ≤ s := by
    rw [div_le_iff₀ hm', mul_comm]; exact Nat.floor_le (by have := s.2.1; positivity)
  have h₂ : (s : ℝ) < (i + 1) / m := by
    rw [lt_div_iff₀ hm', mul_comm]; exact Nat.lt_floor_add_one _
  have hg : (gridPt m (i + 1) : ℝ) = (i + 1) / m := by rw [coe_gridPt him]; push_cast; rfl
  have ht : (t : ℝ) < (i + 1) / m := by
    rcases h _ (hmemR him) with h' | h'
    · exact absurd (Subtype.coe_le_coe.2 h') (by rw [hg]; exact not_le.2 h₂)
    · rw [← hg]; exact h'
  have ht₁ : (i : ℝ) / m ≤ t := h₁.trans (Subtype.coe_le_coe.2 hst)
  calc edist (x s) (x t) ≤ edist (x s) (x (gridPt m i)) + edist (x (gridPt m i)) (x t) :=
        edist_triangle _ _ _
    _ ≤ blockOscillation x m + blockOscillation x m := by
        rw [edist_comm (x (gridPt m i))]
        exact add_le_add (le_blockOscillation x him h₁ h₂.le)
          (le_blockOscillation x him ht₁ ht.le)
    _ = 2 * blockOscillation x m := (two_mul _).symm

end PseudoEMetricSpace

namespace SkorokhodSpace

variable [PseudoEMetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The block oscillation is a Borel function on the Skorokhod space. -/
theorem measurable_blockOscillation (m : ℕ) :
    Measurable fun x : SkorokhodSpace E ↦ blockOscillation (⇑x) m := by
  set D : Set I := {u : I | ∃ q : ℚ, (u : ℝ) = q} ∪ range (gridPt m) with hD
  have hDc : D.Countable := by
    refine Countable.union ?_ (countable_range _)
    have : {u : I | ∃ q : ℚ, (u : ℝ) = q} = Subtype.val ⁻¹' range ((↑) : ℚ → ℝ) := by
      ext u; simp [eq_comm]
    rw [this]
    exact (countable_range _).preimage Subtype.val_injective
  have : Countable D := hDc.to_subtype
  set F : SkorokhodSpace E → ℝ≥0∞ := fun x ↦ ⨆ (i : ℕ) (_ : i < m) (u : D)
    (_ : (i : ℝ) / m ≤ (u : I) ∧ ((u : I) : ℝ) ≤ (i + 1) / m),
    edist (x u) (x (gridPt m i)) with hF
  have hFm : Measurable F :=
    Measurable.iSup fun i ↦ Measurable.iSup fun _ ↦ Measurable.iSup fun u ↦
      Measurable.iSup fun _ ↦ (measurable_apply (u : I)).edist (measurable_apply _)
  convert hFm using 1
  ext x
  refine le_antisymm (iSup₂_le fun i hi ↦ iSup₂_le fun u hu ↦ ?_) (iSup₂_le fun i hi ↦
    iSup₂_le fun u hu ↦ le_blockOscillation x hi hu.1 hu.2)
  have hle : ∀ v : I, v ∈ D → (i : ℝ) / m ≤ v → (v : ℝ) ≤ (i + 1) / m →
      edist (x v) (x (gridPt m i)) ≤ F x := fun v hv h₁ h₂ ↦
    le_iSup_of_le i (le_iSup_of_le hi (le_iSup_of_le ⟨v, hv⟩ (le_iSup_of_le ⟨h₁, h₂⟩ le_rfl)))
  by_cases huD : u ∈ D
  · exact hle u huD hu.1 hu.2
  -- `u` is not the right end, so it is approached from the right by rational points of the block
  have hb : (gridPt m (i + 1) : ℝ) = (i + 1) / m := by rw [coe_gridPt hi]; push_cast; rfl
  have hub : (u : ℝ) < (i + 1) / m := by
    refine lt_of_le_of_ne hu.2 fun h ↦ huD (Or.inr ⟨i + 1, ?_⟩)
    ext; rw [hb, h]
  have hq (k : ℕ) : ∃ q : ℚ, (u : ℝ) < q ∧ (q : ℝ) < min ((u : ℝ) + 1 / (k + 1)) ((i + 1) / m) :=
    exists_rat_btwn (lt_min (by have : (0 : ℝ) < 1 / (k + 1) := by positivity
                                linarith) hub)
  choose q hq₁ hq₂ using hq
  have hqI (k : ℕ) : (q k : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨u.2.1.trans (hq₁ k).le, ((hq₂ k).trans_le (min_le_right _ _)).le.trans (by
      rw [div_le_one (Nat.cast_pos.2 (Nat.zero_lt_of_lt hi))]; exact_mod_cast hi)⟩
  set v : ℕ → I := fun k ↦ ⟨q k, hqI k⟩ with hv
  have hvlim : Tendsto v atTop (𝓝[>] u) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ (hq₁ k)⟩
    rw [tendsto_subtype_rng]
    have hup : Tendsto (fun k : ℕ ↦ (u : ℝ) + 1 / ((k : ℝ) + 1)) atTop (𝓝 (u : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (u : ℝ))).add
        tendsto_one_div_add_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k ↦ (hq₁ k).le) fun k ↦ ((hq₂ k).trans_le (min_le_left _ _)).le
  have hlim : Tendsto (fun k ↦ edist (x (v k)) (x (gridPt m i))) atTop
      (𝓝 (edist (x u) (x (gridPt m i)))) :=
    ((x.isRightContinuous u).tendsto.comp hvlim).edist tendsto_const_nhds
  refine le_of_tendsto' hlim fun k ↦ hle (v k) (Or.inl ⟨q k, rfl⟩)
    (hu.1.trans (hq₁ k).le) ((hq₂ k).trans_le (min_le_right _ _)).le

end SkorokhodSpace
