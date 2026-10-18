/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Modulus

/-!
# Compact sets of the Skorokhod space have uniformly small càdlàg modulus

We prove the necessity half of the Arzelà–Ascoli theorem for `D([0, 1], E)`
([Billingsley, *Convergence of Probability Measures*, Theorem 12.3][billingsley1999]): on a
compact set `K` of càdlàg functions the values lie in a totally bounded set and the càdlàg
modulus `w'_x(δ)` tends to `0` as `δ → 0` uniformly in `x ∈ K`.

The ingredients are Billingsley's (12.7), `w'_x(δ) → 0` for a single càdlàg `x`
(from Billingsley's Lemma 12.1, `IsCadlag.exists_finset_edist_lt`), and a perturbation bound:
if `x` and `y` are within `ρ` in the Skorokhod `J₁` metric, then
`w'_y(δ - 2ρ) ≤ w'_x(δ) + 2ρ`, the time change carrying a partition for `x` to one for `y`.

## Main statements

* `IsCadlag.exists_cadlagModulus_lt`: Billingsley (12.7).
* `cadlagModulus_le_of_timeChange`, `cadlagModulus_le_of_skorokhodEDist_lt`: the perturbation
  bound.
* `SkorokhodSpace.exists_forall_cadlagModulus_lt_of_isCompact`: uniform smallness of the càdlàg
  modulus on a compact set.
* `SkorokhodSpace.exists_totallyBounded_of_isCompact`: the values of the functions of a compact
  set lie in a totally bounded set.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

@[expose] public section

open Filter Set Topology Metric unitInterval
open scoped ENNReal

variable {E : Type*} [PseudoEMetricSpace E]

/-- For a finite set `R` of the unit interval there is `δ > 0` smaller than the distance between
any two distinct points of `R`. -/
lemma Finset.exists_pos_lt_dist (R : Finset I) :
    ∃ δ > (0 : ℝ), ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → δ < dist r r' := by
  classical
  set D : Finset ℝ := insert 1 (((R ×ˢ R).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ dist p.1 p.2)
  have hD : D.Nonempty := Finset.insert_nonempty _ _
  have hpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact one_pos
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hd
      exact dist_pos.2 (Finset.mem_filter.1 hp).2
  refine ⟨D.min' hD / 2, half_pos (hpos _ (D.min'_mem hD)), fun r hr r' hr' hne ↦ ?_⟩
  have hmem : dist r r' ∈ D := Finset.mem_insert_of_mem (Finset.mem_image.2
    ⟨(r, r'), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hr, hr'⟩, hne⟩, rfl⟩)
  have h1 := D.min'_le _ hmem
  have h2 := hpos _ (D.min'_mem hD)
  linarith

/-- **Billingsley (12.7).** The càdlàg modulus of a càdlàg function tends to zero:
for every `ε > 0` there is `δ > 0` with `w'_x(δ) < ε`. -/
theorem IsCadlag.exists_cadlagModulus_lt {x : I → E} (hx : IsCadlag x) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∃ δ > 0, cadlagModulus x δ < ε := by
  classical
  set ε₁ := min ε 1
  have hε₁ : 0 < ε₁ := lt_min hε one_pos
  have hε₁t : ε₁ ≠ ⊤ := (min_le_right _ _).trans_lt ENNReal.one_lt_top |>.ne
  have hε₂ : 0 < ε₁ / 2 := ENNReal.half_pos hε₁.ne'
  obtain ⟨s, hs⟩ := hx.exists_finset_edist_lt hε₂
  set R : Finset I := insert 0 (insert 1 s)
  obtain ⟨δ, hδ, hR⟩ := R.exists_pos_lt_dist
  refine ⟨δ, hδ, lt_of_le_of_lt ?_ ((ENNReal.half_lt_self hε₁.ne' hε₁t).trans_le
    (min_le_left _ _))⟩
  have hsp : IsSparsePartition δ R :=
    ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hR⟩
  refine (iInf₂_le R hsp).trans ?_
  unfold cellOscillation
  refine iSup₂_le fun u v ↦ iSup₂_le fun huv h ↦ (hs u v huv fun r hr ↦ ?_).le
  exact h r (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))

/-- **Perturbation of the càdlàg modulus.** If a time change `φ` within `ρ` of the identity
matches `x` with `y` up to `ρ` (`edist (x t) (y (φ t)) < ρ`), then
`w'_y(δ - 2ρ) ≤ w'_x(δ) + 2ρ`. -/
theorem cadlagModulus_le_of_timeChange {x y : I → E} (φ : I ≃o I) {ρ δ : ℝ}
    (hφ : ∀ t, dist (φ t) t < ρ) (hxy : ∀ t, edist (x t) (y (φ t)) < ENNReal.ofReal ρ) :
    cadlagModulus y (δ - 2 * ρ) ≤ cadlagModulus x δ + 2 * ENNReal.ofReal ρ := by
  classical
  unfold cadlagModulus
  rw [ENNReal.iInf_add]
  refine le_iInf fun R ↦ ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hR ↦ ?_
  have hsp : IsSparsePartition (δ - 2 * ρ) (R.image φ) := by
    refine ⟨Finset.mem_image.2 ⟨0, hR.1, φ.map_bot⟩, Finset.mem_image.2 ⟨1, hR.2.1, φ.map_top⟩,
      ?_⟩
    intro u hu u' hu' hne
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hu'
    have hrr : r ≠ r' := fun h ↦ hne (h ▸ rfl)
    have h1 := hR.2.2 r hr r' hr' hrr
    have h2 := dist_triangle4 r (φ r) (φ r') r'
    have h3 := hφ r
    have h4 := hφ r'
    rw [dist_comm r (φ r)] at h2
    linarith
  refine (iInf₂_le (R.image φ) hsp).trans ?_
  unfold cellOscillation
  refine iSup₂_le fun u v ↦ iSup₂_le fun huv h ↦ ?_
  have hcell : ∀ r ∈ R, r ≤ φ.symm u ∨ φ.symm v < r := by
    intro r hr
    rcases h (φ r) (Finset.mem_image_of_mem _ hr) with h' | h'
    · exact Or.inl (by rw [φ.le_symm_apply]; exact h')
    · exact Or.inr (by rw [φ.symm_apply_lt]; exact h')
  have hosc := edist_le_cellOscillation (x := x) (φ.symm.monotone huv) hcell
  have hu := hxy (φ.symm u)
  have hv := hxy (φ.symm v)
  simp only [OrderIso.apply_symm_apply] at hu hv
  calc edist (y u) (y v)
      ≤ edist (y u) (x (φ.symm u)) + edist (x (φ.symm u)) (x (φ.symm v)) +
          edist (x (φ.symm v)) (y v) := edist_triangle4 _ _ _ _
    _ ≤ ENNReal.ofReal ρ + cellOscillation x R + ENNReal.ofReal ρ := by
        rw [edist_comm (y u)]
        gcongr
    _ = cellOscillation x R + 2 * ENNReal.ofReal ρ := by ring

/-- **Perturbation of the càdlàg modulus** in the Skorokhod `J₁` metric: if
`d(x, y) < ρ`, then `w'_y(δ - 2ρ) ≤ w'_x(δ) + 2ρ`. -/
theorem cadlagModulus_le_of_skorokhodEDist_lt {x y : I → E} {ρ δ : ℝ}
    (h : skorokhodEDist x y < ENNReal.ofReal ρ) :
    cadlagModulus y (δ - 2 * ρ) ≤ cadlagModulus x δ + 2 * ENNReal.ofReal ρ := by
  obtain ⟨φ, hφ, hxy⟩ := exists_timeChange_of_skorokhodEDist_lt h
  exact cadlagModulus_le_of_timeChange φ (fun t ↦ edist_lt_ofReal.1 (hφ t)) hxy

namespace SkorokhodSpace

/-- **Billingsley, Theorem 12.3** (necessity, modulus part). On a compact set of the Skorokhod
space the càdlàg modulus is uniformly small: for every `ε > 0` there is `δ > 0` with
`w'_x(δ) < ε` for all `x ∈ K`. -/
theorem exists_forall_cadlagModulus_lt_of_isCompact {K : Set (SkorokhodSpace E)}
    (hK : IsCompact K) {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ δ > 0, ∀ x ∈ K, cadlagModulus (⇑x) δ < ε := by
  classical
  have hε₂ : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hε₄ : 0 < ε / 2 / 2 := ENNReal.half_pos hε₂.ne'
  obtain ⟨ρ, hρ, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ENNReal.ofReal ρ < ε / 2 / 2 := by
    obtain ⟨r, hr0, hr⟩ := exists_between hε₄
    refine ⟨(r.toReal), ENNReal.toReal_pos hr0.ne' (hr.trans_le le_top |>.ne_top), ?_⟩
    rwa [ENNReal.ofReal_toReal (hr.trans_le le_top).ne_top]
  choose δ hδ hδε using fun x : SkorokhodSpace E ↦ x.isCadlag.exists_cadlagModulus_lt hε₂
  set r : SkorokhodSpace E → ℝ := fun x ↦ min ρ (δ x / 4)
  have hr (x : SkorokhodSpace E) : 0 < r x := lt_min hρ (by linarith [hδ x])
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun x ↦ Metric.eball x (ENNReal.ofReal (r x)))
    fun x _ ↦ Metric.eball_mem_nhds (x := x) (ENNReal.ofReal_pos.2 (hr x))
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exact ⟨1, one_pos, fun x hx ↦ by simpa using htK hx⟩
  refine ⟨t.inf' ht fun x ↦ δ x / 2, (Finset.lt_inf'_iff ht).2 fun x _ ↦ half_pos (hδ x),
    fun y hy ↦ ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (htK hy)
  rw [Metric.mem_eball, edist_comm, edist_def] at hyx
  have hmono : t.inf' ht (fun x ↦ δ x / 2) ≤ δ x - 2 * r x := by
    refine (Finset.inf'_le _ hxt).trans ?_
    have : r x ≤ δ x / 4 := min_le_right _ _
    linarith
  have hrρ : ENNReal.ofReal (r x) ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (min_le_left _ _)
  calc cadlagModulus (⇑y) (t.inf' ht fun x ↦ δ x / 2)
      ≤ cadlagModulus (⇑y) (δ x - 2 * r x) := cadlagModulus_mono _ hmono
    _ ≤ cadlagModulus (⇑x) (δ x) + 2 * ENNReal.ofReal (r x) :=
        cadlagModulus_le_of_skorokhodEDist_lt hyx
    _ < ε / 2 + ε / 2 := by
        refine ENNReal.add_lt_add_of_lt_of_le (by finiteness) (hδε x) ?_
        calc 2 * ENNReal.ofReal (r x) ≤ 2 * (ε / 2 / 2) := by gcongr; exact hrρ.trans hρε.le
          _ = ε / 2 := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
    _ = ε := ENNReal.add_halves ε

/-- **Billingsley, Theorem 12.3** (necessity, range part). The values of the functions of a
compact set of the Skorokhod space lie in a totally bounded set. -/
theorem exists_totallyBounded_of_isCompact {K : Set (SkorokhodSpace E)} (hK : IsCompact K) :
    ∃ C : Set E, TotallyBounded C ∧ ∀ x ∈ K, ∀ t, x t ∈ C := by
  refine ⟨⋃ x ∈ K, range x, ?_, fun x hx t ↦ mem_iUnion₂.2 ⟨x, hx, mem_range_self t⟩⟩
  rw [EMetric.totallyBounded_iff]
  intro ε hε
  have hε₂ : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun x ↦ Metric.eball x (ε / 2))
    fun x _ ↦ Metric.eball_mem_nhds (x := x) hε₂
  choose g hgf hg using fun x : SkorokhodSpace E ↦ x.isCadlag.exists_finite_range_edist_lt hε₂
  refine ⟨⋃ x ∈ t, range (g x), t.finite_toSet.biUnion fun x _ ↦ hgf x, ?_⟩
  intro z hz
  obtain ⟨y, hy, s, rfl⟩ := by simpa only [mem_iUnion₂, mem_range, exists_prop] using hz
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (htK hy)
  rw [Metric.mem_eball] at hyx
  obtain ⟨φ, -, hφ⟩ := exists_timeChange_of_edist_lt hyx
  refine mem_iUnion₂.2 ⟨g x (φ s), mem_iUnion₂.2 ⟨x, hxt, mem_range_self _⟩, ?_⟩
  rw [Metric.mem_eball]
  calc edist (y s) (g x (φ s)) ≤ edist (y s) (x (φ s)) + edist (x (φ s)) (g x (φ s)) :=
        edist_triangle _ _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (hφ s) (hg x (φ s))
    _ = ε := ENNReal.add_halves ε

end SkorokhodSpace
