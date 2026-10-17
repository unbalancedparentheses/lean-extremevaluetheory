/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import Mathlib.Topology.Order.Cadlag
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Skorokhod space `D[0, 1]` and the Skorokhod `J₁` metric

Let `E` be a (pseudo extended) metric space. A *time change* is an order automorphism `φ` of the
unit interval `I = [0, 1]`, i.e. an increasing homeomorphism of `I`; every order automorphism of
`I` is a homeomorphism and fixes `0` and `1`. For functions `x y : I → E` the
*Skorokhod `J₁` distance* is
`d(x, y) = inf_φ max (sup_t |φ t - t|, sup_t edist (x t) (y (φ t)))`,
see [Billingsley, *Convergence of Probability Measures*, §12][billingsley1999].
We define it with values in `ℝ≥0∞`, so that it makes sense for arbitrary functions, and show
that it is a pseudo extended metric on `I → E` which is bounded by the uniform distance.

The *Skorokhod space* `SkorokhodSpace E = D([0, 1], E)` is the type of càdlàg functions
`I → E`. We equip it with the Skorokhod distance. Two right-continuous functions at Skorokhod
distance zero agree, so `SkorokhodSpace E` is an extended metric space when `E` is, and a metric
space when `E` is a metric space, since càdlàg functions on `I` are bounded.

## Main definitions

* `skorokhodEDistWith φ x y`: the cost `max (sup_t edist (φ t) t) (sup_t edist (x t) (y (φ t)))`
  of matching `x` with `y` through the time change `φ`.
* `skorokhodEDist x y`: the Skorokhod `J₁` distance, the infimum of these costs over all
  time changes.
* `SkorokhodSpace E`: the type of càdlàg functions `I → E`, with the Skorokhod `J₁` metric.

## Main statements

* `skorokhodEDist_triangle`, `skorokhodEDist_comm`, `skorokhodEDist_self`: `skorokhodEDist`
  is a pseudo extended metric on `I → E`.
* `skorokhodEDist_le_iSup_edist`: the Skorokhod distance is at most the uniform distance.
* `edist_eq_zero_of_skorokhodEDist_eq_zero`: two right-continuous functions at Skorokhod distance
  zero agree (up to `edist` zero).
* `SkorokhodSpace.tendsto_iff_tendstoUniformly`: convergence in the Skorokhod topology to a
  continuous limit is the same as uniform convergence.
* `SkorokhodSpace.lipschitzWith_ofContinuousMap`: the inclusion `C([0, 1], E) → D([0, 1], E)` is
  `1`-Lipschitz for the uniform metric.
* `SkorokhodSpace.tendsto_apply_of_continuousAt`: convergence in the Skorokhod topology implies
  convergence at every continuity point of the limit, and at the endpoints `0` and `1`
  (`SkorokhodSpace.tendsto_apply_zero`, `SkorokhodSpace.tendsto_apply_one`).

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

@[expose] public section

open Filter Set Topology unitInterval
open scoped ENNReal

variable {E : Type*}

section skorokhodEDist

variable [PseudoEMetricSpace E] {x y z : I → E} {φ : I ≃o I} {ε : ℝ≥0∞}

/-- The cost of matching `x` with `y` through the time change `φ`: the larger of the uniform
distance from `φ` to the identity and the uniform distance from `x` to `y ∘ φ`. -/
noncomputable def skorokhodEDistWith (φ : I ≃o I) (x y : I → E) : ℝ≥0∞ :=
  max (⨆ t, edist (φ t) t) (⨆ t, edist (x t) (y (φ t)))

/-- The Skorokhod `J₁` distance between two functions `x y : I → E`: the infimum over all time
changes `φ` of `max (sup_t edist (φ t) t) (sup_t edist (x t) (y (φ t)))`. -/
noncomputable def skorokhodEDist (x y : I → E) : ℝ≥0∞ :=
  ⨅ φ : I ≃o I, skorokhodEDistWith φ x y

lemma edist_apply_le_skorokhodEDistWith (φ : I ≃o I) (x y : I → E) (t : I) :
    edist (φ t) t ≤ skorokhodEDistWith φ x y :=
  (le_iSup (fun t ↦ edist (φ t) t) t).trans (le_max_left _ _)

lemma edist_apply_apply_le_skorokhodEDistWith (φ : I ≃o I) (x y : I → E) (t : I) :
    edist (x t) (y (φ t)) ≤ skorokhodEDistWith φ x y :=
  (le_iSup (fun t ↦ edist (x t) (y (φ t))) t).trans (le_max_right _ _)

lemma skorokhodEDistWith_le (hφ : ∀ t, edist (φ t) t ≤ ε)
    (hxy : ∀ t, edist (x t) (y (φ t)) ≤ ε) : skorokhodEDistWith φ x y ≤ ε :=
  max_le (iSup_le hφ) (iSup_le hxy)

lemma skorokhodEDist_le_skorokhodEDistWith (φ : I ≃o I) (x y : I → E) :
    skorokhodEDist x y ≤ skorokhodEDistWith φ x y :=
  iInf_le _ φ

/-- To bound the Skorokhod distance, it suffices to exhibit a single good time change. -/
lemma skorokhodEDist_le_of_forall (φ : I ≃o I) (hφ : ∀ t, edist (φ t) t ≤ ε)
    (hxy : ∀ t, edist (x t) (y (φ t)) ≤ ε) : skorokhodEDist x y ≤ ε :=
  (skorokhodEDist_le_skorokhodEDistWith φ x y).trans (skorokhodEDistWith_le hφ hxy)

/-- If the Skorokhod distance is less than `ε`, there is a time change within `ε` of the
identity matching `x` with `y` up to `ε`. -/
lemma exists_timeChange_of_skorokhodEDist_lt (h : skorokhodEDist x y < ε) :
    ∃ φ : I ≃o I, (∀ t, edist (φ t) t < ε) ∧ ∀ t, edist (x t) (y (φ t)) < ε := by
  obtain ⟨φ, hφ⟩ := iInf_lt_iff.1 h
  exact ⟨φ, fun t ↦ (edist_apply_le_skorokhodEDistWith φ x y t).trans_lt hφ,
    fun t ↦ (edist_apply_apply_le_skorokhodEDistWith φ x y t).trans_lt hφ⟩

@[simp]
lemma skorokhodEDist_self (x : I → E) : skorokhodEDist x x = 0 :=
  nonpos_iff_eq_zero.1 <| skorokhodEDist_le_of_forall (OrderIso.refl I) (by simp) (by simp)

/-- The Skorokhod distance is bounded by the uniform distance. -/
lemma skorokhodEDist_le_iSup_edist (x y : I → E) :
    skorokhodEDist x y ≤ ⨆ t, edist (x t) (y t) :=
  skorokhodEDist_le_of_forall (OrderIso.refl I) (by simp)
    (fun t ↦ le_iSup (fun t ↦ edist (x t) (y t)) t)

lemma skorokhodEDist_le_of_forall_edist_le (h : ∀ t, edist (x t) (y t) ≤ ε) :
    skorokhodEDist x y ≤ ε :=
  (skorokhodEDist_le_iSup_edist x y).trans (iSup_le h)

lemma skorokhodEDist_comm (x y : I → E) : skorokhodEDist x y = skorokhodEDist y x := by
  suffices H : ∀ x y : I → E, skorokhodEDist y x ≤ skorokhodEDist x y from
    le_antisymm (H y x) (H x y)
  intro x y
  refine le_iInf fun φ ↦ skorokhodEDist_le_of_forall φ.symm (fun t ↦ ?_) (fun t ↦ ?_)
  · have := edist_apply_le_skorokhodEDistWith φ x y (φ.symm t)
    rwa [OrderIso.apply_symm_apply, edist_comm] at this
  · have := edist_apply_apply_le_skorokhodEDistWith φ x y (φ.symm t)
    rwa [OrderIso.apply_symm_apply, edist_comm] at this

lemma skorokhodEDist_triangle (x y z : I → E) :
    skorokhodEDist x z ≤ skorokhodEDist x y + skorokhodEDist y z := by
  refine ENNReal.le_iInf_add_iInf fun φ ψ ↦
    skorokhodEDist_le_of_forall (φ.trans ψ) (fun t ↦ ?_) (fun t ↦ ?_)
  · calc edist (ψ (φ t)) t ≤ edist (ψ (φ t)) (φ t) + edist (φ t) t := edist_triangle _ _ _
      _ ≤ skorokhodEDistWith φ x y + skorokhodEDistWith ψ y z := by
        rw [add_comm]
        exact add_le_add (edist_apply_le_skorokhodEDistWith φ x y t)
          (edist_apply_le_skorokhodEDistWith ψ y z (φ t))
  · calc edist (x t) (z (ψ (φ t))) ≤ edist (x t) (y (φ t)) + edist (y (φ t)) (z (ψ (φ t))) :=
          edist_triangle _ _ _
      _ ≤ skorokhodEDistWith φ x y + skorokhodEDistWith ψ y z :=
        add_le_add (edist_apply_apply_le_skorokhodEDistWith φ x y t)
          (edist_apply_apply_le_skorokhodEDistWith ψ y z (φ t))

/-- Two right-continuous functions at Skorokhod distance zero agree up to `edist` zero
([Billingsley, §12][billingsley1999]). -/
lemma edist_eq_zero_of_skorokhodEDist_eq_zero (hx : IsRightContinuous x)
    (hy : IsRightContinuous y) (h : skorokhodEDist x y = 0) (t : I) : edist (x t) (y t) = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) (zero_le)
  rw [zero_add]
  rcases eq_or_lt_of_le (le_top : t ≤ ⊤) with rfl | ht
  · -- Every time change fixes `1`.
    obtain ⟨φ, -, hφ⟩ := exists_timeChange_of_skorokhodEDist_lt
      (h.trans_lt (ENNReal.coe_pos.2 hε))
    simpa using (hφ ⊤).le
  · -- For `t < 1`, compare `x t` and `y t` through `x s ≈ y (φ s)` for some `s > t` close to `t`.
    set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 3
    have hδ : 0 < δ := ENNReal.div_pos (ENNReal.coe_pos.2 hε).ne' ENNReal.ofNat_ne_top
    have hevent : ∀ᶠ u in 𝓝[>] t, edist (x u) (x t) < δ ∧ edist (y u) (y t) < δ :=
      ((hx t).tendsto.eventually (Metric.eball_mem_nhds _ hδ)).and
        ((hy t).tendsto.eventually (Metric.eball_mem_nhds _ hδ))
    obtain ⟨b, hb, hbs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' ht).1 hevent
    obtain ⟨s, hts, hsb⟩ := exists_between (α := I) hb
    obtain ⟨η, hη, hηs⟩ := EMetric.mem_nhds_iff.1 (isOpen_Ioo.mem_nhds ⟨hts, hsb⟩)
    obtain ⟨φ, hφ, hxy⟩ := exists_timeChange_of_skorokhodEDist_lt
      (h.trans_lt (lt_min hη hδ : 0 < min η δ))
    have hφs : φ s ∈ Ioo t b := hηs ((hφ s).trans_le (min_le_left _ _))
    calc edist (x t) (y t) ≤ edist (x t) (x s) + edist (x s) (y (φ s)) + edist (y (φ s)) (y t) :=
          edist_triangle4 _ _ _ _
      _ ≤ δ + δ + δ := by
        gcongr
        · rw [edist_comm]; exact (hbs ⟨hts, hsb⟩).1.le
        · exact (hxy s).le.trans (min_le_right _ _)
        · exact (hbs hφs).2.le
      _ = ε := ENNReal.add_thirds _

end skorokhodEDist

lemma skorokhodEDist_ne_top {E : Type*} [PseudoMetricSpace E] {x y : I → E}
    (hx : Bornology.IsBounded (range x)) (hy : Bornology.IsBounded (range y)) :
    skorokhodEDist x y ≠ ⊤ := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (hx.union hy)
  have hC0 : 0 ≤ C := dist_nonneg.trans (hC (Or.inl ⟨0, rfl⟩) (Or.inl ⟨0, rfl⟩))
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (skorokhodEDist_le_of_forall_edist_le
    fun t ↦ (edist_le_ofReal hC0).2 (hC (Or.inl ⟨t, rfl⟩) (Or.inr ⟨t, rfl⟩)))

/-! ### The Skorokhod space -/

/-- The *Skorokhod space* `D([0, 1], E)`: the type of càdlàg (right-continuous with left limits)
functions from the unit interval to `E`. When `E` is a (pseudo extended) metric space it is
equipped with the Skorokhod `J₁` (pseudo extended) metric `skorokhodEDist`. -/
structure SkorokhodSpace (E : Type*) [TopologicalSpace E] where
  /-- The underlying function of an element of the Skorokhod space. -/
  toFun : I → E
  isCadlag' : IsCadlag toFun

namespace SkorokhodSpace

section TopologicalSpace

variable [TopologicalSpace E]

instance instFunLike : FunLike (SkorokhodSpace E) I E where
  coe := toFun
  coe_injective x y h := by cases x; cases y; congr

lemma isCadlag (x : SkorokhodSpace E) : IsCadlag x := x.isCadlag'

lemma isRightContinuous (x : SkorokhodSpace E) : IsRightContinuous x := x.isCadlag.1

@[ext]
lemma ext {x y : SkorokhodSpace E} (h : ∀ t, x t = y t) : x = y := DFunLike.ext _ _ h

@[simp]
lemma coe_mk (f : I → E) (hf : IsCadlag f) : ⇑(⟨f, hf⟩ : SkorokhodSpace E) = f := rfl

/-- A continuous function on the unit interval as an element of the Skorokhod space. -/
def ofContinuousMap (f : C(I, E)) : SkorokhodSpace E := ⟨f, f.continuous.isCadlag⟩

@[simp]
lemma coe_ofContinuousMap (f : C(I, E)) : ⇑(ofContinuousMap f) = f := rfl

end TopologicalSpace

section PseudoEMetricSpace

variable [PseudoEMetricSpace E]

/-- The Skorokhod `J₁` pseudo extended metric on `D([0, 1], E)`. -/
noncomputable instance instPseudoEMetricSpace : PseudoEMetricSpace (SkorokhodSpace E) where
  edist x y := skorokhodEDist x y
  edist_self x := skorokhodEDist_self x
  edist_comm x y := skorokhodEDist_comm x y
  edist_triangle x y z := skorokhodEDist_triangle x y z

lemma edist_def (x y : SkorokhodSpace E) : edist x y = skorokhodEDist x y := rfl

lemma edist_le_iSup_edist (x y : SkorokhodSpace E) : edist x y ≤ ⨆ t, edist (x t) (y t) :=
  skorokhodEDist_le_iSup_edist x y

lemma edist_le_of_forall_edist_le {x y : SkorokhodSpace E} {ε : ℝ≥0∞}
    (h : ∀ t, edist (x t) (y t) ≤ ε) : edist x y ≤ ε :=
  skorokhodEDist_le_of_forall_edist_le h

lemma exists_timeChange_of_edist_lt {x y : SkorokhodSpace E} {ε : ℝ≥0∞} (h : edist x y < ε) :
    ∃ φ : I ≃o I, (∀ t, edist (φ t) t < ε) ∧ ∀ t, edist (x t) (y (φ t)) < ε :=
  exists_timeChange_of_skorokhodEDist_lt h

/-- Uniform convergence implies convergence in the Skorokhod topology. -/
lemma tendsto_of_tendstoUniformly {ι : Type*} {l : Filter ι} {x : ι → SkorokhodSpace E}
    {y : SkorokhodSpace E} (h : TendstoUniformly (fun i ↦ ⇑(x i)) y l) :
    Tendsto x l (𝓝 y) := by
  refine EMetric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  filter_upwards [EMetric.tendstoUniformly_iff.1 h δ hδ] with i hi
  rw [edist_comm]
  exact (edist_le_of_forall_edist_le fun t ↦ (hi t).le).trans_lt hδε

/-- Convergence in the Skorokhod topology implies convergence at every continuity point of the
limit ([Billingsley, §12][billingsley1999]). -/
lemma tendsto_apply_of_continuousAt {ι : Type*} {l : Filter ι} {x : ι → SkorokhodSpace E}
    {y : SkorokhodSpace E} (h : Tendsto x l (𝓝 y)) {t : I} (ht : ContinuousAt y t) :
    Tendsto (fun i ↦ x i t) l (𝓝 (y t)) := by
  refine EMetric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hyδ⟩ := EMetric.continuousAt_iff.1 ht (ε / 2) (ENNReal.half_pos hε.ne')
  filter_upwards [EMetric.tendsto_nhds.1 h (min δ (ε / 2))
    (lt_min hδ (ENNReal.half_pos hε.ne'))] with i hi
  obtain ⟨φ, hφ, hxy⟩ := exists_timeChange_of_edist_lt hi
  calc edist (x i t) (y t) ≤ edist (x i t) (y (φ t)) + edist (y (φ t)) (y t) :=
        edist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
        ENNReal.add_lt_add ((hxy t).trans_le (min_le_right _ _))
          (hyδ ((hφ t).trans_le (min_le_left _ _)))
    _ = ε := ENNReal.add_halves ε

/-- Convergence in the Skorokhod topology implies convergence at a point `t` fixed by every time
change, i.e. at `t = 0` or `t = 1`. -/
lemma tendsto_apply_of_forall_timeChange_apply_eq {ι : Type*} {l : Filter ι}
    {x : ι → SkorokhodSpace E} {y : SkorokhodSpace E} (h : Tendsto x l (𝓝 y)) {t : I}
    (ht : ∀ φ : I ≃o I, φ t = t) : Tendsto (fun i ↦ x i t) l (𝓝 (y t)) := by
  refine EMetric.tendsto_nhds.2 fun ε hε ↦ ?_
  filter_upwards [EMetric.tendsto_nhds.1 h ε hε] with i hi
  obtain ⟨φ, -, hxy⟩ := exists_timeChange_of_edist_lt hi
  simpa [ht φ] using hxy t

lemma tendsto_apply_zero {ι : Type*} {l : Filter ι} {x : ι → SkorokhodSpace E}
    {y : SkorokhodSpace E} (h : Tendsto x l (𝓝 y)) : Tendsto (fun i ↦ x i 0) l (𝓝 (y 0)) :=
  tendsto_apply_of_forall_timeChange_apply_eq h fun φ ↦ φ.map_bot

lemma tendsto_apply_one {ι : Type*} {l : Filter ι} {x : ι → SkorokhodSpace E}
    {y : SkorokhodSpace E} (h : Tendsto x l (𝓝 y)) : Tendsto (fun i ↦ x i 1) l (𝓝 (y 1)) :=
  tendsto_apply_of_forall_timeChange_apply_eq h fun φ ↦ φ.map_top

/-- Convergence in the Skorokhod topology to a continuous limit is uniform convergence
([Billingsley, §12][billingsley1999]). -/
lemma tendsto_iff_tendstoUniformly {ι : Type*} {l : Filter ι} {x : ι → SkorokhodSpace E}
    {y : SkorokhodSpace E} (hy : Continuous y) :
    Tendsto x l (𝓝 y) ↔ TendstoUniformly (fun i ↦ ⇑(x i)) y l := by
  refine ⟨fun h ↦ EMetric.tendstoUniformly_iff.2 fun ε hε ↦ ?_, tendsto_of_tendstoUniformly⟩
  obtain ⟨δ, hδ, hyδ⟩ := EMetric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hy) (ε / 2) (ENNReal.half_pos hε.ne')
  filter_upwards [EMetric.tendsto_nhds.1 h (min δ (ε / 2))
    (lt_min hδ (ENNReal.half_pos hε.ne'))] with i hi t
  obtain ⟨φ, hφ, hxy⟩ := exists_timeChange_of_edist_lt hi
  calc edist (y t) (x i t) ≤ edist (y t) (y (φ t)) + edist (y (φ t)) (x i t) :=
        edist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [edist_comm (y (φ t))]
        exact ENNReal.add_lt_add (hyδ (by rw [edist_comm]; exact (hφ t).trans_le (min_le_left _ _)))
          ((hxy t).trans_le (min_le_right _ _))
    _ = ε := ENNReal.add_halves ε

end PseudoEMetricSpace

/-- The Skorokhod `J₁` extended metric on `D([0, 1], E)`. -/
noncomputable instance instEMetricSpace [EMetricSpace E] : EMetricSpace (SkorokhodSpace E) where
  eq_of_edist_eq_zero {x y} h := ext fun t ↦ edist_eq_zero.1 <|
    edist_eq_zero_of_skorokhodEDist_eq_zero x.isRightContinuous y.isRightContinuous h t

section PseudoMetricSpace

variable [PseudoMetricSpace E]

lemma isBounded_range (x : SkorokhodSpace E) : Bornology.IsBounded (range x) := by
  simpa using isBounded_image_of_isCadlag_of_isCompact x.isCadlag isCompact_univ

lemma edist_ne_top (x y : SkorokhodSpace E) : edist x y ≠ ⊤ :=
  skorokhodEDist_ne_top x.isBounded_range y.isBounded_range

/-- The Skorokhod `J₁` pseudometric on `D([0, 1], E)`: càdlàg functions on `[0, 1]` are bounded,
so the Skorokhod distance is finite. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (SkorokhodSpace E) :=
  PseudoEMetricSpace.toPseudoMetricSpace edist_ne_top

lemma dist_def (x y : SkorokhodSpace E) : dist x y = (skorokhodEDist x y).toReal := rfl

lemma dist_le_of_forall_dist_le {x y : SkorokhodSpace E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t, dist (x t) (y t) ≤ C) : dist x y ≤ C := by
  rw [dist_edist]
  exact ENNReal.toReal_le_of_le_ofReal hC
    (edist_le_of_forall_edist_le fun t ↦ (edist_le_ofReal hC).2 (h t))

/-- The inclusion of `C([0, 1], E)` with the uniform metric into the Skorokhod space is
`1`-Lipschitz. -/
lemma lipschitzWith_ofContinuousMap :
    LipschitzWith 1 (ofContinuousMap : C(I, E) → SkorokhodSpace E) :=
  LipschitzWith.mk_one fun _ _ ↦
    dist_le_of_forall_dist_le dist_nonneg fun t ↦ ContinuousMap.dist_apply_le_dist t

lemma continuous_ofContinuousMap : Continuous (ofContinuousMap : C(I, E) → SkorokhodSpace E) :=
  lipschitzWith_ofContinuousMap.continuous

end PseudoMetricSpace

/-- The Skorokhod `J₁` metric on `D([0, 1], E)`. -/
noncomputable instance instMetricSpace [MetricSpace E] : MetricSpace (SkorokhodSpace E) where
  eq_of_dist_eq_zero {x y} h := eq_of_edist_eq_zero <| by
    rw [edist_dist, h, ENNReal.ofReal_zero]

example [MetricSpace E] :
    (instEMetricSpace : EMetricSpace (SkorokhodSpace E)) = MetricSpace.toEMetricSpace := by
  with_reducible_and_instances rfl

example [PseudoMetricSpace E] : (instPseudoEMetricSpace : PseudoEMetricSpace (SkorokhodSpace E)) =
    PseudoMetricSpace.toPseudoEMetricSpace := by
  with_reducible_and_instances rfl

end SkorokhodSpace
