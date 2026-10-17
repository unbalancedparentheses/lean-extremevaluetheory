/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.ThetaGap
import ExtremeValueTheory.Dependence.MDependentExamples

/-!
# The echo process: `θ < ϑ`

TODO
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Asymptotic independence gives the trivial spectral tail process -/

section AsymptoticIndependence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℤ → Ω → ℝ} {α : ℝ}

/-- The spectral tail process `Θ_t = 1{t = 0}` of an asymptotically independent nonnegative
series, on the one-point space. -/
def unitSpectral (t : ℤ) (_ : Unit) : ℝ := if t = 0 then 1 else 0

theorem measurable_unitSpectral (t : ℤ) : Measurable (unitSpectral t) := measurable_const

/-- **Asymptotic independence gives `Θ = (…, 0, 1, 0, …)`.** If `X_0 ≥ 0`, `P(|X_0| > x)` is
regularly varying with index `-α`, and for every `t ≠ 0` and `ε > 0`,
`P(|X_t| > ε x | |X_0| > x) → 0`, then the spectral tail process is `Θ_t = 1{t = 0}`. -/
theorem hasSpectralTailProcess_of_asymptoticIndependence (hX : ∀ t, Measurable (X t))
    (hX0 : ∀ ω, 0 ≤ X 0 ω) (hRV : IsRegularlyVarying (fun x => P.real {ω | x < |X 0 ω|}) (-α))
    (hai : ∀ t : ℤ, t ≠ 0 → ∀ ε : ℝ, 0 < ε → Tendsto (fun x =>
      P.real {ω | x < |X 0 ω| ∧ ε * x < |X t ω|} / P.real {ω | x < |X 0 ω|}) atTop (𝓝 0)) :
    HasSpectralTailProcess P X α (Measure.dirac ()) unitSpectral := by
  classical
  refine ⟨hRV, fun S f => ?_⟩
  set e : S → ℝ := fun t => if (t : ℤ) = 0 then 1 else 0
  have hmap : (Measure.dirac ()).map (fun ω' (t : S) => unitSpectral t ω') = Measure.dirac e := by
    rw [Measure.map_dirac' (measurable_pi_iff.2 fun t => measurable_unitSpectral _)]
    rfl
  rw [hmap, integral_dirac]
  set s : ℝ → Set Ω := fun x => {ω | x < |X 0 ω|}
  have hZ : Measurable fun ω => |X 0 ω| := continuous_abs.measurable.comp (hX 0)
  have hs : ∀ x, MeasurableSet (s x) := fun x => measurableSet_lt measurable_const hZ
  set w : Ω → (S → ℝ) := fun ω t => X t ω / |X 0 ω|
  have hw : Measurable w := measurable_pi_iff.2 fun t => (hX t).div hZ
  have hpos : ∀ᶠ x in atTop, 0 < P.real (s x) := hRV.eventually_pos
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.1 f.continuous e (η / 2) (half_pos hη)
  set C := ‖f‖
  have hC : 0 ≤ C := norm_nonneg _
  set T : Finset ℤ := S.filter fun t => t ≠ 0
  set B : ℝ → Set Ω := fun x => ⋃ t ∈ T, {ω | δ * x < |X t ω|}
  have hB : ∀ x, MeasurableSet (B x) := fun x =>
    Finset.measurableSet_biUnion _ fun t _ =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX t))
  -- the conditional probability of `B` vanishes
  have hBlim : Tendsto (fun x => ∑ t ∈ T,
      P.real {ω | x < |X 0 ω| ∧ δ * x < |X t ω|} / P.real {ω | x < |X 0 ω|}) atTop (𝓝 0) := by
    have := tendsto_finsetSum T fun t ht => hai t (Finset.mem_filter.1 ht).2 δ hδ
    simpa using this
  have hκ : 0 < η / (2 * (2 * C + 1)) := by positivity
  filter_upwards [hpos, eventually_gt_atTop 0, hBlim.eventually (gt_mem_nhds hκ)] with x hx hx0 hxB
  have hP : P (s x) ≠ 0 := fun h0 => by simp [measureReal_def, h0] at hx
  have := cond_isProbabilityMeasure (μ := P) hP
  set μ := P[|s x]
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂μ, |f (w ω) - f e| ≤ η / 2 + 2 * C * (B x).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [ae_cond_mem (hs x)] with ω hω
    have hω' : x < |X 0 ω| := hω
    by_cases hωB : ω ∈ B x
    · rw [indicator_of_mem hωB, mul_one]
      have := f.dist_le_two_norm (w ω) e
      rw [Real.dist_eq] at this
      linarith
    · rw [indicator_of_notMem hωB, mul_zero, add_zero]
      have hlt : dist (w ω) e < δ := by
        rw [dist_pi_lt_iff hδ]
        intro t
        by_cases ht : (t : ℤ) = 0
        · have hX0pos : 0 < X 0 ω := by
            have := hx0.trans hω'
            rwa [abs_of_nonneg (hX0 ω)] at this
          have h1 : w ω t = 1 := by
            simp only [w, ht, abs_of_nonneg (hX0 ω)]
            exact div_self hX0pos.ne'
          have h2 : e t = 1 := by simp [e, ht]
          rw [h1, h2, dist_self]
          exact hδ
        · have hnB : ¬ δ * x < |X t ω| := fun hcon =>
            hωB (mem_iUnion₂.2 ⟨t, Finset.mem_filter.2 ⟨t.2, ht⟩, hcon⟩)
          simp only [w, e, ht, ite_false, Real.dist_eq, sub_zero, abs_div, abs_abs]
          rw [div_lt_iff₀ (hx0.trans hω')]
          calc |X t ω| ≤ δ * x := not_lt.1 hnB
            _ < δ * |X 0 ω| := mul_lt_mul_of_pos_left hω' hδ
      have := hfδ (w ω) hlt
      rw [Real.dist_eq] at this
      exact this.le
  have hfw : Integrable (fun ω => f (w ω)) μ :=
    integrable_of_abs_le (f.continuous.measurable.comp hw) fun ω => by
      simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (w ω)
  have hint : Integrable (fun ω => η / 2 + 2 * C * (B x).indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator (hB x) |>.const_mul _)
  have hμB : μ.real (B x) ≤ η / (2 * (2 * C + 1)) := by
    rw [measureReal_def, cond_toReal_eq (hs x)]
    refine le_trans ?_ hxB.le
    rw [← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ measureReal_nonneg
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le T _)
    intro ω ⟨h0, h1⟩
    obtain ⟨t, ht, hlt⟩ := mem_iUnion₂.1 h1
    exact mem_iUnion₂.2 ⟨t, ht, h0, hlt⟩
  rw [Real.dist_eq, show f e = ∫ _, f e ∂μ by simp, ← integral_sub hfw (integrable_const _)]
  calc |∫ ω, (f (w ω) - f e) ∂μ| ≤ ∫ ω, |f (w ω) - f e| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (η / 2 + 2 * C * (B x).indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
        integral_mono_ae (hfw.sub (integrable_const _)).abs hint hpt
    _ = η / 2 + 2 * C * μ.real (B x) := by
        rw [integral_add (integrable_const _) ((integrable_const (1 : ℝ)).indicator (hB x)
          |>.const_mul _), integral_const_mul, integral_indicator_const _ (hB x)]
        simp
    _ ≤ η / 2 + 2 * C * (η / (2 * (2 * C + 1))) := by gcongr
    _ < η := by
        have : 2 * C * (η / (2 * (2 * C + 1))) < η / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

end AsymptoticIndependence

/-! ### Two general tools -/

section Tools

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Shift functionals of iid noise are stationary**: `X_t = G((Z_{t + i})_{i ∈ ℤ})` for a
measurable `G`. The law of the whole shifted sequence is shift invariant, as the projective limit
of its (shift invariant) finite-dimensional laws. -/
theorem hasShiftInvariantWindows_of_shift {Z : ℤ → Ω → ℝ} (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hid : ∀ i, IdentDistrib (Z i) (Z 0) P P) {G : (ℤ → ℝ) → ℝ}
    (hG : Measurable G) :
    HasShiftInvariantWindows P (fun t ω => G (fun i => Z (t + i) ω)) := by
  have hstat := hasShiftInvariantWindows_of_iIndepFun hZ hind hid
  set Ψ : ℤ → Ω → (ℤ → ℝ) := fun h ω i => Z (i + h) ω
  have hΨ : ∀ h, Measurable (Ψ h) := fun h => measurable_pi_iff.2 fun i => hZ _
  have hlaw : ∀ h, P.map (Ψ h) = P.map (Ψ 0) := by
    intro h
    have hlim : ∀ k, IsProjectiveLimit (P.map (Ψ k))
        (fun J : Finset ℤ => P.map fun ω (j : J) => Z j ω) := by
      intro k J
      rw [Measure.map_map (Finset.measurable_restrict J) (hΨ k)]
      exact hstat k J
    have : ∀ J : Finset ℤ, IsFiniteMeasure (P.map fun ω (j : J) => Z j ω) := fun J =>
      inferInstance
    exact (hlim h).unique (hlim 0)
  intro h S
  set Φ : (ℤ → ℝ) → (S → ℝ) := fun z t => G (fun i => z (t + i))
  have hΦ : Measurable Φ := measurable_pi_iff.2 fun t =>
    hG.comp (measurable_pi_iff.2 fun i => measurable_pi_apply _)
  have e1 : (fun ω (t : S) => G (fun i => Z (t + h + i) ω)) = Φ ∘ Ψ h := by
    funext ω t
    simp only [Function.comp_apply, Φ, Ψ]
    congr 1
    funext i
    congr 1
    ring
  have e2 : (fun ω (t : S) => G (fun i => Z (t + i) ω)) = Φ ∘ Ψ 0 := by
    funext ω t
    simp [Φ, Ψ]
  rw [e1, e2, ← Measure.map_map hΦ (hΨ h), ← Measure.map_map hΦ (hΨ 0), hlaw h]

/-- **A Bonferroni lower bound for pairwise independent events**:
`P(⋃ⱼ Aⱼ) ≥ S - S²` with `S = ∑ⱼ P(Aⱼ)`. -/
theorem le_measureReal_iUnion_of_pairwise {A : ℕ → Set Ω} (hA : ∀ j, MeasurableSet (A j))
    (hind : ∀ i j, i ≠ j → P.real (A i ∩ A j) = P.real (A i) * P.real (A j))
    (hs : Summable fun j => P.real (A j)) :
    (∑' j, P.real (A j)) - (∑' j, P.real (A j)) ^ 2 ≤ P.real (⋃ j, A j) := by
  set p : ℕ → ℝ := fun j => P.real (A j)
  set U : ℕ → Set Ω := fun N => ⋃ j ∈ Finset.range N, A j
  have hU : ∀ N, MeasurableSet (U N) := fun N => Finset.measurableSet_biUnion _ fun j _ => hA j
  have hfin : ∀ N, (∑ j ∈ Finset.range N, p j) - (∑ j ∈ Finset.range N, p j) ^ 2 ≤
      P.real (U N) := by
    intro N
    induction N with
    | zero => simp [U]
    | succ N ih =>
      set SN := ∑ j ∈ Finset.range N, p j
      have hUs : U (N + 1) = U N ∪ A N := by
        ext ω
        simp only [U, Finset.mem_range, mem_iUnion, mem_union, exists_prop]
        constructor
        · rintro ⟨j, hj, hω⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact Or.inl ⟨j, hj, hω⟩
          · exact Or.inr hω
        · rintro (⟨j, hj, hω⟩ | hω)
          · exact ⟨j, by omega, hω⟩
          · exact ⟨N, by omega, hω⟩
      have hadd := measureReal_union_add_inter (μ := P) (s := U N) (hA N) (measure_ne_top _ _)
        (measure_ne_top _ _)
      have hinter : P.real (U N ∩ A N) ≤ SN * p N := by
        have : U N ∩ A N = ⋃ j ∈ Finset.range N, (A j ∩ A N) := by
          simp only [U, iUnion_inter]
        rw [this]
        refine (measureReal_biUnion_finset_le _ _).trans (le_of_eq ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j hj =>
          hind j N (Finset.mem_range.1 hj).ne
      have hSN : 0 ≤ SN := Finset.sum_nonneg fun j _ => measureReal_nonneg
      have hpN : 0 ≤ p N := measureReal_nonneg
      rw [Finset.sum_range_succ, hUs]
      nlinarith
  have hlim : Tendsto (fun N => (∑ j ∈ Finset.range N, p j) - (∑ j ∈ Finset.range N, p j) ^ 2)
      atTop (𝓝 ((∑' j, p j) - (∑' j, p j) ^ 2)) :=
    hs.hasSum.tendsto_sum_nat.sub (hs.hasSum.tendsto_sum_nat.pow 2)
  refine le_of_tendsto hlim (Eventually.of_forall fun N => (hfin N).trans ?_)
  exact measureReal_mono (iUnion₂_subset fun j _ => subset_iUnion A j)

/-- Countable union bound for `P.real`. -/
theorem measureReal_iUnion_le_tsum {A : ℕ → Set Ω} (hs : Summable fun j => P.real (A j)) :
    P.real (⋃ j, A j) ≤ ∑' j, P.real (A j) := by
  refine ENNReal.toReal_le_of_le_ofReal (tsum_nonneg fun _ => measureReal_nonneg) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hs]
  refine (measure_iUnion_le A).trans (le_of_eq (tsum_congr fun j => ?_))
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- `P.real` is countably additive. -/
theorem hasSum_measureReal_iUnion {A : ℕ → Set Ω} (hA : ∀ j, MeasurableSet (A j))
    (hd : Pairwise (Function.onFun Disjoint A)) :
    HasSum (fun j => P.real (A j)) (P.real (⋃ j, A j)) := by
  have h := measure_iUnion (μ := P) hd hA
  have hs : Summable fun j => P.real (A j) := by
    refine ENNReal.summable_toReal ?_
    rw [← h]
    exact measure_ne_top _ _
  refine hs.hasSum_iff.2 ?_
  rw [measureReal_def, h, ENNReal.tsum_toReal_eq fun _ => measure_ne_top _ _]
  rfl

end Tools

/-! ### The echo process -/

section Echo

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}

/-- The echo of the innovation at time `t - (j + 1)` into time `t`: it is `Z_{t - (j + 1)}` if the
echo lag `L(Z_{t - (j + 1)})` of that innovation is exactly `j + 1`, and `0` otherwise. -/
noncomputable def echoTerm (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (j : ℕ) (ω : Ω) : ℝ :=
  if L (Z (t - (j + 1)) ω) = j + 1 then Z (t - (j + 1)) ω else 0

/-- **The echo process** `X_t = max(Z_t, max {Z_s : s < t, s + L(Z_s) = t})`: every innovation
`Z_s` appears at time `s` and once more, as an echo, at time `s + L(Z_s)`. The echo lag
`L(Z_s) ≥ 1` grows with the size of the innovation. -/
noncomputable def echoProcess (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  max (Z t ω) (⨆ j : ℕ, echoTerm L Z t j ω)

/-- The *sources* of an exceedance of `x` at time `t`: `j = 0` is `Z_t > x` itself, `j ≥ 1` is
the echo of `Z_{t - j} > x` (`L(Z_{t - j}) = j`). -/
def echoSource (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (x : ℝ) (j : ℕ) : Set Ω :=
  {ω | x < Z (t - j) ω ∧ (j = 0 ∨ L (Z (t - j) ω) = j)}

/-- The set of values `z` giving a source with index `j` at level `x`. -/
def echoSourceSet (L : ℝ → ℕ) (x : ℝ) (j : ℕ) : Set ℝ := {z | x < z ∧ (j = 0 ∨ L z = j)}

theorem echoSource_eq (t : ℤ) (x : ℝ) (j : ℕ) :
    echoSource L Z t x j = Z (t - j) ⁻¹' echoSourceSet L x j := rfl

theorem measurableSet_echoSourceSet (hLm : Measurable L) (x : ℝ) (j : ℕ) :
    MeasurableSet (echoSourceSet L x j) := by
  refine measurableSet_Ioi.inter ((MeasurableSet.const (j = 0)).union ?_)
  exact hLm (measurableSet_singleton j)

theorem measurable_echoTerm (hZ : ∀ t, Measurable (Z t)) (hLm : Measurable L) (t : ℤ) (j : ℕ) :
    Measurable (echoTerm L Z t j) :=
  Measurable.ite ((hLm.comp (hZ _)) (measurableSet_singleton _)) (hZ _) measurable_const

theorem measurable_echoProcess (hZ : ∀ t, Measurable (Z t)) (hLm : Measurable L) (t : ℤ) :
    Measurable (echoProcess L Z t) :=
  (hZ t).max (Measurable.iSup fun j => measurable_echoTerm hZ hLm t j)

theorem le_echoProcess (t : ℤ) (ω : Ω) : Z t ω ≤ echoProcess L Z t ω := le_max_left _ _

theorem echoProcess_nonneg (hpos : ∀ t ω, 0 ≤ Z t ω) (t : ℤ) (ω : Ω) :
    0 ≤ echoProcess L Z t ω := (hpos t ω).trans (le_echoProcess t ω)

/-- The echo process is a shift functional of the innovations. -/
theorem echoProcess_eq_shift : echoProcess L Z = fun t ω => (fun z : ℤ → ℝ =>
    max (z 0) (⨆ j : ℕ, if L (z (-(j + 1))) = j + 1 then z (-(j + 1)) else 0))
      (fun i => Z (t + i) ω) := by
  funext t ω
  simp only [echoProcess, echoTerm, add_zero, ← sub_eq_add_neg]

/-- **Upper inclusion**: an exceedance of `x ≥ 0` at time `t` has a source. -/
theorem setOf_lt_echoProcess_subset {x : ℝ} (hx : 0 ≤ x) (t : ℤ) :
    {ω | x < echoProcess L Z t ω} ⊆ ⋃ j, echoSource L Z t x j := by
  intro ω hω
  simp only [mem_ofPred_eq, echoProcess, lt_max_iff] at hω
  rcases hω with hω | hω
  · exact mem_iUnion.2 ⟨0, by simpa [echoSource] using hω⟩
  · by_cases hb : BddAbove (range fun j => echoTerm L Z t j ω)
    · obtain ⟨j, hj⟩ := exists_lt_of_lt_ciSup hω
      simp only [echoTerm] at hj
      split_ifs at hj with hL
      · refine mem_iUnion.2 ⟨j + 1, ?_⟩
        simp only [echoSource, mem_ofPred_eq, Nat.cast_add, Nat.cast_one]
        exact ⟨hj, Or.inr hL⟩
      · exact absurd hj (not_lt.2 hx)
    · rw [Real.iSup_of_not_bddAbove hb] at hω
      exact absurd hω (not_lt.2 hx)

/-- **Lower inclusion**, when the echoes into `t` are bounded (almost surely, see
`ae_bddAbove_echoTerm`). -/
theorem lt_echoProcess_of_mem_echoSource {t : ℤ} {x : ℝ} {j : ℕ} {ω : Ω}
    (hb : BddAbove (range fun j => echoTerm L Z t j ω)) (hω : ω ∈ echoSource L Z t x j) :
    x < echoProcess L Z t ω := by
  obtain ⟨h1, h2⟩ := hω
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h1' : x < Z t ω := by simpa using h1
    exact h1'.trans_le (le_echoProcess t ω)
  · replace h2 : L (Z (t - j) ω) = j := h2.resolve_left hj.ne'
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hterm : echoTerm L Z t k ω = Z (t - (k + 1)) ω := by
      have h2' : L (Z (t - (k + 1)) ω) = k + 1 := by exact_mod_cast h2
      simp [echoTerm, h2']
    refine lt_max_of_lt_right (lt_of_lt_of_le ?_ (le_ciSup hb k))
    rw [hterm]
    exact_mod_cast h1

variable (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω) (hLm : Measurable L)
  (hL1 : ∀ z, 1 ≤ L z)

include hZ hlaw in
omit [IsProbabilityMeasure P] in
theorem measureReal_preimage_eq (t : ℤ) {s : Set ℝ} (hs : MeasurableSet s) :
    P.real (Z t ⁻¹' s) = (paretoMeasure 1 α).real s := by
  rw [← map_measureReal_apply (hZ t) hs, hlaw]

include hZ hlaw in
omit [IsProbabilityMeasure P] in
theorem measure_preimage_eq (t : ℤ) {s : Set ℝ} (hs : MeasurableSet s) :
    P (Z t ⁻¹' s) = paretoMeasure 1 α s := by
  rw [← Measure.map_apply (hZ t) hs, hlaw]

include hα hZ hlaw hLm in
omit [IsProbabilityMeasure P] in
/-- **Almost surely, only finitely many innovations echo into a given time** (Borel–Cantelli:
`∑ⱼ P(L(Z_{t - j}) = j) = ∑ⱼ P(L(Z_0) = j) ≤ 1`). -/
theorem ae_bddAbove_echoTerm :
    ∀ᵐ ω ∂P, ∀ t, BddAbove (range fun j => echoTerm L Z t j ω) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  rw [ae_all_iff]
  intro t
  set s : ℕ → Set Ω := fun j => {ω | L (Z (t - (j + 1)) ω) = j + 1}
  have hs : ∀ j, P (s j) = paretoMeasure 1 α (L ⁻¹' {j + 1}) := fun j =>
    measure_preimage_eq hZ hlaw _ (hLm (measurableSet_singleton _))
  have hsum : ∑' j, P (s j) ≠ ∞ := by
    rw [tsum_congr hs, ← measure_iUnion]
    · exact measure_ne_top _ _
    · intro i j hij
      exact Disjoint.preimage _ (Set.disjoint_singleton.2 (by omega))
    · exact fun j => hLm (measurableSet_singleton _)
  have hae : ∀ᵐ ω ∂P, ω ∉ limsup s atTop :=
    measure_eq_zero_iff_ae_notMem.1 (measure_limsup_atTop_eq_zero hsum)
  filter_upwards [hae] with ω hω
  rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently] at hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨max (Finset.sup' (Finset.range (N + 1)) Finset.nonempty_range_add_one
    fun j => echoTerm L Z t j ω) 0, ?_⟩
  rintro _ ⟨j, rfl⟩
  by_cases hj : j ≤ N
  · exact le_max_of_le_left (Finset.le_sup' (fun j => echoTerm L Z t j ω)
      (Finset.mem_range.2 (by omega)))
  · have : echoTerm L Z t j ω = 0 := by
      rw [echoTerm, ite_eq_right_iff]
      exact fun h => absurd h (hN j (by omega))
    show echoTerm L Z t j ω ≤ _
    rw [this]
    exact le_max_right _ _

end Echo

end ExtremeValueTheory
