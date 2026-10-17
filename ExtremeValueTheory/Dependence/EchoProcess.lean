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

include hα hLm hL1 in
/-- The source probabilities at level `x ≥ 1` sum to `2 x^(-α)`: the innovation itself and its
echo. -/
theorem hasSum_measureReal_echoSourceSet {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun j => (paretoMeasure 1 α).real (echoSourceSet L x j)) (2 * x ^ (-α)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set ν := paretoMeasure 1 α
  set b : ℕ → ℝ := fun j => ν.real {z | x < z ∧ L z = j}
  have hb : HasSum b (x ^ (-α)) := by
    have hU : (⋃ j, {z : ℝ | x < z ∧ L z = j}) = Ioi x := by
      ext z
      simp
    rw [← paretoMeasure_one_real_Ioi hα hx, ← hU]
    refine hasSum_measureReal_iUnion (fun j => measurableSet_Ioi.inter
      (hLm (measurableSet_singleton j))) fun i j hij => ?_
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨-, hi⟩ ⟨-, hj⟩
    exact hij (hi.symm.trans hj)
  have hb0 : b 0 = 0 := by
    have : {z : ℝ | x < z ∧ L z = 0} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ h
      have := hL1 z
      omega
    simp [b, this]
  have hsum := hb.add (hasSum_ite_eq 0 (x ^ (-α)))
  rw [show x ^ (-α) + x ^ (-α) = 2 * x ^ (-α) by ring] at hsum
  refine hsum.congr_fun fun j => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [hb0, ↓reduceIte, zero_add, echoSourceSet, true_or, and_true]
    exact paretoMeasure_one_real_Ioi hα hx
  · simp only [b, echoSourceSet, hj.ne', false_or, ↓reduceIte, add_zero]

include hα hZ hlaw hLm hL1 in
omit [IsProbabilityMeasure P] in
theorem hasSum_measureReal_echoSource (t : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun j => P.real (echoSource L Z t x j)) (2 * x ^ (-α)) := by
  refine (hasSum_measureReal_echoSourceSet hα hLm hL1 hx).congr_fun fun j => ?_
  rw [echoSource_eq, measureReal_preimage_eq hZ hlaw _ (measurableSet_echoSourceSet hLm x j)]

include hα hZ hlaw hLm hL1 in
/-- `P(X_0 > x) ≤ 2 x^(-α)` for `x ≥ 1`. -/
theorem measureReal_lt_echoProcess_le (t : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    P.real {ω | x < echoProcess L Z t ω} ≤ 2 * x ^ (-α) := by
  have hs := hasSum_measureReal_echoSource hα hZ hlaw hLm hL1 t hx
  refine (measureReal_mono (setOf_lt_echoProcess_subset (by linarith) t)).trans ?_
  rw [← hs.tsum_eq]
  exact measureReal_iUnion_le_tsum hs.summable

include hα hZ hind hlaw hLm hL1 in
/-- `P(X_0 > x) ≥ 2 x^(-α) - 4 x^(-2α)` for `x ≥ 1` (Bonferroni over the independent sources). -/
theorem le_measureReal_lt_echoProcess (t : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    2 * x ^ (-α) - (2 * x ^ (-α)) ^ 2 ≤ P.real {ω | x < echoProcess L Z t ω} := by
  have hs := hasSum_measureReal_echoSource hα hZ hlaw hLm hL1 t hx
  have hA : ∀ j, MeasurableSet (echoSource L Z t x j) := fun j => by
    rw [echoSource_eq]
    exact hZ _ (measurableSet_echoSourceSet hLm x j)
  have hpair : ∀ i j, i ≠ j → P.real (echoSource L Z t x i ∩ echoSource L Z t x j) =
      P.real (echoSource L Z t x i) * P.real (echoSource L Z t x j) := by
    intro i j hij
    have hij' : t - (i : ℤ) ≠ t - j := by omega
    rw [echoSource_eq, echoSource_eq, measureReal_def,
      (hind.indepFun hij').measure_inter_preimage_eq_mul _ _ (measurableSet_echoSourceSet hLm x i)
        (measurableSet_echoSourceSet hLm x j), ENNReal.toReal_mul]
    rfl
  have key := le_measureReal_iUnion_of_pairwise hA hpair hs.summable
  rw [hs.tsum_eq] at key
  refine key.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_))
  filter_upwards [ae_bddAbove_echoTerm hα hZ hlaw hLm] with ω hω hmem
  obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
  exact lt_echoProcess_of_mem_echoSource (hω t) hj

include hα hZ hind hlaw hLm hL1 in
/-- `P(X_t > x) / x^(-α) → 2`. -/
theorem tendsto_measureReal_lt_echoProcess_div (t : ℤ) :
    Tendsto (fun x => P.real {ω | x < echoProcess L Z t ω} / x ^ (-α)) atTop (𝓝 2) := by
  have hy := tendsto_rpow_neg_atTop hα
  have hlow : Tendsto (fun x : ℝ => 2 - 4 * x ^ (-α)) atTop (𝓝 2) := by
    simpa using (hy.const_mul 4).const_sub 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have h0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    rw [le_div_iff₀ h0]
    nlinarith [le_measureReal_lt_echoProcess hα hZ hind hlaw hLm hL1 t hx]
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have h0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    rw [div_le_iff₀ h0]
    exact measureReal_lt_echoProcess_le hα hZ hlaw hLm hL1 t hx

include hα hZ hind hlaw hpos hLm hL1 in
/-- The echo process is regularly varying with index `-α`. -/
theorem isRegularlyVarying_echoProcess :
    IsRegularlyVarying (fun x => P.real {ω | x < |echoProcess L Z 0 ω|}) (-α) := by
  have h := (IsRegularlyVarying.rpow_id (-α)).of_tendsto_div
    (tendsto_measureReal_lt_echoProcess_div hα hZ hind hlaw hLm hL1 0) two_pos
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [abs_of_nonneg (echoProcess_nonneg hpos _ _)]

include hind in
omit [IsProbabilityMeasure P] in
/-- Two sources of exceedances at times `0` and `t ≠ 0` are either distinct innovations
(independent) or the same innovation, which then has echo lag `|t|`; the latter is impossible
above a level `z₀` beyond which all echo lags exceed `|t|`. -/
theorem measure_echoSource_inter_le {t : ℤ} (ht : t ≠ 0) {z₀ : ℝ}
    (hz₀ : ∀ z, z₀ ≤ z → t.natAbs < L z) (hLm : Measurable L) {x y : ℝ} (hx : z₀ ≤ x)
    (j j' : ℕ) :
    P (echoSource L Z 0 x j ∩ echoSource L Z t y j') ≤
      P (echoSource L Z 0 x j) * P (echoSource L Z t y j') := by
  by_cases h : (0 : ℤ) - j = t - j'
  · have hempty : echoSource L Z 0 x j ∩ echoSource L Z t y j' = ∅ := by
      ext ω
      simp only [echoSource, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
        not_and]
      rintro ⟨h1, h2⟩ _ h4
      rw [← h] at h4
      have hL := hz₀ _ (hx.trans h1.le)
      rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4 <;> omega
    rw [hempty, measure_empty]
    exact zero_le
  · rw [echoSource_eq, echoSource_eq]
    exact le_of_eq ((hind.indepFun h).measure_inter_preimage_eq_mul _ _
      (measurableSet_echoSourceSet hLm x j) (measurableSet_echoSourceSet hLm y j'))

include hα hZ hind hlaw hLm hL1 in
/-- **Pair bound**: for `t ≠ 0`, `P(X_0 > x, X_t > y) ≤ 2 x^(-α) · 2 y^(-α)` for `x` large and
`y ≥ 1`. -/
theorem eventually_measureReal_lt_echoProcess_inter_le (hLinf : Tendsto L atTop atTop) {t : ℤ}
    (ht : t ≠ 0) : ∃ z₀ : ℝ, ∀ x y : ℝ, z₀ ≤ x → 1 ≤ y →
      P.real {ω | x < echoProcess L Z 0 ω ∧ y < echoProcess L Z t ω} ≤
        2 * x ^ (-α) * (2 * y ^ (-α)) := by
  obtain ⟨z₁, hz₁⟩ := eventually_atTop.1 (hLinf.eventually_gt_atTop t.natAbs)
  refine ⟨max z₁ 1, fun x y hx hy => ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hsx := hasSum_measureReal_echoSource hα hZ hlaw hLm hL1 0 hx1
  have hsy := hasSum_measureReal_echoSource hα hZ hlaw hLm hL1 t hy
  have htsum : ∀ (s : ℤ) (w : ℝ) (c : ℝ),
      HasSum (fun j => P.real (echoSource L Z s w j)) c →
        ∑' j, P (echoSource L Z s w j) = ENNReal.ofReal c := by
    intro s w c hc
    rw [← hc.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hc.summable]
    exact tsum_congr fun j => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hsub : {ω | x < echoProcess L Z 0 ω ∧ y < echoProcess L Z t ω} ⊆
      ⋃ j, ⋃ j', echoSource L Z 0 x j ∩ echoSource L Z t y j' := by
    intro ω ⟨h1, h2⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (by linarith) 0 h1)
    obtain ⟨j', hj'⟩ := mem_iUnion.1 (setOf_lt_echoProcess_subset (by linarith) t h2)
    exact mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨j', hj, hj'⟩⟩
  have hbound : P {ω | x < echoProcess L Z 0 ω ∧ y < echoProcess L Z t ω} ≤
      ENNReal.ofReal (2 * x ^ (-α)) * ENNReal.ofReal (2 * y ^ (-α)) := by
    calc _ ≤ P (⋃ j, ⋃ j', echoSource L Z 0 x j ∩ echoSource L Z t y j') := measure_mono hsub
      _ ≤ ∑' j, ∑' j', P (echoSource L Z 0 x j ∩ echoSource L Z t y j') :=
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => measure_iUnion_le _)
      _ ≤ ∑' j, ∑' j', P (echoSource L Z 0 x j) * P (echoSource L Z t y j') :=
          ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun j' =>
            measure_echoSource_inter_le hind ht (fun z hz => hz₁ z hz) hLm
              ((le_max_left _ _).trans hx) j j'
      _ = (∑' j, P (echoSource L Z 0 x j)) * ∑' j', P (echoSource L Z t y j') := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun j => ENNReal.tsum_mul_left
      _ = _ := by rw [htsum 0 x _ hsx, htsum t y _ hsy]
  have hpos1 : 0 ≤ 2 * x ^ (-α) := by positivity
  have hpos2 : 0 ≤ 2 * y ^ (-α) := by positivity
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rwa [ENNReal.ofReal_mul hpos1]

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The echo process is asymptotically independent at every fixed lag**: the echo of a large
innovation comes at lag `L(Z) → ∞`. -/
theorem tendsto_echoProcess_cond (hLinf : Tendsto L atTop atTop) {t : ℤ} (ht : t ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x => P.real {ω | x < |echoProcess L Z 0 ω| ∧ ε * x < |echoProcess L Z t ω|} /
      P.real {ω | x < |echoProcess L Z 0 ω|}) atTop (𝓝 0) := by
  obtain ⟨z₀, hz₀⟩ := eventually_measureReal_lt_echoProcess_inter_le hα hZ hind hlaw hLm hL1
    hLinf ht
  have hlim : Tendsto (fun x : ℝ => 4 * (ε * x) ^ (-α)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hα).comp
      (tendsto_id.const_mul_atTop hε)).const_mul 4
  refine squeeze_zero' (Eventually.of_forall fun x => div_nonneg measureReal_nonneg
    measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop z₀, eventually_ge_atTop 1,
    eventually_ge_atTop (1 / ε)] with x hxz hx1 hxε
  have hεx : 1 ≤ ε * x := by rwa [div_le_iff₀' hε] at hxε
  simp only [abs_of_nonneg (echoProcess_nonneg hpos _ _)]
  have h0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
  have hlow : x ^ (-α) ≤ P.real {ω | x < echoProcess L Z 0 ω} := by
    rw [← measureReal_lt_of_map_eq hZ hlaw hα 0 hx1]
    exact measureReal_mono fun ω hω => lt_of_lt_of_le hω (le_echoProcess 0 ω)
  rw [div_le_iff₀ (h0.trans_le hlow)]
  calc _ ≤ 2 * x ^ (-α) * (2 * (ε * x) ^ (-α)) := hz₀ x (ε * x) hxz hεx
    _ = 4 * (ε * x) ^ (-α) * x ^ (-α) := by ring
    _ ≤ _ := by gcongr

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The spectral tail process of the echo process is trivial**: `Θ_t = 1{t = 0}`. -/
theorem hasSpectralTailProcess_echoProcess (hLinf : Tendsto L atTop atTop) :
    HasSpectralTailProcess P (echoProcess L Z) α (Measure.dirac ()) unitSpectral :=
  hasSpectralTailProcess_of_asymptoticIndependence (measurable_echoProcess hZ hLm)
    (echoProcess_nonneg hpos 0) (isRegularlyVarying_echoProcess hα hZ hind hlaw hpos hLm hL1)
    fun _ ht _ hε => tendsto_echoProcess_cond hα hZ hind hlaw hpos hLm hL1 hLinf ht hε

/-- **The candidate extremal index of the echo process is `ϑ = 1`.** -/
theorem candidateExtremalIndex_unitSpectral (hα : 0 < α) :
    candidateExtremalIndex (Measure.dirac ()) unitSpectral α = 1 :=
  candidateExtremalIndex_eq_one hα (by simp [unitSpectral])
    fun k => by simp [unitSpectral]; omega

/-- The event that some innovation before time `0` exceeds `u` and echoes at or after time `0`. -/
def echoIntoFuture (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (u : ℝ) : Set Ω :=
  ⋃ j : ℕ, Z (-(j + 1)) ⁻¹' {z | u < z ∧ j + 1 ≤ L z}

include hα in
/-- The mass of the echoes into the future vanishes when `L(Z)` has a finite mean:
`∑ⱼ P(Z > u, L(Z) ≥ j + 1) = E[L(Z); Z > u] → 0`. -/
theorem tendsto_tsum_echoIntoFuture
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z}) :
    Tendsto (fun u => ∑' j : ℕ, (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z}) atTop
      (𝓝 0) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun _ : ℕ => (0 : ℝ))
    (f := fun u j => (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z}) hLsum ?_ ?_
  · simpa using h
  · intro j
    refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
      (tendsto_rpow_neg_atTop hα)
    filter_upwards [eventually_ge_atTop 1] with u hu
    rw [← paretoMeasure_one_real_Ioi hα hu]
    exact measureReal_mono fun z hz => hz.1
  · exact Eventually.of_forall fun u j => by
      rw [Real.norm_of_nonneg measureReal_nonneg]
      exact measureReal_mono fun z hz => hz.2

include hα hZ hlaw hLm in
theorem measureReal_echoIntoFuture_le
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z}) (u : ℝ) :
    P.real (echoIntoFuture L Z u) ≤
      ∑' j : ℕ, (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hm : ∀ j : ℕ, MeasurableSet {z : ℝ | u < z ∧ j + 1 ≤ L z} := fun j =>
    measurableSet_Ioi.inter (hLm measurableSet_Ici)
  have heq : ∀ j : ℕ, P.real (Z (-(j + 1)) ⁻¹' {z | u < z ∧ j + 1 ≤ L z}) =
      (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z} := fun j =>
    measureReal_preimage_eq hZ hlaw _ (hm j)
  have hs : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | u < z ∧ j + 1 ≤ L z} :=
    hLsum.of_nonneg_of_le (fun _ => measureReal_nonneg) fun j => measureReal_mono fun z hz => hz.2
  rw [echoIntoFuture]
  simp_rw [← heq] at hs ⊢
  exact measureReal_iUnion_le_tsum hs

omit [IsProbabilityMeasure P] in
/-- **No exceedance up to time `n`**: if no innovation at times `0, …, n - 1` exceeds `u ≥ 0` and
no earlier innovation above `u` echoes at or after time `0`, then `M n ≤ u`. -/
theorem partialMax_echoProcess_le {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) {ω : Ω}
    (h1 : ∀ k < n, Z k ω ≤ u) (h2 : ω ∉ echoIntoFuture L Z u) :
    partialMax (fun k : ℕ => echoProcess L Z k) n ω ≤ u := by
  rw [partialMax_le_iff hn]
  intro k hk
  refine max_le (h1 k hk) (ciSup_le fun j => ?_)
  simp only [echoTerm]
  split_ifs with hL
  · by_cases hkj : (j : ℤ) + 1 ≤ k
    · obtain ⟨k', hk'⟩ : ∃ k' : ℕ, (k : ℤ) - (j + 1) = k' := ⟨k - (j + 1), by omega⟩
      rw [hk']
      exact h1 k' (by omega)
    · obtain ⟨i, hi⟩ : ∃ i : ℕ, (k : ℤ) - (j + 1) = -(i + 1) := ⟨j - k, by omega⟩
      rw [hi]
      rw [hi] at hL
      by_contra hcon
      exact h2 (mem_iUnion.2 ⟨i, not_le.1 hcon, by omega⟩)
  · exact hu

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The extremal index of the echo process is `θ = 1/2`**, provided the echo lag of an
innovation has finite mean, `E[L(Z)] = ∑ⱼ P(L(Z) ≥ j + 1) < ∞`, and grows to infinity with the
innovation. Each exceedance cluster consists of two exceedances, an innovation and its echo,
`L(Z)` time units later; since `E[L(Z); Z > uₙ] → 0`, the echoes of innovations before time `0`
are negligible and `P(M n ≤ uₙ) ≈ P(Z ≤ uₙ)^n → exp (-τ / 2)`. -/
theorem hasExtremalIndex_echoProcess (hLinf : Tendsto L atTop atTop)
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z}) :
    HasExtremalIndex (fun k : ℕ => echoProcess L Z k) P (1 / 2) := by
  have hT := hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos hLm hL1 hLinf
  refine ⟨⟨by norm_num, by norm_num⟩, fun τ hτ u hu => ?_⟩
  have hu' : Tendsto (fun n : ℕ => n * P.real {ω | u n < |echoProcess L Z 0 ω|}) atTop (𝓝 τ) := by
    simpa [abs_of_nonneg (echoProcess_nonneg hpos _ _)] using hu
  have hu0 : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess L Z 0 ω}) atTop (𝓝 τ) := by
    simpa using hu
  have hinf := hT.tendsto_atTop_of_tendsto_mul hu'
  -- `n uₙ^(-α) → τ / 2`
  set b : ℕ → ℝ := fun n => u n ^ (-α)
  have hratio := (tendsto_measureReal_lt_echoProcess_div hα hZ hind hlaw hLm hL1 0).comp hinf
  have hnb : Tendsto (fun n : ℕ => (n : ℝ) * b n) atTop (𝓝 (τ / 2)) := by
    refine (hu0.div hratio two_ne_zero).congr' ?_
    filter_upwards [hinf.eventually_ge_atTop 1] with n hn
    have h0 : 0 < u n ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
    have hP : 0 < P.real {ω | u n < echoProcess L Z 0 ω} := by
      refine h0.trans_le ?_
      rw [← measureReal_lt_of_map_eq hZ hlaw hα 0 hn]
      exact measureReal_mono fun ω hω => lt_of_lt_of_le hω (le_echoProcess 0 ω)
    simp only [Pi.div_apply, Function.comp_apply, b]
    field_simp
  have hb : Tendsto b atTop (𝓝 0) := (tendsto_rpow_neg_atTop hα).comp hinf
  have hpow := tendsto_one_sub_pow_exp_of_tendsto_mul (k := fun n => n) hb hnb
  rw [show -(τ / 2) = -(1 / 2 * τ) by ring] at hpow
  -- the iid part
  have hidZ : ∀ k : ℕ, IdentDistrib (Z k) (Z ((0 : ℕ) : ℤ)) P P := fun k =>
    ⟨(hZ _).aemeasurable, (hZ _).aemeasurable, by rw [hlaw, hlaw]⟩
  have hindN : iIndepFun (fun k : ℕ => Z k) P :=
    hind.precomp (g := fun k : ℕ => (k : ℤ)) Nat.cast_injective
  have hiid : ∀ n, 1 ≤ u n → P.real (maxLE (fun k : ℕ => Z k) (Finset.range n) (u n)) =
      (1 - b n) ^ n := by
    intro n hn
    rw [measureReal_maxLE_of_iIndepFun hindN hidZ, Finset.card_range]
    congr 1
    have hc : {ω | Z ((0 : ℕ) : ℤ) ω ≤ u n} = {ω | u n < Z 0 ω}ᶜ := by
      ext ω; simp
    rw [hc, probReal_compl_eq_one_sub (measurableSet_lt measurable_const (hZ 0)),
      measureReal_lt_of_map_eq hZ hlaw hα 0 hn]
  have hR := (tendsto_tsum_echoIntoFuture hα hLsum).comp hinf
  have hlow : Tendsto (fun n => (1 - b n) ^ n -
      ∑' j : ℕ, (paretoMeasure 1 α).real {z | u n < z ∧ j + 1 ≤ L z}) atTop
        (𝓝 (Real.exp (-(1 / 2 * τ)))) := by
    simpa using hpow.sub hR
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hpow ?_ ?_
  · filter_upwards [hinf.eventually_ge_atTop 1, eventually_gt_atTop 0] with n hn hn0
    rw [← hiid n hn]
    have hsub : maxLE (fun k : ℕ => Z k) (Finset.range n) (u n) \ echoIntoFuture L Z (u n) ⊆
        {ω | partialMax (fun k : ℕ => echoProcess L Z k) n ω ≤ u n} := by
      rintro ω ⟨h1, h2⟩
      exact partialMax_echoProcess_le hn0 (by linarith) (fun k hk => h1 k (Finset.mem_range.2 hk))
        h2
    have := measureReal_echoIntoFuture_le hα hZ hlaw hLm hLsum (P := P) (u n)
    have h3 : P.real (maxLE (fun k : ℕ => Z k) (Finset.range n) (u n)) ≤
        P.real (maxLE (fun k : ℕ => Z k) (Finset.range n) (u n) \ echoIntoFuture L Z (u n)) +
          P.real (echoIntoFuture L Z (u n)) := by
      refine (measureReal_mono (fun ω hω => ?_)).trans (measureReal_union_le _ _)
      by_cases h : ω ∈ echoIntoFuture L Z (u n)
      · exact Or.inr h
      · exact Or.inl ⟨hω, h⟩
    linarith [measureReal_mono (μ := P) hsub]
  · filter_upwards [hinf.eventually_ge_atTop 1, eventually_gt_atTop 0] with n hn hn0
    rw [← hiid n hn]
    refine measureReal_mono fun ω hω t ht => ?_
    have := (partialMax_le_iff hn0).1 hω t (Finset.mem_range.1 ht)
    exact (le_echoProcess (L := L) t ω).trans this

include hZ hind hlaw hLm in
/-- The echo process is stationary. -/
theorem hasShiftInvariantWindows_echoProcess : HasShiftInvariantWindows P (echoProcess L Z) := by
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i =>
    ⟨(hZ _).aemeasurable, (hZ _).aemeasurable, by rw [hlaw, hlaw]⟩
  have hG : Measurable fun z : ℤ → ℝ =>
      max (z 0) (⨆ j : ℕ, if L (z (-(j + 1))) = j + 1 then z (-(j + 1)) else 0) :=
    (measurable_pi_apply 0).max (Measurable.iSup fun j =>
      Measurable.ite ((hLm.comp (measurable_pi_apply _)) (measurableSet_singleton _))
        (measurable_pi_apply _) measurable_const)
  rw [echoProcess_eq_shift]
  exact hasShiftInvariantWindows_of_shift hZ hind hid hG

include hα hZ hind hlaw hpos hLm hL1 in
/-- **The echo process has `θ = 1/2 < 1 = ϑ`.** For iid Pareto(`α`) innovations and an echo lag
`L ≥ 1` with `L(z) → ∞` and `E[L(Z)] < ∞`, the echo process is stationary, its spectral tail
process is `Θ_t = 1{t = 0}` (so `ϑ = 1`), and its extremal index is `1/2`. -/
theorem echoProcess_theta_lt_vartheta (hLinf : Tendsto L atTop atTop)
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z}) :
    HasShiftInvariantWindows P (echoProcess L Z) ∧
      HasSpectralTailProcess P (echoProcess L Z) α (Measure.dirac ()) unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      HasExtremalIndex (fun k : ℕ => echoProcess L Z k) P (1 / 2) :=
  ⟨hasShiftInvariantWindows_echoProcess hZ hind hlaw hLm,
    hasSpectralTailProcess_echoProcess hα hZ hind hlaw hpos hLm hL1 hLinf,
    by rw [candidateExtremalIndex_unitSpectral hα]; rfl,
    hasExtremalIndex_echoProcess hα hZ hind hlaw hpos hLm hL1 hLinf hLsum⟩

end Echo

/-! ### A concrete echo lag: `L(z) = ⌊log z⌋ + 1` -/

section LogLag

/-- The logarithmic echo lag `L(z) = ⌊log z⌋₊ + 1`. -/
noncomputable def logLag (z : ℝ) : ℕ := ⌊Real.log z⌋₊ + 1

theorem measurable_logLag : Measurable logLag := by
  show Measurable ((fun n : ℕ => n + 1) ∘ fun z => ⌊Real.log z⌋₊)
  exact measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_log)

theorem one_le_logLag (z : ℝ) : 1 ≤ logLag z := Nat.le_add_left 1 _

theorem tendsto_logLag : Tendsto logLag atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_succ _)
    (tendsto_nat_floor_atTop.comp Real.tendsto_log_atTop)

/-- `E[L(Z)] < ∞` for the logarithmic lag: `P(L(Z) ≥ j + 1) ≤ 2^α e^(-α j)`. -/
theorem summable_logLag {α : ℝ} (hα : 0 < α) :
    Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ logLag z} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hgeo : Summable fun j : ℕ => (2 : ℝ) ^ α * Real.exp (-α) ^ j :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by linarith))).mul_left _
  refine hgeo.of_nonneg_of_le (fun _ => measureReal_nonneg) fun j => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [pow_zero, mul_one]
    exact measureReal_le_one.trans (Real.one_le_rpow (by norm_num) hα.le)
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have he : 1 ≤ Real.exp j / 2 := by
      have := Real.add_one_le_exp (j : ℝ)
      linarith
    calc (paretoMeasure 1 α).real {z | j + 1 ≤ logLag z}
        ≤ (paretoMeasure 1 α).real (Ioi (Real.exp j / 2)) := by
          refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
          filter_upwards [ae_one_lt_paretoMeasure (α := α)] with z hz1 hz
          have hz' : j ≤ ⌊Real.log z⌋₊ := by simpa [logLag] using hz
          have hlog : (j : ℝ) ≤ Real.log z :=
            (Nat.cast_le.2 hz').trans (Nat.floor_le (Real.log_pos hz1).le)
          have := (Real.exp_le_exp.2 hlog).trans_eq (Real.exp_log (by linarith))
          show Real.exp j / 2 < z
          linarith [Real.exp_pos (j : ℝ)]
      _ = (Real.exp j / 2) ^ (-α) := paretoMeasure_one_real_Ioi hα he
      _ = Real.exp j ^ (-α) / 2 ^ (-α) := Real.div_rpow (Real.exp_pos _).le (by norm_num) _
      _ = Real.exp (j * -α) * 2 ^ α := by
          rw [← Real.exp_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      _ = 2 ^ α * Real.exp (-α) ^ j := by
          rw [← Real.exp_nat_mul]
          ring_nf

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ}

/-- **A fully explicit example of `θ < ϑ`**: with iid Pareto(`α`) innovations and the echo lag
`L(z) = ⌊log z⌋₊ + 1`, the echo process `X_t = max(Z_t, max {Z_s : s + L(Z_s) = t})` is
stationary with spectral tail process `Θ_t = 1{t = 0}`, so `ϑ = 1`, while its extremal index is
`θ = 1/2`. -/
theorem logEchoProcess_theta_lt_vartheta (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) :
    HasShiftInvariantWindows P (echoProcess logLag Z) ∧
      HasSpectralTailProcess P (echoProcess logLag Z) α (Measure.dirac ()) unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      HasExtremalIndex (fun k : ℕ => echoProcess logLag Z k) P (1 / 2) :=
  echoProcess_theta_lt_vartheta hα hZ hind hlaw hpos measurable_logLag one_le_logLag
    tendsto_logLag (summable_logLag hα)

end LogLag

end ExtremeValueTheory
