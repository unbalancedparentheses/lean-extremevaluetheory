/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.TailProcess

/-!
# The time-change formula

For a stationary jointly regularly varying time series with spectral tail process `(Θ_t)`, the
*time-change formula* ([BS09, Theorem 3.1], [KS20, Theorem 5.3.1]) states that for every `i ∈ ℤ`,
every finite window `S ⊆ ℤ` and every measurable `h ≥ 0`,
`E[h((Θ_{t-i})_{t ∈ S}) 1{Θ_{-i} ≠ 0}] = E[h((Θ_t / |Θ_i|)_{t ∈ S}) |Θ_i|^α]`.

We first prove the tail-process form ([BS09, Theorem 3.1 (ii)]): with `Y_t = R Θ_t`, `R` Pareto(`α`)
independent of `(Θ_t)`, for every `ε > 0` and bounded continuous `H`,
`E[H((Y_{t-i})_{t ∈ S}) 1{|Y_{-i}| > ε}] = ε^(-α) E[H((ε Y_t)_{t ∈ S}) 1{|Y_i| > 1/ε}]`.
It follows from stationarity, shifting the window by `i`, and from regular variation of
`P(|X_0| > x)`, comparing the conditioning levels `x` and `εx`. The two sides are then finite
measures which agree on bounded continuous functions, hence agree, and the formula for `Θ` follows
by integrating out `R` and letting `ε → 0`.

## Main definitions

* `ExtremeValueTheory.HasShiftInvariantWindows P X`: strict stationarity of `(X_t)_{t ∈ ℤ}`,
  phrased through finite windows.

## Main results

* `ExtremeValueTheory.HasSpectralTailProcess.integral_tailProcess_shift`: the tail-process form.
* `ExtremeValueTheory.HasSpectralTailProcess.lintegral_timeChange`: the time-change formula.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

/-! ### Windows and stationarity -/

/-- Coordinate `t` of a window vector `y : S → ℝ`, and `0` if `t ∉ S`. -/
noncomputable def readW {S : Finset ℤ} (y : S → ℝ) (t : ℤ) : ℝ :=
  if h : t ∈ S then y ⟨t, h⟩ else 0

theorem continuous_readW (S : Finset ℤ) (t : ℤ) : Continuous fun y : S → ℝ => readW y t := by
  unfold readW
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

theorem measurable_readW (S : Finset ℤ) (t : ℤ) : Measurable fun y : S → ℝ => readW y t :=
  (continuous_readW S t).measurable

theorem measurable_abs_readW (S : Finset ℤ) (t : ℤ) :
    Measurable fun y : S → ℝ => |readW y t| :=
  continuous_abs.measurable.comp (measurable_readW S t)

@[simp]
theorem readW_mk {S : Finset ℤ} (f : ℤ → ℝ) {t : ℤ} (ht : t ∈ S) :
    readW (fun s : S => f s) t = f t := by
  simp [readW, ht]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}

/-- Strict stationarity of a time series `(X_t)_{t ∈ ℤ}`: the law of every finite window is
invariant under time shifts. (Named to avoid a clash with other stationarity notions.) -/
def HasShiftInvariantWindows (P : Measure Ω) (X : ℤ → Ω → ℝ) : Prop :=
  ∀ (h : ℤ) (S : Finset ℤ),
    P.map (fun ω (t : S) => X (t + h) ω) = P.map (fun ω (t : S) => X t ω)

/-- For `R` Pareto independent of `f`, `P(|R f| = c) = 0` for `c ≠ 0`. -/
theorem prod_abs_mul_eq_null {α : ℝ} (hα : 0 < α) {Q : Measure Ω'} [SFinite Q] {f : Ω' → ℝ}
    (hf : Measurable f) {c : ℝ} (hc : c ≠ 0) :
    ((paretoMeasure 1 α).prod Q) {p | |p.1 * f p.2| = c} = 0 := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hm : MeasurableSet {p : ℝ × Ω' | |p.1 * f p.2| = c} :=
    measurableSet_eq_fun (continuous_abs.measurable.comp
      (measurable_fst.mul (hf.comp measurable_snd))) measurable_const
  rw [Measure.prod_apply_symm hm]
  refine (lintegral_congr fun ω' => ?_).trans lintegral_zero
  by_cases ha : f ω' = 0
  · have : (fun r : ℝ => (r, ω')) ⁻¹' {p : ℝ × Ω' | |p.1 * f p.2| = c} = ∅ := by
      ext r; simp [ha, eq_comm, hc]
    rw [this, measure_empty]
  · refine measure_mono_null (t := {c / f ω'} ∪ {-c / f ω'}) (fun r hr => ?_)
      (measure_union_null (paretoMeasure_singleton _ _) (paretoMeasure_singleton _ _))
    have hr : |r * f ω'| = c := hr
    rcases (abs_eq ((abs_nonneg (r * f ω')).trans_eq hr)).1 hr with h | h
    · left; simp only [mem_singleton_iff]; field_simp; linarith
    · right; simp only [mem_singleton_iff]; field_simp; linarith

/-! ### The tail-process form -/

section TailForm

variable {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

omit [IsProbabilityMeasure P] in
/-- Stationarity, applied to the integral of a bounded measurable function of a window. -/
theorem HasShiftInvariantWindows.integral_comp (hstat : HasShiftInvariantWindows P X)
    (hX : ∀ t, Measurable (X t)) (h : ℤ) (W : Finset ℤ) {G : (W → ℝ) → ℝ}
    (hG : Measurable G) :
    ∫ ω, G (fun t : W => X (t + h) ω) ∂P = ∫ ω, G (fun t : W => X t ω) ∂P := by
  have h1 : Measurable fun ω (t : W) => X (t + h) ω := measurable_pi_iff.2 fun t => hX _
  have h2 : Measurable fun ω (t : W) => X t ω := measurable_pi_iff.2 fun t => hX _
  rw [← integral_map h1.aemeasurable hG.aestronglyMeasurable,
    ← integral_map h2.aemeasurable hG.aestronglyMeasurable, hstat h W]

/-- **Time change, tail-process form, bounded continuous version** ([BS09, Theorem 3.1 (ii)]).
For a stationary series with spectral tail process `Θ`, writing `Y_t = R Θ_t` with `R`
Pareto(`α`) independent of `Θ`: for every `i`, every window `S`, every `ε > 0` and every bounded
continuous `H`,
`E[H((Y_{t-i})_{t ∈ S}) 1{|Y_{-i}| > ε}] = ε^(-α) E[H((ε Y_t)_{t ∈ S}) 1{|Y_i| > 1/ε}]`.
Uses stationarity (`HasShiftInvariantWindows`), regular variation of `|X_0|` and the window
convergence of the spectral tail process. -/
theorem HasSpectralTailProcess.integral_tailProcess_shift (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) (i : ℤ)
    (S : Finset ℤ) (H : (S → ℝ) →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p, {p : ℝ × Ω' | ε < |p.1 * Θ (-i) p.2|}.indicator
        (fun p => H fun t : S => p.1 * Θ (t - i) p.2) p ∂((paretoMeasure 1 α).prod Q) =
      ε ^ (-α) * ∫ p, {p : ℝ × Ω' | 1 / ε < |p.1 * Θ i p.2|}.indicator
        (fun p => H fun t : S => ε * (p.1 * Θ t p.2)) p ∂((paretoMeasure 1 α).prod Q) := by
  classical
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q with hπ
  set W : Finset ℤ := S.image (· - i) ∪ S ∪ {0, i, -i} with hWdef
  have hW0 : (0 : ℤ) ∈ W := by simp [hWdef]
  have hWi : i ∈ W := by simp [hWdef]
  have hWmi : -i ∈ W := by simp [hWdef]
  have hWS : ∀ t ∈ S, t ∈ W := fun t ht => by simp [hWdef, ht]
  have hWSi : ∀ t ∈ S, t - i ∈ W := fun t ht => by
    simp only [hWdef, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl ⟨t, ht, rfl⟩)
  have hT := h.hasTailProcess hα hX hΘm
  set Yw : ℝ × Ω' → (W → ℝ) := fun p t => p.1 * Θ t p.2 with hYwdef
  have hYw : Measurable Yw :=
    measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm t).comp measurable_snd)
  set Xw : ℝ → Ω → (W → ℝ) := fun x ω t => X t ω / x with hXwdef
  have hXw : ∀ x, Measurable (Xw x) := fun x =>
    measurable_pi_iff.2 fun t => (hX t).div_const x
  set s : ℝ → Set Ω := fun x => {ω | x < |X 0 ω|} with hsdef
  have hZ : Measurable fun ω => |X 0 ω| := continuous_abs.measurable.comp (hX 0)
  have hs : ∀ x, MeasurableSet (s x) := fun x => measurableSet_lt measurable_const hZ
  have hpos := h.1.eventually_pos
  have hμs : ∀ᶠ x in atTop, IsProbabilityMeasure ((P[|s x]).map (Xw x)) := by
    filter_upwards [hpos] with x hx
    have := cond_isProbabilityMeasure (μ := P) (ENNReal.toReal_pos_iff.1 hx).1.ne'
    infer_instance
  have hconv : ∀ f : (W → ℝ) →ᵇ ℝ, Tendsto (fun x => ∫ y, f y ∂(P[|s x]).map (Xw x)) atTop
      (𝓝 (∫ y, f y ∂π.map Yw)) := fun f =>
    ((hT.2 W) f).congr fun x =>
      (integral_map (hXw x).aemeasurable f.continuous.aestronglyMeasurable).symm
  -- the two test functions on windows
  let A : (W → ℝ) →ᵇ ℝ := H.compContinuous
    ⟨fun y (t : S) => readW y (t - i), continuous_pi fun t => continuous_readW W _⟩
  let B : (W → ℝ) →ᵇ ℝ := H.compContinuous
    ⟨fun y (t : S) => ε * readW y t, continuous_pi fun t =>
      continuous_const.mul (continuous_readW W _)⟩
  have hnull : ∀ j ∈ W, ∀ c : ℝ, c ≠ 0 → (π.map Yw) {y | |readW y j| = c} = 0 := by
    intro j hj c hc
    rw [Measure.map_apply hYw (measurableSet_eq_fun (measurable_abs_readW W j)
      measurable_const)]
    have : Yw ⁻¹' {y | |readW y j| = c} = {p : ℝ × Ω' | |p.1 * Θ j p.2| = c} := by
      ext p
      simp only [mem_preimage, mem_ofPred_eq, hYwdef]
      rw [readW_mk (fun t => p.1 * Θ t p.2) hj]
    rw [this]
    exact prod_abs_mul_eq_null hα (hΘm j) hc
  have hA := tendsto_integral_indicator_of_forall_integral_tendsto hμs hconv A
    (continuous_readW W (-i)).abs (hnull (-i) hWmi ε hε.ne')
  have hB := (tendsto_integral_indicator_of_forall_integral_tendsto hμs hconv B
    (continuous_readW W i).abs (hnull i hWi (1 / ε) (by positivity))).comp
    (tendsto_id.const_mul_atTop hε)
  have hratio := h.1.tendsto hε
  have key := hratio.mul hB
  -- the identity before the limit
  have heq : ∀ᶠ x in atTop,
      ∫ y, {y | ε < |readW y (-i)|}.indicator A y ∂(P[|s x]).map (Xw x) =
        P.real (s (ε * x)) / P.real (s x) *
          ∫ y, {y | 1 / ε < |readW y i|}.indicator B y ∂(P[|s (ε * x)]).map (Xw (ε * x)) := by
    filter_upwards [hpos, eventually_gt_atTop 0,
      (tendsto_id.const_mul_atTop hε).eventually hpos] with x hx hx0 hεx
    simp only [id] at hεx
    have hmA : Measurable ({y : W → ℝ | ε < |readW y (-i)|}.indicator A) :=
      A.continuous.measurable.indicator (measurableSet_lt measurable_const
        (measurable_abs_readW W _))
    have hmB : Measurable ({y : W → ℝ | 1 / ε < |readW y i|}.indicator B) :=
      B.continuous.measurable.indicator (measurableSet_lt measurable_const
        (measurable_abs_readW W _))
    rw [integral_map (hXw x).aemeasurable hmA.aestronglyMeasurable,
      integral_map (hXw _).aemeasurable hmB.aestronglyMeasurable,
      integral_cond_eq, integral_cond_eq, smul_eq_mul, smul_eq_mul,
      ← integral_indicator (hs x), ← integral_indicator (hs _)]
    -- the function of the shifted window
    let G : (W → ℝ) → ℝ := fun v =>
      if x < |readW v i| ∧ ε * x < |readW v 0| then H (fun t : S => readW v t / x) else 0
    have hG : Measurable G := by
      refine Measurable.ite ?_ (H.continuous.measurable.comp (measurable_pi_iff.2 fun t =>
        (measurable_readW W _).div_const x)) measurable_const
      exact (measurableSet_lt measurable_const (measurable_abs_readW W _)).inter
        (measurableSet_lt measurable_const (measurable_abs_readW W _))
    have h1 : ∀ ω, (s x).indicator (fun ω => {y | ε < |readW y (-i)|}.indicator A (Xw x ω)) ω =
        G (fun t : W => X (t + -i) ω) := by
      intro ω
      have e1 : readW (fun t : W => X (t + -i) ω) i = X 0 ω := by
        rw [readW_mk (fun t => X (t + -i) ω) hWi]; simp
      have e2 : readW (fun t : W => X (t + -i) ω) 0 = X (-i) ω := by
        rw [readW_mk (fun t => X (t + -i) ω) hW0]; simp
      have e3 : readW (Xw x ω) (-i) = X (-i) ω / x := readW_mk (fun t => X t ω / x) hWmi
      have e4 : (fun t : S => readW (Xw x ω) (t - i)) = fun t : S =>
          readW (fun t : W => X (t + -i) ω) t / x := by
        funext t
        rw [readW_mk (fun t => X t ω / x) (hWSi t t.2),
          readW_mk (fun t => X (t + -i) ω) (hWS t t.2), sub_eq_add_neg]
      simp only [G, e1, e2, Set.indicator_apply, mem_ofPred_eq, hsdef, A,
        BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, e3, e4,
        abs_div, abs_of_pos hx0, lt_div_iff₀ hx0]
      by_cases c1 : x < |X 0 ω| <;> by_cases c2 : ε * x < |X (-i) ω| <;> simp [c1, c2]
    have h2 : ∀ ω, G (fun t : W => X t ω) =
        (s (ε * x)).indicator (fun ω => {y | 1 / ε < |readW y i|}.indicator B
          (Xw (ε * x) ω)) ω := by
      intro ω
      have e1 : readW (fun t : W => X t ω) i = X i ω := readW_mk (fun t => X t ω) hWi
      have e2 : readW (fun t : W => X t ω) 0 = X 0 ω := readW_mk (fun t => X t ω) hW0
      have e3 : readW (Xw (ε * x) ω) i = X i ω / (ε * x) :=
        readW_mk (fun t => X t ω / (ε * x)) hWi
      have e4 : (fun t : S => ε * readW (Xw (ε * x) ω) t) = fun t : S =>
          readW (fun t : W => X t ω) t / x := by
        funext t
        rw [readW_mk (fun t => X t ω / (ε * x)) (hWS t t.2),
          readW_mk (fun t => X t ω) (hWS t t.2)]
        field_simp
      have hεx0 : 0 < ε * x := mul_pos hε hx0
      simp only [G, e1, e2, Set.indicator_apply, mem_ofPred_eq, hsdef, B,
        BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, e3, e4,
        abs_div, abs_of_pos hεx0, div_lt_div_iff₀ hε hεx0, one_mul]
      have : ε * x < |X i ω| * ε ↔ x < |X i ω| := by
        rw [mul_comm ε x]; exact mul_lt_mul_iff_left₀ hε
      by_cases c1 : x < |X i ω| <;> by_cases c2 : ε * x < |X 0 ω| <;> simp [c1, c2, this]
    rw [integral_congr_ae (ae_of_all _ h1), hstat.integral_comp hX (-i) W hG,
      integral_congr_ae (ae_of_all _ h2)]
    have hne1 : P.real (s x) ≠ 0 := hx.ne'
    have hne2 : P.real (s (ε * x)) ≠ 0 := hεx.ne'
    field_simp
  have hlim := tendsto_nhds_unique hA (key.congr' (heq.mono fun x hx => hx.symm))
  rw [integral_map hYw.aemeasurable (A.continuous.measurable.indicator (measurableSet_lt
      measurable_const (measurable_abs_readW W _))).aestronglyMeasurable,
    integral_map hYw.aemeasurable (B.continuous.measurable.indicator (measurableSet_lt
      measurable_const (measurable_abs_readW W _))).aestronglyMeasurable] at hlim
  convert hlim using 2
  · funext p
    have e3 : readW (Yw p) (-i) = p.1 * Θ (-i) p.2 := readW_mk (fun t => p.1 * Θ t p.2) hWmi
    have e4 : (fun t : S => readW (Yw p) (t - i)) = fun t : S => p.1 * Θ (t - i) p.2 := by
      funext t; exact readW_mk (fun t => p.1 * Θ t p.2) (hWSi t t.2)
    simp only [Set.indicator_apply, mem_ofPred_eq, A, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk, e3, e4]
  · congr 1
    funext p
    have e3 : readW (Yw p) i = p.1 * Θ i p.2 := readW_mk (fun t => p.1 * Θ t p.2) hWi
    have e4 : (fun t : S => ε * readW (Yw p) t) = fun t : S => ε * (p.1 * Θ t p.2) := by
      funext t; rw [readW_mk (fun t => p.1 * Θ t p.2) (hWS t t.2)]
    simp only [Set.indicator_apply, mem_ofPred_eq, B, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk, e3, e4]

/-- **Time change, tail-process form, measure version** ([BS09, Theorem 3.1 (ii)]): the law of
`(Y_{t-i})_{t ∈ S}` on `{|Y_{-i}| > ε}` equals `ε^(-α)` times the law of `(ε Y_t)_{t ∈ S}` on
`{|Y_i| > 1/ε}`. -/
theorem HasSpectralTailProcess.map_restrict_tailProcess_shift (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ) (i : ℤ)
    (S : Finset ℤ) {ε : ℝ} (hε : 0 < ε) :
    (((paretoMeasure 1 α).prod Q).restrict {p | ε < |p.1 * Θ (-i) p.2|}).map
        (fun p (t : S) => p.1 * Θ (t - i) p.2) =
      (ε ^ (-α)).toNNReal • (((paretoMeasure 1 α).prod Q).restrict
        {p | 1 / ε < |p.1 * Θ i p.2|}).map (fun p (t : S) => ε * (p.1 * Θ t p.2)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hm1 : Measurable fun p : ℝ × Ω' => fun t : S => p.1 * Θ (t - i) p.2 :=
    measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
  have hm2 : Measurable fun p : ℝ × Ω' => fun t : S => ε * (p.1 * Θ t p.2) :=
    measurable_pi_iff.2 fun t => measurable_const.mul
      (measurable_fst.mul ((hΘm _).comp measurable_snd))
  have hA1 : MeasurableSet {p : ℝ × Ω' | ε < |p.1 * Θ (-i) p.2|} :=
    measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (measurable_fst.mul ((hΘm _).comp measurable_snd)))
  have hA2 : MeasurableSet {p : ℝ × Ω' | 1 / ε < |p.1 * Θ i p.2|} :=
    measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (measurable_fst.mul ((hΘm _).comp measurable_snd)))
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun H => ?_
  rw [integral_map hm1.aemeasurable H.continuous.aestronglyMeasurable,
    integral_smul_nnreal_measure,
    integral_map hm2.aemeasurable H.continuous.aestronglyMeasurable,
    ← integral_indicator hA1, ← integral_indicator hA2, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (Real.rpow_nonneg hε.le _)]
  exact h.integral_tailProcess_shift hα hX hΘm hstat i S H hε

end TailForm

/-! ### The time-change formula for the spectral tail process -/

/-- `P(|R a| > c) = min(1, c^(-α) |a|^α)` for `R` Pareto(`α`) and `c > 0`. -/
theorem paretoMeasure_lt_abs_mul {α : ℝ} (hα : 0 < α) {c : ℝ} (hc : 0 < c) (a : ℝ) :
    paretoMeasure 1 α {r | c < |r * a|} = ENNReal.ofReal (min 1 (c ^ (-α) * |a| ^ α)) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have hIoi : paretoMeasure 1 α (Ioi 1)ᶜ = 0 := by rw [compl_Ioi]; exact paretoMeasure_one_Iic_one
  rw [← measure_inter_conull hIoi]
  rcases eq_or_ne a 0 with rfl | ha
  · have : {r : ℝ | c < |r * 0|} ∩ Ioi 1 = ∅ := by ext r; simp [hc.le]
    rw [this, measure_empty, abs_zero, Real.zero_rpow hα.ne', mul_zero, min_eq_right zero_le_one,
      ENNReal.ofReal_zero]
  · have ha' : 0 < |a| := abs_pos.2 ha
    set m := max (c / |a|) 1
    have hm : 1 ≤ m := le_max_right _ _
    have : {r : ℝ | c < |r * a|} ∩ Ioi 1 = Ioi m := by
      ext r
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, m, max_lt_iff]
      constructor
      · rintro ⟨h1, h2⟩
        rw [abs_mul, abs_of_pos (one_pos.trans h2)] at h1
        exact ⟨(div_lt_iff₀ ha').2 h1, h2⟩
      · rintro ⟨h1, h2⟩
        rw [abs_mul, abs_of_pos (one_pos.trans h2)]
        exact ⟨(div_lt_iff₀ ha').1 h1, h2⟩
    rw [this, paretoMeasure_one_Ioi hα hm]
    congr 1
    have hdiv : (c / |a|) ^ (-α) = c ^ (-α) * |a| ^ α := by
      rw [Real.div_rpow hc.le ha'.le, Real.rpow_neg ha'.le, div_inv_eq_mul]
    rcases le_total (c / |a|) 1 with h1 | h1
    · rw [show m = 1 from max_eq_right h1, Real.one_rpow, ← hdiv, min_eq_left]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) h1 (by linarith)
    · rw [show m = c / |a| from max_eq_left h1, ← hdiv, min_eq_right]
      exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)

section SpectralForm

variable {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

/-- The time-change identity at a fixed truncation level `ε`, after integrating out the Pareto
variable. -/
private lemma lintegral_timeChange_eps (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (hstat : HasShiftInvariantWindows P X)
    (h : HasSpectralTailProcess P X α Q Θ) (i : ℤ) (S : Finset ℤ)
    {g : (S → ℝ) → ℝ≥0∞} (hg : Measurable g) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ω', g (fun t : S => Θ (t - i) ω') *
        ENNReal.ofReal (min 1 (ε ^ (-α) * |Θ (-i) ω'| ^ α)) ∂Q =
      ∫⁻ ω', g (fun t : S => Θ t ω' / |Θ i ω'|) *
        ENNReal.ofReal (min (ε ^ (-α)) (|Θ i ω'| ^ α)) ∂Q := by
  classical
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set S' := insert i S
  have hiS' : i ∈ S' := Finset.mem_insert_self i S
  have hSS' : ∀ t ∈ S, t ∈ S' := fun t ht => Finset.mem_insert_of_mem ht
  have key := congrArg (fun m : Measure (S' → ℝ) =>
    ∫⁻ y, g (fun t : S => readW y t / |readW y i|) ∂m)
    (h.map_restrict_tailProcess_shift hα hX hΘm hstat i S' hε)
  have hG : Measurable fun y : S' → ℝ => g (fun t : S => readW y t / |readW y i|) :=
    hg.comp (measurable_pi_iff.2 fun t => (measurable_readW _ _).div (measurable_abs_readW _ _))
  have hm1 : Measurable fun p : ℝ × Ω' => fun t : S' => p.1 * Θ (t - i) p.2 :=
    measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
  have hm2 : Measurable fun p : ℝ × Ω' => fun t : S' => ε * (p.1 * Θ t p.2) :=
    measurable_pi_iff.2 fun t => measurable_const.mul
      (measurable_fst.mul ((hΘm _).comp measurable_snd))
  have hf : ∀ j : ℤ, Measurable fun p : ℝ × Ω' => |p.1 * Θ j p.2| := fun j =>
    continuous_abs.measurable.comp (measurable_fst.mul ((hΘm _).comp measurable_snd))
  have hA1 : MeasurableSet {p : ℝ × Ω' | ε < |p.1 * Θ (-i) p.2|} :=
    measurableSet_lt measurable_const (hf _)
  have hA2 : MeasurableSet {p : ℝ × Ω' | 1 / ε < |p.1 * Θ i p.2|} :=
    measurableSet_lt measurable_const (hf _)
  rw [lintegral_map hG hm1, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
    lintegral_map hG hm2,
    ← lintegral_indicator hA1, ← lintegral_indicator hA2] at key
  have h0 := h.ae_abs_eq_one hΘm (hX 0)
  have hπ : ∀ᵐ p ∂((paretoMeasure 1 α).prod Q), 1 < p.1 ∧ |Θ 0 p.2| = 1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure,
      Measure.quasiMeasurePreserving_snd.ae h0] with p h1 h2 using ⟨h1, h2⟩
  -- simplify the left side
  have hL : ∫⁻ p, {p : ℝ × Ω' | ε < |p.1 * Θ (-i) p.2|}.indicator (fun p =>
        g (fun t : S => readW (fun t : S' => p.1 * Θ (t - i) p.2) t /
          |readW (fun t : S' => p.1 * Θ (t - i) p.2) i|)) p ∂((paretoMeasure 1 α).prod Q) =
      ∫⁻ ω', g (fun t : S => Θ (t - i) ω') *
        ENNReal.ofReal (min 1 (ε ^ (-α) * |Θ (-i) ω'| ^ α)) ∂Q := by
    rw [lintegral_congr_ae (g := fun p => {p : ℝ × Ω' | ε < |p.1 * Θ (-i) p.2|}.indicator
      (fun p => g (fun t : S => Θ (t - i) p.2)) p)]
    · have hmL : Measurable fun p : ℝ × Ω' => {p : ℝ × Ω' | ε < |p.1 * Θ (-i) p.2|}.indicator
          (fun p => g (fun t : S => Θ (t - i) p.2)) p :=
        (hg.comp (measurable_pi_iff.2 fun t => (hΘm _).comp measurable_snd)).indicator hA1
      rw [lintegral_prod_symm _ hmL.aemeasurable]
      refine lintegral_congr fun ω' => ?_
      have : (fun r : ℝ => {p : ℝ × Ω' | ε < |p.1 * Θ (-i) p.2|}.indicator
          (fun p => g (fun t : S => Θ (t - i) p.2)) (r, ω')) =
          {r : ℝ | ε < |r * Θ (-i) ω'|}.indicator (fun _ => g (fun t : S => Θ (t - i) ω')) := by
        funext r; simp [Set.indicator_apply]
      rw [this, lintegral_indicator_const (measurableSet_lt measurable_const
        (show Measurable fun r : ℝ => |r * Θ (-i) ω'| from
          continuous_abs.measurable.comp (measurable_id.mul_const _))),
        paretoMeasure_lt_abs_mul hα hε]
    · filter_upwards [hπ] with p hp
      simp only [Set.indicator_apply, mem_ofPred_eq]
      split_ifs
      · congr 1
        funext t
        rw [readW_mk (fun t => p.1 * Θ (t - i) p.2) (hSS' t t.2),
          readW_mk (fun t => p.1 * Θ (t - i) p.2) hiS', sub_self, abs_mul, hp.2, mul_one,
          abs_of_pos (one_pos.trans hp.1)]
        field_simp [(one_pos.trans hp.1).ne']
      · rfl
  -- simplify the right side
  have hR : ∫⁻ p, {p : ℝ × Ω' | 1 / ε < |p.1 * Θ i p.2|}.indicator (fun p =>
        g (fun t : S => readW (fun t : S' => ε * (p.1 * Θ t p.2)) t /
          |readW (fun t : S' => ε * (p.1 * Θ t p.2)) i|)) p ∂((paretoMeasure 1 α).prod Q) =
      ∫⁻ ω', g (fun t : S => Θ t ω' / |Θ i ω'|) *
        ENNReal.ofReal (min 1 ((1 / ε) ^ (-α) * |Θ i ω'| ^ α)) ∂Q := by
    rw [lintegral_congr_ae (g := fun p => {p : ℝ × Ω' | 1 / ε < |p.1 * Θ i p.2|}.indicator
      (fun p => g (fun t : S => Θ t p.2 / |Θ i p.2|)) p)]
    · have hmR : Measurable fun p : ℝ × Ω' => {p : ℝ × Ω' | 1 / ε < |p.1 * Θ i p.2|}.indicator
          (fun p => g (fun t : S => Θ t p.2 / |Θ i p.2|)) p :=
        (hg.comp (measurable_pi_iff.2 fun t => ((hΘm _).comp measurable_snd).div
          (continuous_abs.measurable.comp ((hΘm _).comp measurable_snd)))).indicator hA2
      rw [lintegral_prod_symm _ hmR.aemeasurable]
      refine lintegral_congr fun ω' => ?_
      have : (fun r : ℝ => {p : ℝ × Ω' | 1 / ε < |p.1 * Θ i p.2|}.indicator
          (fun p => g (fun t : S => Θ t p.2 / |Θ i p.2|)) (r, ω')) =
          {r : ℝ | 1 / ε < |r * Θ i ω'|}.indicator
            (fun _ => g (fun t : S => Θ t ω' / |Θ i ω'|)) := by
        funext r; simp [Set.indicator_apply]
      rw [this, lintegral_indicator_const (measurableSet_lt measurable_const
        (show Measurable fun r : ℝ => |r * Θ i ω'| from
          continuous_abs.measurable.comp (measurable_id.mul_const _))),
        paretoMeasure_lt_abs_mul hα (by positivity)]
    · filter_upwards [hπ] with p hp
      simp only [Set.indicator_apply, mem_ofPred_eq]
      split_ifs with hpi
      · congr 1
        funext t
        have hp1 : 0 < p.1 := one_pos.trans hp.1
        have hΘi : Θ i p.2 ≠ 0 := by
          intro h0; rw [h0, mul_zero, abs_zero] at hpi; exact absurd hpi (not_lt.2 (by positivity))
        rw [readW_mk (fun t => ε * (p.1 * Θ t p.2)) (hSS' t t.2),
          readW_mk (fun t => ε * (p.1 * Θ t p.2)) hiS', abs_mul, abs_mul, abs_of_pos hε,
          abs_of_pos hp1]
        field_simp
      · rfl
  rw [hL, hR] at key
  rw [key, ← lintegral_const_mul]
  · refine lintegral_congr fun ω' => ?_
    rw [mul_comm, mul_assoc, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _
      (Real.rpow_nonneg hε.le _), ← ENNReal.ofReal_mul (le_min zero_le_one (by positivity))]
    congr 2
    have h1ε : (1 / ε) ^ (-α) = ε ^ α := by
      rw [one_div, Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv]
    rw [min_mul_of_nonneg _ _ (Real.rpow_nonneg hε.le _), one_mul, h1ε, mul_right_comm,
      ← Real.rpow_add hε, add_neg_cancel, Real.rpow_zero, one_mul]
  · exact (hg.comp (measurable_pi_iff.2 fun t => (hΘm _).div
      (continuous_abs.measurable.comp (hΘm _)))).mul
      (ENNReal.measurable_ofReal.comp (measurable_const.min
        (measurable_const.mul ((continuous_abs.measurable.comp (hΘm _)).pow_const _))))

/-- **The time-change formula** ([BS09, Theorem 3.1 (iii)], [KS20, Theorem 5.3.1]). Let `(X_t)`
be a stationary (`HasShiftInvariantWindows`) time series with spectral tail process `(Θ_t)` and
index `α > 0`. Then for every `i ∈ ℤ`, every finite window `S ⊆ ℤ` and every measurable
`g ≥ 0` on `ℝ^S`,
`E[g((Θ_{t-i})_{t ∈ S}) 1{Θ_{-i} ≠ 0}] = E[g((Θ_t / |Θ_i|)_{t ∈ S}) |Θ_i|^α]`.
The right side vanishes on `{Θ_i = 0}` because of the factor `|Θ_i|^α`. The proof uses stationarity
only through the window laws, regular variation of `P(|X_0| > x)` (through the spectral tail
process), and `|Θ_0| = 1`. -/
theorem HasSpectralTailProcess.lintegral_timeChange (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (hstat : HasShiftInvariantWindows P X)
    (h : HasSpectralTailProcess P X α Q Θ) (i : ℤ) (S : Finset ℤ)
    {g : (S → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω', {ω' | Θ (-i) ω' ≠ 0}.indicator (fun ω' => g fun t : S => Θ (t - i) ω') ω' ∂Q =
      ∫⁻ ω', g (fun t : S => Θ t ω' / |Θ i ω'|) * ENNReal.ofReal (|Θ i ω'| ^ α) ∂Q := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hεα : ∀ n, ε n ^ (-α) = ((n : ℝ) + 1) ^ α := fun n => by
    simp only [ε, one_div, Real.inv_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), inv_inv]
  have hmono : Monotone fun n : ℕ => ((n : ℝ) + 1) ^ α := fun m n hmn =>
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1) hα.le
  have htop : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hLm : ∀ n, Measurable fun ω' => g (fun t : S => Θ (t - i) ω') *
      ENNReal.ofReal (min 1 (ε n ^ (-α) * |Θ (-i) ω'| ^ α)) := fun n =>
    (hg.comp (measurable_pi_iff.2 fun t => hΘm _)).mul (ENNReal.measurable_ofReal.comp
      (measurable_const.min (measurable_const.mul
        ((continuous_abs.measurable.comp (hΘm _)).pow_const _))))
  have hRm : ∀ n, Measurable fun ω' => g (fun t : S => Θ t ω' / |Θ i ω'|) *
      ENNReal.ofReal (min (ε n ^ (-α)) (|Θ i ω'| ^ α)) := fun n =>
    (hg.comp (measurable_pi_iff.2 fun t => (hΘm _).div
      (continuous_abs.measurable.comp (hΘm _)))).mul (ENNReal.measurable_ofReal.comp
      (measurable_const.min ((continuous_abs.measurable.comp (hΘm _)).pow_const _)))
  have hL := lintegral_tendsto_of_tendsto_of_monotone (μ := Q) (fun n => (hLm n).aemeasurable)
    (F := fun ω' => {ω' | Θ (-i) ω' ≠ 0}.indicator (fun ω' => g fun t : S => Θ (t - i) ω') ω')
    (ae_of_all _ fun ω' m n hmn => by
      simp only [hεα]
      gcongr)
    (ae_of_all _ fun ω' => by
      simp only [hεα]
      by_cases h0 : Θ (-i) ω' = 0
      · simp [h0, Real.zero_rpow hα.ne']
      · have hpos : 0 < |Θ (-i) ω'| ^ α := Real.rpow_pos_of_pos (abs_pos.2 h0) _
        rw [indicator_of_mem (show ω' ∈ {ω' | Θ (-i) ω' ≠ 0} from h0)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [(htop.atTop_mul_const hpos).eventually_ge_atTop 1] with n hn
        rw [min_eq_left hn, ENNReal.ofReal_one, mul_one])
  have hR := lintegral_tendsto_of_tendsto_of_monotone (μ := Q) (fun n => (hRm n).aemeasurable)
    (F := fun ω' => g (fun t : S => Θ t ω' / |Θ i ω'|) * ENNReal.ofReal (|Θ i ω'| ^ α))
    (ae_of_all _ fun ω' m n hmn => by
      simp only [hεα]
      gcongr)
    (ae_of_all _ fun ω' => by
      simp only [hεα]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [htop.eventually_ge_atTop (|Θ i ω'| ^ α)] with n hn
      rw [min_eq_right hn])
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  exact (lintegral_timeChange_eps hα hX hΘm hstat h i S hg (hε n)).symm

/-- A shifted exceedance block has probability at most `ϑ`: by the time-change formula (tail
form, `ε = 1`), `P(|Y_j| > 1, |Y_k| ≤ 1 for all k > j) ≤ P(|Y_k| ≤ 1 for all k ≥ 1) = ϑ`. -/
private lemma measure_lastExceedance_le (hα : 0 < α) (hX : ∀ t, Measurable (X t))
    (hΘm : ∀ t, Measurable (Θ t)) (hstat : HasShiftInvariantWindows P X)
    (h : HasSpectralTailProcess P X α Q Θ) (j : ℕ) :
    ((paretoMeasure 1 α).prod Q) {p | 1 < |p.1 * Θ j p.2| ∧
        ∀ k : ℤ, (j : ℤ) < k → |p.1 * Θ k p.2| ≤ 1} ≤
      ((paretoMeasure 1 α).prod Q) {p | ∀ k : ℕ, |p.1 * Θ (k + 1) p.2| ≤ 1} := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q
  have hf : ∀ k : ℤ, Measurable fun p : ℝ × Ω' => |p.1 * Θ k p.2| := fun k =>
    continuous_abs.measurable.comp (measurable_fst.mul ((hΘm _).comp measurable_snd))
  -- the finite-horizon events
  set a : ℕ → Set (ℝ × Ω') := fun n => {p | ∀ t ∈ Finset.Icc (1 : ℤ) n, |p.1 * Θ t p.2| ≤ 1}
  have ha_meas : ∀ n, MeasurableSet (a n) := fun n => by
    simp only [a, ofPred_forall]
    exact MeasurableSet.iInter fun t => MeasurableSet.iInter fun _ =>
      measurableSet_le (hf t) measurable_const
  have hbound : ∀ n : ℕ, π {p | 1 < |p.1 * Θ j p.2| ∧
      ∀ k : ℤ, (j : ℤ) < k → |p.1 * Θ k p.2| ≤ 1} ≤ π (a n) := by
    intro n
    set S := Finset.Icc (1 : ℤ) n
    have key := congrArg (fun m : Measure (S → ℝ) => m {y | ∀ t, |y t| ≤ 1})
      (h.map_restrict_tailProcess_shift hα hX hΘm hstat (-(j : ℤ)) S one_pos)
    have hB : MeasurableSet {y : S → ℝ | ∀ t, |y t| ≤ 1} := by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun t =>
        measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply t))
          measurable_const
    have hm1 : Measurable fun p : ℝ × Ω' => fun t : S => p.1 * Θ (t - -(j : ℤ)) p.2 :=
      measurable_pi_iff.2 fun t => measurable_fst.mul ((hΘm _).comp measurable_snd)
    have hm2 : Measurable fun p : ℝ × Ω' => fun t : S => 1 * (p.1 * Θ t p.2) :=
      measurable_pi_iff.2 fun t => measurable_const.mul
        (measurable_fst.mul ((hΘm _).comp measurable_snd))
    rw [Measure.map_apply hm1 hB, Measure.smul_apply, Measure.map_apply hm2 hB,
      Measure.restrict_apply (hm1 hB), Measure.restrict_apply (hm2 hB)] at key
    calc π {p | 1 < |p.1 * Θ j p.2| ∧ ∀ k : ℤ, (j : ℤ) < k → |p.1 * Θ k p.2| ≤ 1}
        ≤ π ((fun p : ℝ × Ω' => fun t : S => p.1 * Θ (t - -(j : ℤ)) p.2) ⁻¹'
            {y | ∀ t, |y t| ≤ 1} ∩ {p | 1 < |p.1 * Θ (-(-(j : ℤ))) p.2|}) := by
          refine measure_mono fun p hp => ⟨fun t => ?_, ?_⟩
          · have ht := (Finset.mem_Icc.1 t.2).1
            exact hp.2 _ (by omega)
          · simpa using hp.1
      _ = _ := key
      _ ≤ π (a n) := by
          rw [Real.one_rpow, Real.toNNReal_one, one_smul]
          refine (measure_mono inter_subset_left).trans (measure_mono fun p hp t ht => ?_)
          have := hp ⟨t, ht⟩
          simpa using this
  -- pass to the limit `n → ∞`
  have hanti : Antitone a := fun m n hmn p hp t ht =>
    hp t (Finset.Icc_subset_Icc le_rfl (by exact_mod_cast hmn) ht)
  have hlim := tendsto_measure_iInter_atTop (μ := π) (fun n => (ha_meas n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  have hinter : (⋂ n, a n) = {p | ∀ k : ℕ, |p.1 * Θ (k + 1) p.2| ≤ 1} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, a, Finset.mem_Icc]
    constructor
    · intro hp k
      exact_mod_cast hp (k + 1) ((k : ℤ) + 1) ⟨by omega, by push_cast; omega⟩
    · intro hp n t ht
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = (k : ℤ) + 1 := ⟨(t - 1).toNat, by omega⟩
      exact_mod_cast hp k
  rw [hinter] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hbound)

/-- **Positivity of the candidate extremal index** ([KS20, §7.5], [Planinić–Soulier 2018]). For a
stationary series with spectral tail process `(Θ_t)` such that `Θ_t → 0` almost surely as
`t → ∞`, the candidate extremal index is positive. The proof decomposes according to the last
exceedance `j ≥ 0` of the level `1` by the tail process `Y_t = R Θ_t` (which exists because
`|Y_0| = R > 1` and `Y_t → 0`), and bounds the probability of each such event by `ϑ` using the
time-change formula. Only the forward condition `Θ_t → 0` (`t → +∞`) is used. -/
theorem HasSpectralTailProcess.candidateExtremalIndex_pos (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    (hlim : ∀ᵐ ω' ∂Q, Tendsto (fun k : ℕ => Θ k ω') atTop (𝓝 0)) :
    0 < candidateExtremalIndex Q Θ α := by
  classical
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  set π := (paretoMeasure 1 α).prod Q
  have h0 := h.ae_abs_eq_one hΘm (hX 0)
  have hπ1 : ∀ᵐ p ∂π, 1 < p.1 := Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure
  rw [candidateExtremalIndex_eq_measure hα hΘm h0]
  have heq : π {p | ∀ k : ℕ, p.1 * |Θ (k + 1) p.2| ≤ 1} =
      π {p | ∀ k : ℕ, |p.1 * Θ (k + 1) p.2| ≤ 1} := by
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hπ1] with p hp
    simp only [abs_mul, abs_of_pos (one_pos.trans hp)]
  rw [heq, pos_iff_ne_zero]
  intro hzero
  set E : ℕ → Set (ℝ × Ω') := fun j => {p | 1 < |p.1 * Θ j p.2| ∧
    ∀ k : ℤ, (j : ℤ) < k → |p.1 * Θ k p.2| ≤ 1}
  have hE : ∀ j, π (E j) = 0 := fun j =>
    le_antisymm ((measure_lastExceedance_le hα hX hΘm hstat h j).trans hzero.le) zero_le
  have hU : π (⋃ j, E j) = 0 := measure_iUnion_null hE
  have hae : ∀ᵐ p ∂π, p ∈ ⋃ j, E j := by
    filter_upwards [hπ1, Measure.quasiMeasurePreserving_snd.ae h0,
      Measure.quasiMeasurePreserving_snd.ae hlim] with p h1 h2 h3
    have h3' : Tendsto (fun k : ℕ => |p.1 * Θ k p.2|) atTop (𝓝 0) := by
      simpa using ((h3.const_mul p.1).abs)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h3'.eventually (gt_mem_nhds one_pos))
    have hr0 : 1 < |p.1 * Θ 0 p.2| := by
      rw [abs_mul, h2, mul_one, abs_of_pos (one_pos.trans h1)]; exact h1
    set T := (Finset.range N).filter fun k : ℕ => 1 < |p.1 * Θ (k : ℤ) p.2|
    have h0T : 0 ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.pos_of_ne_zero fun hN0 => ?_, by exact_mod_cast hr0⟩
      have := hN 0 (by omega)
      push_cast at this
      linarith
    set j := T.max' ⟨0, h0T⟩
    have hjT : j ∈ T := T.max'_mem _
    refine mem_iUnion.2 ⟨j, (Finset.mem_filter.1 hjT).2, fun k hk => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.toNat, by omega⟩
    have hjm : j < m := by exact_mod_cast hk
    by_contra hcon
    rw [not_le] at hcon
    rcases le_or_gt N m with hNm | hNm
    · linarith [hN m hNm]
    · have hmT : m ∈ T := Finset.mem_filter.2 ⟨Finset.mem_range.2 hNm, hcon⟩
      exact absurd (T.le_max' m hmT) (not_le.2 hjm)
  have : π (⋃ j, E j)ᶜ = 0 := ae_iff.1 hae
  have h1 : π univ ≤ 0 := by
    calc π univ ≤ π (⋃ j, E j) + π (⋃ j, E j)ᶜ := by
          rw [← measure_union disjoint_compl_right (MeasurableSet.iUnion fun j => ?_).compl,
            union_compl_self]
          simp only [E, Set.ofPred_and, ofPred_forall]
          refine (measurableSet_lt measurable_const ?_).inter (MeasurableSet.iInter fun k =>
            MeasurableSet.iInter fun _ => measurableSet_le ?_ measurable_const)
          · exact continuous_abs.measurable.comp
              (measurable_fst.mul ((hΘm _).comp measurable_snd))
          · exact continuous_abs.measurable.comp
              (measurable_fst.mul ((hΘm _).comp measurable_snd))
      _ = 0 := by rw [hU, this, add_zero]
  simp at h1

end SpectralForm

end ExtremeValueTheory
