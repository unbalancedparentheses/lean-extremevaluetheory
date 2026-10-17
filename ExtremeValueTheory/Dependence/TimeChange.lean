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
      simp only [mem_preimage, mem_setOf_eq, hYwdef]
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
      simp only [G, e1, e2, Set.indicator_apply, mem_setOf_eq, hsdef, A,
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
      simp only [G, e1, e2, Set.indicator_apply, mem_setOf_eq, hsdef, B,
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
    simp only [Set.indicator_apply, mem_setOf_eq, A, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk, e3, e4]
  · congr 1
    funext p
    have e3 : readW (Yw p) i = p.1 * Θ i p.2 := readW_mk (fun t => p.1 * Θ t p.2) hWi
    have e4 : (fun t : S => ε * readW (Yw p) t) = fun t : S => ε * (p.1 * Θ t p.2) := by
      funext t; rw [readW_mk (fun t => p.1 * Θ t p.2) (hWS t t.2)]
    simp only [Set.indicator_apply, mem_setOf_eq, B, BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk, e3, e4]

end TailForm

end ExtremeValueTheory
