/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MixtureProcess

/-!
# The block condition `𝒜(uₙ)` is necessary for `θ = ϑ`, even under anticlustering

`HasSpectralTailProcess.hasExtremalIndex_abs` derives `θ = ϑ` from stationarity, the spectral
tail process, `rₙ → ∞`, `rₙ / n → 0`, and, along every level sequence with
`n P(|X_0| > uₙ) → τ > 0`, forward anticlustering *and* the block condition `𝒜(uₙ)`. The
constant/iid mixture of `Dependence/MixtureProcess.lean` shows that `𝒜` fails when anticlustering
fails; here we show that `𝒜` is needed **even when anticlustering holds**: without it the extremal
index need not exist at all.

## The model

Let `(Z_t)_{t ∈ ℤ}` be iid Pareto(`α`), `E` an event independent of `Z` with `p = P(E) ∈ (0, 1)`,
and `0 ≤ c < 1`. The **scale mixture** is `X_t = c Z_t` on `E` and `X_t = Z_t` off `E`: a
non-ergodic mixture of two iid sequences with different scales (`c = 0` is allowed: then `X ≡ 0`
on `E`). With `κ = p c^α + 1 - p`:

* `X` is stationary (`hasShiftInvariantWindows_scaleMixture`) and `P(X_0 > x) = κ x^(-α)` for
  `x ≥ 1` (`measureReal_lt_abs_scaleMixture`);
* its spectral tail process is `Θ_t = 1{t = 0}` (`hasSpectralTailProcess_scaleMixture`), so
  `ϑ = 1`: each regime is iid, so the process is asymptotically independent;
* it satisfies the (two-sided) anticlustering condition `AntiClusteringAt` along every
  `uₙ → ∞` with `rₙ uₙ^(-α) → 0` (`antiClusteringAt_scaleMixture`), in particular along every
  level sequence with `n P(X_0 > uₙ) → τ` and every `rₙ / n → 0`;
* `P(M n ≤ uₙ) → p e^(-c^α τ / κ) + (1 - p) e^(-τ / κ)` (`tendsto_partialMax_scaleMixture`),
  which is not of the form `e^(-θ τ)`: **no extremal index exists**
  (`not_hasExtremalIndex_scaleMixture`), and **`𝒜(uₙ)` fails**
  (`not_conditionA_scaleMixture`) for every `rₙ → ∞`, `rₙ / n → 0`.

`scaleMixture_needs_conditionA` packages all of this: every hypothesis of `hasExtremalIndex_abs`
except `𝒜` holds, and its conclusion fails (there is no `θ` at all, in particular `θ ≠ ϑ`).

Common hypotheses below: `E` measurable (`hE`) and independent of `σ(Z)` (`hEZ`), `Z` measurable
(`hZ`), iid (`hind`) with Pareto(`α`) law (`hlaw`), `Z ≥ 0` (`hpos`), `α > 0` (`hα`),
`0 ≤ c ≤ 1` (`hc0`, `hc1`); strict `c < 1` and `0 < p < 1` only for the negative results.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section ScaleMixture

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α c : ℝ} {Z : ℤ → Ω → ℝ} {E : Set Ω}

open Classical in
/-- **The scale mixture**: on `E`, the iid sequence `c Z_t`; off `E`, the iid sequence `Z_t`. -/
noncomputable def scaleMixture (E : Set Ω) (c : ℝ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  if ω ∈ E then c * Z t ω else Z t ω

theorem measurable_scaleMixture (hE : MeasurableSet E) (hZ : ∀ t, Measurable (Z t)) (t : ℤ) :
    Measurable (scaleMixture E c Z t) :=
  Measurable.ite hE ((hZ t).const_mul c) (hZ t)

theorem scaleMixture_nonneg (hc0 : 0 ≤ c) (hpos : ∀ t ω, 0 ≤ Z t ω) (t : ℤ) (ω : Ω) :
    0 ≤ scaleMixture E c Z t ω := by
  unfold scaleMixture
  split_ifs
  · exact mul_nonneg hc0 (hpos t ω)
  · exact hpos t ω

theorem scaleMixture_le (hc1 : c ≤ 1) (hpos : ∀ t ω, 0 ≤ Z t ω) (t : ℤ) (ω : Ω) :
    scaleMixture E c Z t ω ≤ Z t ω := by
  unfold scaleMixture
  split_ifs
  · exact mul_le_of_le_one_left (hpos t ω) hc1
  · exact le_rfl

/-- **Every event of the scale mixture splits along `E`**:
`P(X ∈ C) = p P(c Z ∈ C) + (1 - p) P(Z ∈ C)`. -/
theorem measureReal_scaleMixture_preimage (hE : MeasurableSet E)
    (hEZ : Indep (MeasurableSpace.generateFrom {E}) (innovationSigma Z) P)
    (hZ : ∀ t, Measurable (Z t)) {C : Set (ℤ → ℝ)} (hC : MeasurableSet C) :
    P.real ((fun ω t => scaleMixture E c Z t ω) ⁻¹' C) =
      P.real E * P.real ((fun ω t => c * Z t ω) ⁻¹' C) +
        (1 - P.real E) * P.real ((fun ω t => Z t ω) ⁻¹' C) := by
  have h1 : Measurable[innovationSigma Z] (fun ω t => c * Z t ω) := by
    let := innovationSigma Z
    exact Measurable.of_eval fun t => (measurable_innovationSigma t).const_mul c
  have h2 : Measurable[innovationSigma Z] (fun ω t => Z t ω) := by
    let := innovationSigma Z
    exact Measurable.of_eval fun t => measurable_innovationSigma t
  have h2m : Measurable (fun ω t => Z t ω) := measurable_pi_iff.2 hZ
  have hset : (fun ω t => scaleMixture E c Z t ω) ⁻¹' C =
      (E ∩ (fun ω t => c * Z t ω) ⁻¹' C) ∪ (Eᶜ ∩ (fun ω t => Z t ω) ⁻¹' C) := by
    ext ω
    by_cases h : ω ∈ E <;> simp [scaleMixture, h]
  rw [hset, measureReal_union (Disjoint.mono inter_subset_left inter_subset_left
    disjoint_compl_right) (hE.compl.inter (h2m hC)), measureReal_inter_of_indep hEZ (h1 hC),
    measureReal_compl_inter_of_indep hE hEZ (h2 hC)]

omit [IsProbabilityMeasure P] in
/-- The tail of a scaled Pareto variable: `P(c Z_t > x) = c^α x^(-α)` for `x ≥ 1`, `0 ≤ c ≤ 1`. -/
theorem measureReal_lt_const_mul (hZ : ∀ t, Measurable (Z t))
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hα : 0 < α) {d : ℝ} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) (t : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    P.real {ω | x < d * Z t ω} = d ^ α * x ^ (-α) := by
  obtain rfl | hd := hd0.eq_or_lt
  · have : {ω | x < 0 * Z t ω} = ∅ := by
      ext ω
      simp only [zero_mul, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      linarith
    rw [this, measureReal_empty, Real.zero_rpow hα.ne', zero_mul]
  · have e : {ω | x < d * Z t ω} = {ω | x / d < Z t ω} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [div_lt_iff₀' hd]
    have hxd : 1 ≤ x / d := by
      rw [le_div_iff₀ hd]
      nlinarith
    rw [e, measureReal_lt_of_map_eq hZ hlaw hα t hxd, Real.div_rpow (by linarith) hd.le,
      Real.rpow_neg hd.le, div_inv_eq_mul, mul_comm]

variable (hE : MeasurableSet E)
  (hEZ : Indep (MeasurableSpace.generateFrom {E}) (innovationSigma Z) P)
  (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω)
  (hc0 : 0 ≤ c) (hc1 : c ≤ 1)

include hE hEZ hα hZ hlaw hpos hc0 hc1 in
/-- **The marginal tail**: `P(|X_0| > x) = κ x^(-α)` with `κ = p c^α + 1 - p`, for `x ≥ 1`. -/
theorem measureReal_lt_abs_scaleMixture {x : ℝ} (hx : 1 ≤ x) :
    P.real {ω | x < |scaleMixture E c Z 0 ω|} =
      (P.real E * c ^ α + (1 - P.real E)) * x ^ (-α) := by
  have hC : MeasurableSet {z : ℤ → ℝ | x < |z 0|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_pi_apply 0))
  have key := measureReal_scaleMixture_preimage (c := c) hE hEZ hZ hC
  have e1 : (fun ω t => scaleMixture E c Z t ω) ⁻¹' {z : ℤ → ℝ | x < |z 0|} =
      {ω | x < |scaleMixture E c Z 0 ω|} := rfl
  have e2 : (fun ω t => c * Z t ω) ⁻¹' {z : ℤ → ℝ | x < |z 0|} = {ω | x < c * Z 0 ω} := by
    ext ω; simp [abs_mul, abs_of_nonneg hc0, abs_of_nonneg (hpos 0 ω)]
  have e3 : (fun ω t => Z t ω) ⁻¹' {z : ℤ → ℝ | x < |z 0|} = {ω | x < Z 0 ω} := by
    ext ω; simp [abs_of_nonneg (hpos 0 ω)]
  rw [e1, e2, e3, measureReal_lt_const_mul hZ hlaw hα hc0 hc1 0 hx,
    measureReal_lt_of_map_eq hZ hlaw hα 0 hx] at key
  rw [key]
  ring

omit hE hEZ hc0 hc1 in
include hα hZ hind hlaw hpos in
/-- The block maximum of a scaled iid Pareto sequence:
`P(max_{k < n} |d Z_k| ≤ u) = (1 - d^α u^(-α))^n` for `u ≥ 1`, `0 ≤ d ≤ 1`. -/
theorem measureReal_forall_const_mul_le {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (n : ℕ) {u : ℝ}
    (hu : 1 ≤ u) :
    P.real ((fun ω t => d * Z t ω) ⁻¹' {z : ℤ → ℝ | ∀ k ∈ Finset.range n, |z k| ≤ u}) =
      (1 - d ^ α * u ^ (-α)) ^ n := by
  have hindN : iIndepFun (fun k : ℕ => fun ω => d * Z k ω) P :=
    (hind.precomp (g := fun k : ℕ => (k : ℤ)) Nat.cast_injective).comp (fun _ x => d * x)
      (fun _ => measurable_const_mul d)
  have hidN : ∀ k : ℕ, IdentDistrib (fun ω => d * Z k ω) (fun ω => d * Z ((0 : ℕ) : ℤ) ω) P P :=
    fun k => IdentDistrib.comp ⟨(hZ _).aemeasurable, (hZ _).aemeasurable, by rw [hlaw, hlaw]⟩
      (measurable_const_mul d)
  have e : (fun ω t => d * Z t ω) ⁻¹' {z : ℤ → ℝ | ∀ k ∈ Finset.range n, |z k| ≤ u} =
      maxLE (fun k : ℕ => fun ω => d * Z k ω) (Finset.range n) u := by
    ext ω
    simp [maxLE, abs_mul, abs_of_nonneg hd0, abs_of_nonneg (hpos _ ω)]
  have hc : P.real {ω | d * Z ((0 : ℕ) : ℤ) ω ≤ u} = 1 - d ^ α * u ^ (-α) := by
    have : {ω | d * Z ((0 : ℕ) : ℤ) ω ≤ u} = {ω | u < d * Z 0 ω}ᶜ := by ext; simp
    rw [this, probReal_compl_eq_one_sub (measurableSet_lt measurable_const ((hZ 0).const_mul d)),
      measureReal_lt_const_mul hZ hlaw hα hd0 hd1 0 hu]
  rw [e, measureReal_maxLE_of_iIndepFun hindN hidN, hc, Finset.card_range]

include hE hEZ hα hZ hind hlaw hpos hc0 hc1 in
/-- **The law of the maximum**: `P(max_{k < n} |X_k| ≤ u) = p (1 - c^α u^(-α))^n +
(1 - p) (1 - u^(-α))^n` for `n ≥ 1`, `u ≥ 1`. -/
theorem measureReal_partialMax_scaleMixture {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 1 ≤ u) :
    P.real {ω | partialMax (fun k : ℕ => |scaleMixture E c Z k|) n ω ≤ u} =
      P.real E * (1 - c ^ α * u ^ (-α)) ^ n + (1 - P.real E) * (1 - u ^ (-α)) ^ n := by
  have hC : MeasurableSet {z : ℤ → ℝ | ∀ k ∈ Finset.range n, |z k| ≤ u} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply _)) measurable_const
  have key := measureReal_scaleMixture_preimage (c := c) hE hEZ hZ hC
  have e1 : {ω | partialMax (fun k : ℕ => |scaleMixture E c Z k|) n ω ≤ u} =
      (fun ω t => scaleMixture E c Z t ω) ⁻¹' {z : ℤ → ℝ | ∀ k ∈ Finset.range n, |z k| ≤ u} := by
    ext ω
    simp only [mem_ofPred_eq, partialMax_le_iff hn, Pi.abs_apply, mem_preimage,
      Finset.mem_range]
  have e3 : (fun ω t => Z t ω) = fun ω t => 1 * Z t ω := by simp
  rw [e1, key, measureReal_forall_const_mul_le hα hZ hind hlaw hpos hc0 hc1 n hu, e3,
    measureReal_forall_const_mul_le hα hZ hind hlaw hpos zero_le_one le_rfl n hu,
    Real.one_rpow, one_mul]

include hE hEZ hα hZ hind hlaw hpos hc0 hc1 in
/-- **The maximum has a mixture limit**: if `uₙ → ∞` and `n uₙ^(-α) → s`, then
`P(max_{k < n} |X_k| ≤ uₙ) → p e^(-c^α s) + (1 - p) e^(-s)`. -/
theorem tendsto_partialMax_scaleMixture {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {s : ℝ}
    (hs : Tendsto (fun n : ℕ => n * u n ^ (-α)) atTop (𝓝 s)) :
    Tendsto (fun n => P.real {ω | partialMax (fun k : ℕ => |scaleMixture E c Z k|) n ω ≤ u n})
      atTop (𝓝 (P.real E * Real.exp (-(c ^ α * s)) + (1 - P.real E) * Real.exp (-s))) := by
  have hb : Tendsto (fun n => u n ^ (-α)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hα).comp hu
  have h1 := tendsto_one_sub_pow_exp_of_tendsto_mul (k := fun n => n)
    (b := fun n => c ^ α * u n ^ (-α)) (by simpa using hb.const_mul (c ^ α))
    ((hs.const_mul (c ^ α)).congr fun n => by ring)
  have h2 := tendsto_one_sub_pow_exp_of_tendsto_mul (k := fun n => n) hb hs
  refine ((h1.const_mul (P.real E)).add (h2.const_mul (1 - P.real E))).congr' ?_
  filter_upwards [hu.eventually_ge_atTop 1, eventually_gt_atTop 0] with n hn hn0
  exact (measureReal_partialMax_scaleMixture hE hEZ hα hZ hind hlaw hpos hc0 hc1 hn0 hn).symm

/-! ### Stationarity and the spectral tail process -/

omit hα hpos hc0 hc1 in
include hE hEZ hZ hind hlaw in
/-- **The scale mixture is stationary**: a mixture, with weights independent of the noise, of two
stationary iid sequences. -/
theorem hasShiftInvariantWindows_scaleMixture :
    HasShiftInvariantWindows P (scaleMixture E c Z) := by
  have hid : ∀ i, IdentDistrib (Z i) (Z 0) P P := fun i =>
    ⟨(hZ _).aemeasurable, (hZ _).aemeasurable, by rw [hlaw, hlaw]⟩
  have hZs : HasShiftInvariantWindows P (fun t ω => Z t ω) := by
    have := hasShiftInvariantWindows_of_shift hZ hind hid (G := fun z => z 0)
      (measurable_pi_apply 0)
    simpa using this
  have hcZs : HasShiftInvariantWindows P (fun t ω => c * Z t ω) := by
    have := hasShiftInvariantWindows_of_shift hZ hind hid (G := fun z => c * z 0)
      (by fun_prop)
    simpa using this
  have key : ∀ (Y : ℤ → Ω → ℝ), (∀ t, Measurable (Y t)) → HasShiftInvariantWindows P Y →
      ∀ (S : Finset ℤ) (k : ℤ) {B : Set (S → ℝ)}, MeasurableSet B →
        P.real ((fun ω (t : S) => Y (t + k) ω) ⁻¹' B) =
          P.real ((fun ω (t : S) => Y t ω) ⁻¹' B) := by
    intro Y hY hYs S k B hB
    have := congrArg (fun μ : Measure (S → ℝ) => μ.real B) (hYs k S)
    rwa [map_measureReal_apply (measurable_pi_iff.2 fun t => hY _) hB,
      map_measureReal_apply (measurable_pi_iff.2 fun t => hY _) hB] at this
  intro h S
  have hX : ∀ k, Measurable fun ω (t : S) => scaleMixture E c Z (t + k) ω := fun k =>
    measurable_pi_iff.2 fun t => measurable_scaleMixture hE hZ _
  have e0 : (fun ω (t : S) => scaleMixture E c Z t ω) =
      fun ω (t : S) => scaleMixture E c Z (t + 0) ω := by simp
  ext B hB
  rw [Measure.map_apply (hX h) hB, e0, Measure.map_apply (hX 0) hB,
    ← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _)]
  congr 1
  have hCk : ∀ k : ℤ, MeasurableSet ((fun (z : ℤ → ℝ) (t : S) => z (t + k)) ⁻¹' B) := fun k =>
    (measurable_pi_iff.2 fun t => measurable_pi_apply _) hB
  have hk := fun k : ℤ => measureReal_scaleMixture_preimage (c := c) hE hEZ hZ (hCk k)
  have e : ∀ k : ℤ, (fun ω (t : S) => scaleMixture E c Z (t + k) ω) ⁻¹' B =
      (fun ω t => scaleMixture E c Z t ω) ⁻¹' ((fun (z : ℤ → ℝ) (t : S) => z (t + k)) ⁻¹' B) :=
    fun k => rfl
  rw [e h, e 0, hk h, hk 0]
  have e2 : ∀ (Y : ℤ → Ω → ℝ) (k : ℤ), (fun ω t => Y t ω) ⁻¹'
      ((fun (z : ℤ → ℝ) (t : S) => z (t + k)) ⁻¹' B) =
        (fun ω (t : S) => Y (t + k) ω) ⁻¹' B := fun Y k => rfl
  rw [e2 (fun t ω => c * Z t ω), e2 (fun t ω => c * Z t ω), e2 (fun t ω => Z t ω),
    e2 (fun t ω => Z t ω),
    key _ (fun t => (hZ t).const_mul c) hcZs S h hB, key _ (fun t => (hZ t).const_mul c) hcZs S 0 hB,
    key _ hZ hZs S h hB, key _ hZ hZs S 0 hB]

include hE hEZ hα hZ hind hlaw hpos hc0 hc1 in
/-- **The spectral tail process of the scale mixture is trivial**: `Θ_t = 1{t = 0}`. Both regimes
are iid, so the process is asymptotically independent at every lag. -/
theorem hasSpectralTailProcess_scaleMixture (hp1 : P.real E < 1) :
    HasSpectralTailProcess P (scaleMixture E c Z) α (Measure.dirac ()) unitSpectral := by
  set κ := P.real E * c ^ α + (1 - P.real E)
  have hκ : 0 < κ := by
    have : 0 ≤ P.real E * c ^ α := mul_nonneg measureReal_nonneg (Real.rpow_nonneg hc0 _)
    simp only [κ]; linarith
  have hRV : IsRegularlyVarying (fun x => P.real {ω | x < |scaleMixture E c Z 0 ω|}) (-α) := by
    refine ((IsRegularlyVarying.rpow_id (-α)).const_mul hκ).congr ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    exact (measureReal_lt_abs_scaleMixture hE hEZ hα hZ hlaw hpos hc0 hc1 hx).symm
  refine hasSpectralTailProcess_of_asymptoticIndependence (measurable_scaleMixture hE hZ)
    (scaleMixture_nonneg hc0 hpos 0) hRV fun t ht ε hε => ?_
  have hlim : Tendsto (fun x : ℝ => (ε * x) ^ (-α) / κ) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hα).comp (tendsto_id.const_mul_atTop hε)).div_const κ
  refine squeeze_zero' (Eventually.of_forall fun x => div_nonneg measureReal_nonneg
    measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (1 / ε)] with x hx hxε
  have hεx : 1 ≤ ε * x := by rwa [div_le_iff₀' hε] at hxε
  have hx0 : 0 < x ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
  rw [measureReal_lt_abs_scaleMixture hE hEZ hα hZ hlaw hpos hc0 hc1 hx,
    div_le_div_iff₀ (by positivity) hκ]
  have hsub : {ω | x < |scaleMixture E c Z 0 ω| ∧ ε * x < |scaleMixture E c Z t ω|} ⊆
      {ω | x < Z 0 ω} ∩ {ω | ε * x < Z t ω} := by
    intro ω ⟨h0, h1⟩
    rw [abs_of_nonneg (scaleMixture_nonneg hc0 hpos _ _)] at h0 h1
    exact ⟨h0.trans_le (scaleMixture_le hc1 hpos 0 ω), h1.trans_le (scaleMixture_le hc1 hpos t ω)⟩
  have h1 := measureReal_mono (μ := P) hsub
  rw [measureReal_lt_inter_lt_of_ne hZ hind hlaw hα (Ne.symm ht) hx hεx] at h1
  calc P.real {ω | x < |scaleMixture E c Z 0 ω| ∧ ε * x < |scaleMixture E c Z t ω|} * κ
      ≤ x ^ (-α) * (ε * x) ^ (-α) * κ := by gcongr
    _ = (ε * x) ^ (-α) * (κ * x ^ (-α)) := by ring

/-! ### Anticlustering holds -/

include hE hEZ hα hZ hind hlaw hpos hc0 hc1 in
/-- **The scale mixture satisfies anticlustering** (two-sided, at the single level sequence
`uₙ`) whenever `uₙ → ∞`, `rₙ uₙ^(-α) → 0` and `P(E) < 1`: a joint exceedance at lags `t ≠ 0`
needs two large independent innovations, of probability `uₙ^(-2α)`, and there are `≤ 2 rₙ + 1`
lags. -/
theorem antiClusteringAt_scaleMixture (hp1 : P.real E < 1) {u : ℕ → ℝ}
    (hu : Tendsto u atTop atTop) {r : ℕ → ℕ}
    (hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0)) :
    AntiClusteringAt P (scaleMixture E c Z) u r := by
  set κ := P.real E * c ^ α + (1 - P.real E)
  have hκ : 0 < κ := by
    have : 0 ≤ P.real E * c ^ α := mul_nonneg measureReal_nonneg (Real.rpow_nonneg hc0 _)
    simp only [κ]; linarith
  have hb : Tendsto (fun n => u n ^ (-α)) atTop (𝓝 0) := (tendsto_rpow_neg_atTop hα).comp hu
  have hlim : Tendsto (fun n => 2 * ((r n : ℝ) * u n ^ (-α)) + u n ^ (-α)) atTop (𝓝 0) := by
    simpa using (hrb.const_mul 2).add hb
  intro ε hε
  refine ⟨1, ?_⟩
  filter_upwards [hu.eventually_ge_atTop 1, hlim.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < ε * κ))] with n hn hsmall
  set b := u n ^ (-α)
  have hb0 : 0 < b := Real.rpow_pos_of_pos (by linarith) _
  set T : Finset ℤ := (Finset.Icc (-(r n : ℤ)) (r n)).erase 0
  have hsub : {ω | u n < |scaleMixture E c Z 0 ω| ∧ ∃ t : ℤ, ((1 : ℕ) : ℤ) ≤ |t| ∧ |t| ≤ r n ∧
      u n < |scaleMixture E c Z t ω|} ⊆ ⋃ t ∈ T, {ω | u n < Z 0 ω} ∩ {ω | u n < Z t ω} := by
    rintro ω ⟨h0, t, ht1, htr, ht⟩
    rw [abs_of_nonneg (scaleMixture_nonneg hc0 hpos _ _)] at h0 ht
    refine mem_iUnion₂.2 ⟨t, ?_, h0.trans_le (scaleMixture_le hc1 hpos 0 ω),
      ht.trans_le (scaleMixture_le hc1 hpos t ω)⟩
    rw [Finset.mem_erase, Finset.mem_Icc]
    have := abs_le.1 htr
    refine ⟨fun h => ?_, this.1, this.2⟩
    rw [h] at ht1
    simp at ht1
  have hsum : ∀ t ∈ T, P.real ({ω | u n < Z 0 ω} ∩ {ω | u n < Z t ω}) = b * b := by
    intro t ht
    exact measureReal_lt_inter_lt_of_ne hZ hind hlaw hα (Ne.symm (Finset.ne_of_mem_erase ht)) hn hn
  have hcard : (T.card : ℝ) ≤ 2 * r n + 1 := by
    have h1 : T.card ≤ (Finset.Icc (-(r n : ℤ)) (r n)).card := Finset.card_erase_le
    have h2 : (Finset.Icc (-(r n : ℤ)) (r n)).card = 2 * r n + 1 := by
      rw [Int.card_Icc]; omega
    have : T.card ≤ 2 * r n + 1 := h2 ▸ h1
    exact_mod_cast this
  rw [measureReal_lt_abs_scaleMixture hE hEZ hα hZ hlaw hpos hc0 hc1 hn]
  calc _ ≤ P.real (⋃ t ∈ T, {ω | u n < Z 0 ω} ∩ {ω | u n < Z t ω}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ t ∈ T, P.real ({ω | u n < Z 0 ω} ∩ {ω | u n < Z t ω}) :=
        measureReal_biUnion_finset_le _ _
    _ = T.card * (b * b) := by rw [Finset.sum_congr rfl hsum]; simp
    _ ≤ (2 * r n + 1) * (b * b) := by gcongr
    _ = (2 * (r n * b) + b) * b := by ring
    _ ≤ (ε * κ) * b := by gcongr
    _ = ε * (κ * b) := by ring

/-! ### No extremal index, and `𝒜` fails -/

include hE hEZ hα hZ hind hlaw hpos hc0 in
/-- **The scale mixture has no extremal index** when `0 < P(E) < 1` and `c < 1`: the limits
`p e^(-c^α τ / κ) + (1 - p) e^(-τ / κ)` are not of the form `e^(-θ τ)` (comparing `τ` and `2 τ`
gives `p (1 - p) (A - B)² = 0` with `A = e^(-c^α / κ) ≠ B = e^(-1 / κ)`). -/
theorem not_hasExtremalIndex_scaleMixture (hc1 : c < 1) (hp0 : 0 < P.real E)
    (hp1 : P.real E < 1) (θ : ℝ) :
    ¬ HasExtremalIndex (fun k : ℕ => |scaleMixture E c Z k|) P θ := by
  rintro ⟨-, h⟩
  set p := P.real E
  set κ := p * c ^ α + (1 - p)
  have hcα : c ^ α < 1 := Real.rpow_lt_one hc0 hc1 hα
  have hκ : 0 < κ := by
    have : 0 ≤ p * c ^ α := mul_nonneg hp0.le (Real.rpow_nonneg hc0 _)
    simp only [κ]; linarith
  have key : ∀ τ : ℝ, 0 < τ → Real.exp (-(θ * τ)) =
      p * Real.exp (-(c ^ α * (τ / κ))) + (1 - p) * Real.exp (-(τ / κ)) := by
    intro τ hτ0
    set u : ℕ → ℝ := fun n => ((n : ℝ) * κ / τ) ^ (1 / α)
    have hu : Tendsto u atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).comp
        ((tendsto_natCast_atTop_atTop.atTop_mul_const hκ).atTop_div_const hτ0)
    have hub : ∀ᶠ n : ℕ in atTop, (n : ℝ) * u n ^ (-α) = τ / κ := by
      filter_upwards [eventually_gt_atTop 0] with n hn0
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      simp only [u]
      rw [← Real.rpow_mul (by positivity), show 1 / α * -α = -1 by field_simp, Real.rpow_neg_one]
      field_simp
    have hs : Tendsto (fun n : ℕ => n * u n ^ (-α)) atTop (𝓝 (τ / κ)) :=
      tendsto_const_nhds.congr' (hub.mono fun n hn => hn.symm)
    have hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |scaleMixture E c Z 0 ω|}) atTop
        (𝓝 τ) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hub, hu.eventually_ge_atTop 1] with n hn hn1
      rw [measureReal_lt_abs_scaleMixture hE hEZ hα hZ hlaw hpos hc0 hc1.le hn1,
        show P.real E * c ^ α + (1 - P.real E) = κ from rfl, mul_left_comm, hn]
      field_simp
    have h1 := h τ hτ0 u (by simpa using hτ)
    exact tendsto_nhds_unique h1
      (tendsto_partialMax_scaleMixture hE hEZ hα hZ hind hlaw hpos hc0 hc1.le hu hs)
  have k1 := key 1 one_pos
  have k2 := key 2 two_pos
  set A := Real.exp (-(c ^ α * (1 / κ)))
  set B := Real.exp (-(1 / κ))
  have hA2 : Real.exp (-(c ^ α * (2 / κ))) = A ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hB2 : Real.exp (-(2 / κ)) = B ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hθ2 : Real.exp (-(θ * 2)) = Real.exp (-(θ * 1)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hθ2, k1, hA2, hB2] at k2
  have hAB : B < A := Real.exp_lt_exp.2 (by
    have : c ^ α * (1 / κ) < 1 / κ := by
      have := one_div_pos.2 hκ
      nlinarith
    linarith)
  have : p * (1 - p) * (A - B) ^ 2 = 0 := by linear_combination -k2
  have hpos' : 0 < p * (1 - p) * (A - B) ^ 2 := by
    have : 0 < A - B := by linarith
    have : 0 < 1 - p := by linarith
    positivity
  linarith

include hE hEZ hα hZ hind hlaw hpos hc0 in
/-- **The block condition `𝒜(uₙ)` fails** for the scale mixture (`0 < P(E) < 1`, `c < 1`), along
every level sequence with `n P(|X_0| > uₙ) → τ > 0` and every `rₙ → ∞`, `rₙ / n → 0`, although
anticlustering holds there: otherwise `tendsto_partialMax_abs` would give
`P(M n ≤ uₙ) → e^(-ϑ τ) = e^(-τ)`, whereas the limit is
`p e^(-c^α τ / κ) + (1 - p) e^(-τ / κ) > e^(-τ)` (strict convexity of `exp`). -/
theorem not_conditionA_scaleMixture (hc1 : c < 1) (hp0 : 0 < P.real E) (hp1 : P.real E < 1)
    {u : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < |scaleMixture E c Z 0 ω|}) atTop (𝓝 τ))
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0)) :
    AntiClusteringAt P (scaleMixture E c Z) u r ∧
      ¬ ConditionA (fun k : ℕ => |scaleMixture E c Z k|) P u r := by
  set p := P.real E
  set κ := p * c ^ α + (1 - p)
  have hcα : c ^ α < 1 := Real.rpow_lt_one hc0 hc1 hα
  have hκ : 0 < κ := by
    have : 0 ≤ p * c ^ α := mul_nonneg hp0.le (Real.rpow_nonneg hc0 _)
    simp only [κ]; linarith
  have hT := hasSpectralTailProcess_scaleMixture hE hEZ hα hZ hind hlaw hpos hc0 hc1.le hp1
  have hu := hT.tendsto_atTop_of_tendsto_mul hτ
  have hs : Tendsto (fun n : ℕ => n * u n ^ (-α)) atTop (𝓝 (τ / κ)) := by
    refine (hτ.div_const κ).congr' ?_
    filter_upwards [hu.eventually_ge_atTop 1] with n hn
    rw [measureReal_lt_abs_scaleMixture hE hEZ hα hZ hlaw hpos hc0 hc1.le hn,
      show P.real E * c ^ α + (1 - P.real E) = κ from rfl]
    field_simp
  have hrb : Tendsto (fun n => (r n : ℝ) * u n ^ (-α)) atTop (𝓝 0) := by
    have := hrn.mul hs
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hAC := antiClusteringAt_scaleMixture hE hEZ hα hZ hind hlaw hpos hc0 hc1.le hp1 hu hrb
  refine ⟨hAC, fun hA => ?_⟩
  have h1 := hT.tendsto_partialMax_abs hα (measurable_scaleMixture hE hZ)
    measurable_unitSpectral (hasShiftInvariantWindows_scaleMixture hE hEZ hZ hind hlaw) hτ hr hrn
    hAC.forward hA
  rw [candidateExtremalIndex_unitSpectral hα, ENNReal.toReal_one, one_mul] at h1
  have h2 := tendsto_partialMax_scaleMixture hE hEZ hα hZ hind hlaw hpos hc0 hc1.le hu hs
  have heq := tendsto_nhds_unique h1 h2
  have hne : -(c ^ α * (τ / κ)) ≠ -(τ / κ) := by
    intro h
    have : c ^ α * (τ / κ) = 1 * (τ / κ) := by linarith
    have := mul_right_cancel₀ (by positivity : τ / κ ≠ 0) this
    linarith
  have hconv := strictConvexOn_exp.2 (Set.mem_univ (-(c ^ α * (τ / κ))))
    (Set.mem_univ (-(τ / κ))) hne hp0 (by linarith : 0 < 1 - p) (by ring)
  simp only [smul_eq_mul] at hconv
  have hmid : p * -(c ^ α * (τ / κ)) + (1 - p) * -(τ / κ) = -τ := by
    simp only [κ] at *
    field_simp
    ring
  rw [hmid] at hconv
  linarith

/-! ### The packaged counterexample -/

include hE hEZ hα hZ hind hlaw hpos hc0 in
/-- **`𝒜(uₙ)` is necessary in `hasExtremalIndex_abs`, even under anticlustering.** For the scale
mixture with `0 < P(E) < 1` and `0 ≤ c < 1`:
* it is stationary, with spectral tail process `Θ_t = 1{t = 0}` and `ϑ = 1`;
* along every level sequence with `n P(|X_0| > uₙ) → τ > 0` and every `rₙ → ∞`, `rₙ / n → 0`,
  anticlustering holds and `𝒜(uₙ)` fails;
* `(|X_n|)` has no extremal index, in particular not `ϑ`. -/
theorem scaleMixture_needs_conditionA (hc1 : c < 1) (hp0 : 0 < P.real E) (hp1 : P.real E < 1) :
    HasShiftInvariantWindows P (scaleMixture E c Z) ∧
      HasSpectralTailProcess P (scaleMixture E c Z) α (Measure.dirac ()) unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      (∀ τ > 0, ∀ u : ℕ → ℝ,
        Tendsto (fun n : ℕ => n * P.real {ω | u n < |scaleMixture E c Z 0 ω|}) atTop (𝓝 τ) →
        ∀ r : ℕ → ℕ, Tendsto r atTop atTop → Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0) →
          AntiClusteringAt P (scaleMixture E c Z) u r ∧
            ¬ ConditionA (fun k : ℕ => |scaleMixture E c Z k|) P u r) ∧
      ∀ θ, ¬ HasExtremalIndex (fun k : ℕ => |scaleMixture E c Z k|) P θ :=
  ⟨hasShiftInvariantWindows_scaleMixture hE hEZ hZ hind hlaw,
    hasSpectralTailProcess_scaleMixture hE hEZ hα hZ hind hlaw hpos hc0 hc1.le hp1,
    by rw [candidateExtremalIndex_unitSpectral hα]; rfl,
    fun _ hτ0 _ hτ _ hr hrn =>
      not_conditionA_scaleMixture hE hEZ hα hZ hind hlaw hpos hc0 hc1 hp0 hp1 hτ0 hτ hr hrn,
    not_hasExtremalIndex_scaleMixture hE hEZ hα hZ hind hlaw hpos hc0 hc1 hp0 hp1⟩

end ScaleMixture

end ExtremeValueTheory
