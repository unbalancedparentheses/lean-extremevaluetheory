/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.DomainOfAttraction.GEVDomain
import ExtremeValueTheory.PeaksOverThreshold.Converse
import ExtremeValueTheory.Statistics.BlockMaxima

/-!
# Random-variable forms: sample maxima and conditional excesses

The main theorems on domains of attraction are stated for c.d.f.s. This file states them for random
variables, as a reader of the literature expects them.

## Main results

* `isInMDAGEV_iff_exists_tendsto_sampleMax`: for an iid sequence with c.d.f. `F`, `F` is in
  `MDA(H_ξ)` if and only if `(max_{i<n} X_i - b_n) / a_n` converges in distribution to `H_ξ`.
* `exists_isInMDAGEV_and_smul_eq_of_tendsto_sampleMax`: **Fisher–Tippett–Gnedenko for iid sample
  maxima**: a nondegenerate limit of normalized maxima is of the type of some `H_ξ`, and `F` is in
  `MDA(H_ξ)`.
* `measureReal_cond_lt_sub`: the conditional tail of the excess is `excessSurvival`.
* `isInMDAGEV_iff_exists_tendstoUniformlyOn_cond`: **Pickands–Balkema–de Haan for conditional
  probabilities**: `P(X - u > β(u) x | X > u) → Ḡ_ξ(x)` uniformly in `x ≥ 0`, as `u ↑ x_F`.

The maximum `max_{i<n} X_i` is `blockMax X n 0`, the block of index `0`: see `blockMax_zero_le_iff`.
Convergence in distribution is stated as convergence of distribution functions at the continuity
points of the limit.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorems 1.1.3 and 1.1.6 [dHF].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Theorem 3.4.13(b) [EKM].
-/

open MeasureTheory ProbabilityTheory Filter Set Topology ExtremeValueTheory
open scoped ENNReal

namespace CumulativeDistributionFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `blockMax X n 0` is the sample maximum: it is at most `u` iff every `X i`, `i < n`, is. -/
theorem blockMax_zero_le_iff {X : ℕ → Ω → ℝ} {n : ℕ} (hn : 0 < n) (ω : Ω) (u : ℝ) :
    blockMax X n 0 ω ≤ u ↔ ∀ i < n, X i ω ≤ u := by
  simp [blockMax_le_iff hn]

/-- The normalization `x ↦ (x - b) / a`, as the affine map whose action sends `F` to
`x ↦ F (a x + b)`. -/
private lemma normalization_smul_apply (F : CumulativeDistributionFunction) {a : ℝ} (ha : 0 < a)
    (b x : ℝ) : ((AffineIncrEquiv.mkOfCoefs ha b)⁻¹ • F) x = F (a * x + b) := by
  rw [mulAction_apply_eq, inv_inv]
  simp

/-- The distribution function of `(max_{i<n} X_i - b) / a` at `x` is `F (a x + b) ^ n`. -/
private lemma measureReal_normalized_sampleMax_le {F : CumulativeDistributionFunction}
    {X : ℕ → Ω → ℝ} (hF : ∀ x, F x = P.real {ω | X 0 ω ≤ x}) (hind : iIndepFun X P)
    (hid : ∀ t, IdentDistrib (X t) (X 0) P P) {a : ℝ} (ha : 0 < a) (b : ℝ) {n : ℕ} (hn : 0 < n)
    (x : ℝ) : P.real {ω | (blockMax X n 0 ω - b) / a ≤ x} = F (a * x + b) ^ n := by
  have : {ω | (blockMax X n 0 ω - b) / a ≤ x} = {ω | blockMax X n 0 ω ≤ a * x + b} := by
    ext ω
    simp only [mem_ofPred_eq, div_le_iff₀ ha]
    constructor <;> intro h <;> linarith
  rw [this, measureReal_blockMax_le hind hid hn, hF]

/-- **Domain of attraction for iid sample maxima**: for an iid sequence `X` with c.d.f. `F`, `F` is
in `MDA(H_ξ)` if and only if there are `a_n > 0`, `b_n` such that `(max_{i<n} X_i - b_n) / a_n`
converges in distribution to `H_ξ` ([dHF, §1.1]). Every point is a continuity point of `H_ξ`
(`continuous_gevCDF`). -/
theorem isInMDAGEV_iff_exists_tendsto_sampleMax {F : CumulativeDistributionFunction}
    {X : ℕ → Ω → ℝ} (hF : ∀ x, F x = P.real {ω | X 0 ω ≤ x}) (hind : iIndepFun X P)
    (hid : ∀ t, IdentDistrib (X t) (X 0) P P) (ξ : ℝ) :
    F.IsInMDAGEV ξ ↔ ∃ (a b : ℕ → ℝ), (∀ n, 0 < a n) ∧ ∀ x,
      Tendsto (fun n ↦ P.real {ω | (blockMax X n 0 ω - b n) / a n ≤ x}) atTop (𝓝 (gevCDF ξ x)) := by
  rw [isInMDAGEV_iff_exists_tendsto_gevCDF]
  constructor
  · rintro ⟨As, hAs⟩
    refine ⟨fun n ↦ (As n)⁻¹.coefs.1, fun n ↦ (As n)⁻¹.coefs.2,
      fun n ↦ (As n)⁻¹.coefs_fst_pos, fun x ↦ (hAs x).congr' ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [measureReal_normalized_sampleMax_le hF hind hid (As n)⁻¹.coefs_fst_pos _ hn,
      mulAction_apply_eq, AffineIncrEquiv.apply_eq]
  · rintro ⟨a, b, ha, h⟩
    refine ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs (ha n) (b n))⁻¹, fun x ↦ (h x).congr' ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [measureReal_normalized_sampleMax_le hF hind hid (ha n) _ hn, normalization_smul_apply]

/-- **Fisher–Tippett–Gnedenko theorem for iid sample maxima** ([dHF, Theorem 1.1.3]): let `X` be
an iid sequence with c.d.f. `F`. If `(max_{i<n} X_i - b_n) / a_n` converges in distribution to a
nondegenerate c.d.f. `G`, with `a_n > 0`, then `G` is of the type of some `H_ξ`, and `F` is in
`MDA(H_ξ)` for some `ξ`. -/
theorem exists_isInMDAGEV_and_smul_eq_of_tendsto_sampleMax {F G : CumulativeDistributionFunction}
    {X : ℕ → Ω → ℝ} (hF : ∀ x, F x = P.real {ω | X 0 ω ≤ x}) (hind : iIndepFun X P)
    (hid : ∀ t, IdentDistrib (X t) (X 0) P P) {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hG : ¬G.IsDegenerate)
    (h : ∀ x, ContinuousAt G x →
      Tendsto (fun n ↦ P.real {ω | (blockMax X n 0 ω - b n) / a n ≤ x}) atTop (𝓝 (G x))) :
    (∃ ξ, F.IsInMDAGEV ξ) ∧ ∃ (A : AffineIncrEquiv) (ξ : ℝ), A • G = gevCDF ξ := by
  have hlim : ∀ x, ContinuousAt G x →
      Tendsto (fun n : ℕ ↦ (((AffineIncrEquiv.mkOfCoefs (ha n) (b n))⁻¹ • F) x) ^ n) atTop
        (𝓝 (G x)) := fun x hx ↦ (h x hx).congr' <| by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [measureReal_normalized_sampleMax_le hF hind hid (ha n) _ hn, normalization_smul_apply]
  exact ⟨exists_isInMDAGEV_of_tendsto hG hlim,
    IsExtremeValueDistr.exists_smul_eq_gevCDF ⟨hG, F, _, hlim⟩⟩

/-- **The conditional tail of the excess**: if `X` has c.d.f. `F`, then
`P(X - u > y | X > u) = (1 - F (u + y)) / (1 - F u)` for `y ≥ 0`. The right side is
`excessSurvival`. When `P(X > u) = 0` both sides are `0`. -/
theorem measureReal_cond_lt_sub {F : CumulativeDistributionFunction} {X : Ω → ℝ}
    [IsProbabilityMeasure P] (hX : Measurable X) (hF : ∀ x, F x = P.real {ω | X ω ≤ x}) (u : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    (P[|X ⁻¹' Ioi u]).real {ω | y < X ω - u} = excessSurvival (fun t ↦ 1 - F t) u y := by
  have htail : ∀ t, 1 - F t = P.real {ω | t < X ω} := fun t ↦ by
    have hm : MeasurableSet {ω | X ω ≤ t} := measurableSet_le hX measurable_const
    rw [hF, ← probReal_compl_eq_one_sub hm]
    congr 1
    ext ω
    simp
  have hinter : X ⁻¹' Ioi u ∩ {ω | y < X ω - u} = {ω | u + y < X ω} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_ofPred_eq]
    constructor
    · rintro ⟨-, h⟩
      linarith
    · intro h
      constructor <;> linarith
  rw [excessSurvival, htail, htail, measureReal_def,
    cond_apply (hX measurableSet_Ioi), hinter, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ← measureReal_def, ← measureReal_def, div_eq_inv_mul]
  rfl

/-- **Pickands–Balkema–de Haan theorem for conditional probabilities** ([EKM, Theorem 3.4.13(b)],
[dHF, Theorem 1.1.6]): if `X` has c.d.f. `F`, then for every `ξ ∈ ℝ`, `F` is in `MDA(H_ξ)` if and
only if there is a scale `β > 0` such that
`P(X - u > β(u) x | X > u) → Ḡ_{ξ,1}(x)` uniformly in `x ≥ 0`, as `u` increases to the right endpoint
of `F`. No condition on the endpoint, and no density, is assumed. -/
theorem isInMDAGEV_iff_exists_tendstoUniformlyOn_cond {F : CumulativeDistributionFunction}
    {X : Ω → ℝ} [IsProbabilityMeasure P] (hX : Measurable X)
    (hF : ∀ x, F x = P.real {ω | X ω ≤ x}) (ξ : ℝ) :
    F.IsInMDAGEV ξ ↔ ∃ β : ℝ → ℝ, (∀ᶠ u in F.upperEndpointFilter, 0 < β u) ∧
      TendstoUniformlyOn (fun u x ↦ (P[|X ⁻¹' Ioi u]).real {ω | β u * x < X ω - u})
        (gpdSurvivalAll ξ 1) F.upperEndpointFilter (Ici 0) := by
  rw [isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival]
  refine exists_congr fun β ↦ and_congr_right fun hβ ↦ ?_
  have heq : ∀ᶠ u in F.upperEndpointFilter,
      EqOn (fun x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
        (fun x ↦ (P[|X ⁻¹' Ioi u]).real {ω | β u * x < X ω - u}) (Ici 0) := by
    filter_upwards [hβ] with u hu x hx
    exact (measureReal_cond_lt_sub hX hF u (mul_nonneg hu.le hx)).symm
  have heq' : ∀ᶠ u in F.upperEndpointFilter,
      EqOn (fun x ↦ (P[|X ⁻¹' Ioi u]).real {ω | β u * x < X ω - u})
        (fun x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x)) (Ici 0) :=
    heq.mono fun u hu x hx ↦ (hu hx).symm
  exact ⟨fun h ↦ h.congr heq, fun h ↦ h.congr heq'⟩

end CumulativeDistributionFunction
