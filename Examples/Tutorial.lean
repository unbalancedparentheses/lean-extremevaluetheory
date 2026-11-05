import ExtremeValueTheory

/-!
# Your first extreme value theory proof in Lean

One example, end to end. `docs/TUTORIAL.md` is the commentary on this file.

The law is `F̄(x) = (1 + x)⁻²` on `[0, ∞)`, a Lomax law; the library has no name for it, so we do
everything by hand. We

1. define it as a `CumulativeDistributionFunction`;
2. show its tail is regularly varying with index `-2`;
3. apply Gnedenko's theorem to put it in the Fréchet domain `MDA(Φ₂)`;
4. apply Hill's consistency theorem to an iid sample from it, with `k n = ⌊√n⌋`.

What the end result says: for an iid sample of this exact law, the Hill estimator converges in
probability to `1/2`. It says nothing about any finite `n`.
-/

open Filter Topology Set MeasureTheory ProbabilityTheory
open CumulativeDistributionFunction ExtremeValueTheory

namespace Examples.Tutorial

/-! ### Step 1: the law -/

/-- The law with `F(x) = 1 - (1 + x)⁻²` for `x ≥ 0` and `F(x) = 0` for `x < 0`. A
`CumulativeDistributionFunction` carries four proofs: monotone, right-continuous, limit `1` at
`+∞`, limit `0` at `-∞`. Writing the tail with `max x 0` makes it one formula on all of `ℝ`. -/
noncomputable def lomaxCDF : CumulativeDistributionFunction where
  toFun x := 1 - (1 + max x 0) ^ (-2 : ℝ)
  mono' := fun x y hxy ↦ sub_le_sub_left (Real.rpow_le_rpow_of_nonpos
    (by positivity) (by gcongr) (by norm_num)) 1
  right_continuous' := fun x ↦ (continuous_const.sub
    ((continuous_const.add (continuous_id.max continuous_const)).rpow_const fun y ↦
      Or.inl (show 1 + max (id y) (0 : ℝ) ≠ 0 by positivity))).continuousWithinAt
  tendsto_atTop := by
    have h1 : Tendsto (fun x : ℝ ↦ 1 + x) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
    have h := ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).comp h1).const_sub (1 : ℝ)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp [max_eq_left hx]
  tendsto_atBot := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot 0] with x hx
    simp [max_eq_right hx]

/-- The tail, in the form the rest of the proof uses. -/
theorem one_sub_lomaxCDF {x : ℝ} (hx : 0 ≤ x) : 1 - lomaxCDF x = (1 + x) ^ (-2 : ℝ) := by
  change 1 - (1 - (1 + max x 0) ^ (-2 : ℝ)) = _
  rw [max_eq_left hx, sub_sub_cancel]

/-! ### Step 2: the tail is regularly varying -/

/-- `1 + x` is regularly varying with index `1`, because `(1 + x) / x → 1`.
`IsRegularlyVarying.of_tendsto_div` transfers regular variation along such a limit. -/
theorem isRegularlyVarying_one_add : IsRegularlyVarying (fun x : ℝ ↦ 1 + x) 1 := by
  refine (IsRegularlyVarying.rpow_id 1).of_tendsto_div (L := 1) ?_ one_pos
  have h : Tendsto (fun x : ℝ ↦ x⁻¹ + 1) atTop (𝓝 (0 + 1)) :=
    tendsto_inv_atTop_zero.add_const 1
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_one]
  field_simp

/-- The tail `1 - F` is regularly varying with index `-2`. `IsRegularlyVarying` only looks near
`+∞`, so it is enough that the tail equals `(1 + x)⁻²` eventually. -/
theorem isRegularlyVarying_tail : IsRegularlyVarying (fun x ↦ 1 - lomaxCDF x) (-2) := by
  have h := isRegularlyVarying_one_add.rpow (-2)
  rw [one_mul] at h
  refine h.congr ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [one_sub_lomaxCDF hx]

/-! ### Step 3: Gnedenko's theorem -/

/-- **The law is in the Fréchet domain `MDA(Φ₂)`**, by Gnedenko's theorem `isInMDAFrechet_iff`.
The proof of `0 < 2` is part of the statement, because `Φ_α` is only defined for `α > 0`. -/
theorem isInMDAFrechet_lomaxCDF : lomaxCDF.IsInMDAFrechet (two_pos : (0 : ℝ) < 2) :=
  (lomaxCDF.isInMDAFrechet_iff two_pos).2 isRegularlyVarying_tail

/-- The definition of the domain, unfolded: there are affine maps `As n` such that
`(As n • F)(x)ⁿ → Φ₂(x)` for every `x`. Gnedenko's theorem gives their existence, not a formula. -/
example : ∃ As : ℕ → AffineIncrEquiv, ∀ x,
    Tendsto (fun n : ℕ ↦ ((As n • lomaxCDF) x) ^ n) atTop
      (𝓝 (standardFrechetCDF (two_pos : (0 : ℝ) < 2) x)) :=
  isInMDAFrechet_lomaxCDF

/-- The same fact on the GEV scale: `ξ = 1/α = 1/2`. -/
example : lomaxCDF.IsInMDAGEV (1 / 2) :=
  isInMDAFrechet_lomaxCDF.isInMDAGEV

/-- Gnedenko's theorem is an equivalence, so regular variation can also be recovered. -/
example : IsRegularlyVarying (fun x ↦ 1 - lomaxCDF x) (-2) :=
  (lomaxCDF.isInMDAFrechet_iff two_pos).1 isInMDAFrechet_lomaxCDF

/-! ### Step 4: Hill's estimator -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Hill consistency for this law.** A sample is a sequence `X : ℕ → Ω → ℝ`, its law is
`lomaxCDF.measure`, and the estimator is `hill` applied to the first `n` observations. With
`k n = ⌊√n⌋` (`Nat.sqrt`), the Hill estimator converges in probability to `1/2`.

`tendstoInMeasure_hill_of_hasLaw` asks for regular variation of `x ↦ μ.real (Ioi x)`; the simp
lemma `measureReal_Ioi` says that for `μ = F.measure` this is `1 - F x`. -/
theorem tendstoInMeasure_hill_lomax {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) lomaxCDF.measure P) (hindep : iIndepFun X P) :
    TendstoInMeasure P (fun n ω ↦ hill (fun i : Fin n ↦ X i ω) (Nat.sqrt n)) atTop
      (fun _ ↦ 1 / 2) := by
  refine tendstoInMeasure_hill_of_hasLaw hX hlaw hindep two_pos ?_ tendsto_sqrt_atTop
    tendsto_sqrt_div
  simpa only [measureReal_Ioi] using isRegularlyVarying_tail

/-- **The theorem above is not vacuous**: such a sample exists (Mathlib's `exists_iid`), so its
hypotheses can all be met at once. -/
theorem exists_sample_tendstoInMeasure_hill_lomax :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ iIndepFun X P ∧ (∀ i, HasLaw (X i) lomaxCDF.measure P) ∧
      TendstoInMeasure P (fun n ω ↦ hill (fun i : Fin n ↦ X i ω) (Nat.sqrt n)) atTop
        (fun _ ↦ 1 / 2) := by
  obtain ⟨Ω, _, P, X, hXm, hlaw, hind, hP⟩ := exists_iid ℕ lomaxCDF.measure
  exact ⟨Ω, _, P, X, hP, hind, hlaw, tendstoInMeasure_hill_lomax hXm hlaw hind⟩

end Examples.Tutorial
