/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.PeaksOverThreshold.Balkema
import ExtremeValueTheory.DomainOfAttraction.Quantile
import ExtremeValueTheory.DomainOfAttraction.VonMises
import ExtremeValueTheory.GEV.Family
import ExtremeValueTheory.StableLaws.GaussianDomain.Necessity
import ExtremeValueTheory.Statistics.GEVLikelihood

/-!
# The unified domain of attraction `MDA(H_ξ)`: API and examples

`CumulativeDistributionFunction.IsInMDAGEV F ξ` (defined with the Pickands–Balkema–de Haan
theorem) is a case split on the sign of `ξ`. This file unfolds it into the three classical domains
and places the textbook examples in it, with the de Haan–Ferreira sign convention
`ξ = 1/α` (Fréchet), `ξ = 0` (Gumbel), `ξ = -1/α` (Weibull).

## Main results

* `isInMDAGEV_iff_of_pos`, `isInMDAGEV_iff_of_neg`, `isInMDAGEV_zero_iff`: the three cases.
* `IsInMDAFrechet.isInMDAGEV`, `IsInMDAWeibull.isInMDAGEV`, `IsInMDAGumbel.isInMDAGEV`.
* `isInMDAGEV_iff_exists_tendsto_gevCDF`: `IsInMDAGEV ξ` is the textbook statement, convergence of
  the normalized `F ^ n` to `gevCDF ξ` itself.
* `isInMDAGEV_iff_exists_tendsto_gevCDF_of_continuousAt`: the same at continuity points, which is
  the literal form of weak convergence; `gevCDF ξ` is continuous, so the two agree.
* `exists_isInMDAGEV_of_tendsto`: a nondegenerate limit of normalized maxima places `F` in some
  `MDA(H_ξ)`.
* `IsInMDAGEV.unique`: the shape `ξ` of a domain of attraction is unique.
* `isInMDAGEV_paretoCDF`: Pareto(`α`) is in `MDA(H_{1/α})`.
* `isInMDAGEV_powerCDF`: `1 - (1 - x)^α` (uniform for `α = 1`) is in `MDA(H_{-1/α})`.
* `isInMDAGEV_standardExponentialCDF`: the standard exponential law is in `MDA(H_0)`.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 1.1.3 [dHF].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events for Insurance and
  Finance*, Springer (1997), Tables 3.4.2–3.4.4 [EKM].
-/

open Real Filter Topology ExtremeValueTheory

namespace CumulativeDistributionFunction

variable {F : CumulativeDistributionFunction}

/-- For `ξ > 0`, `MDA(H_ξ)` is the Fréchet domain `MDA(Φ_{1/ξ})`. -/
theorem isInMDAGEV_iff_of_pos {ξ : ℝ} (hξ : 0 < ξ) :
    F.IsInMDAGEV ξ ↔ F.IsInMDAFrechet (one_div_pos.2 hξ) := by
  rw [IsInMDAGEV, dif_pos hξ]

/-- For `ξ < 0`, `MDA(H_ξ)` is the Weibull domain `MDA(Ψ_{-1/ξ})`. -/
theorem isInMDAGEV_iff_of_neg {ξ : ℝ} (hξ : ξ < 0) :
    F.IsInMDAGEV ξ ↔ F.IsInMDAWeibull (div_pos_of_neg_of_neg neg_one_lt_zero hξ) := by
  rw [IsInMDAGEV, dif_neg hξ.not_gt, dif_pos hξ]

/-- `MDA(H_0)` is the Gumbel domain `MDA(Λ)`. -/
theorem isInMDAGEV_zero_iff : F.IsInMDAGEV 0 ↔ F.IsInMDAGumbel := by
  rw [IsInMDAGEV, dif_neg (lt_irrefl 0), dif_neg (lt_irrefl 0)]

/-- The Fréchet domain `MDA(Φ_α)` is `MDA(H_{1/α})`. -/
theorem IsInMDAFrechet.isInMDAGEV {α : ℝ} {hα : 0 < α} (h : F.IsInMDAFrechet hα) :
    F.IsInMDAGEV (1 / α) := by
  rw [isInMDAGEV_iff_of_pos (one_div_pos.2 hα)]
  convert h using 2
  simp

/-- The Weibull domain `MDA(Ψ_α)` is `MDA(H_{-1/α})`. -/
theorem IsInMDAWeibull.isInMDAGEV {α : ℝ} {hα : 0 < α} (h : F.IsInMDAWeibull hα) :
    F.IsInMDAGEV (-1 / α) := by
  rw [isInMDAGEV_iff_of_neg (div_neg_of_neg_of_pos neg_one_lt_zero hα)]
  convert h using 2
  field_simp

/-- The Gumbel domain `MDA(Λ)` is `MDA(H_0)`. -/
theorem IsInMDAGumbel.isInMDAGEV (h : F.IsInMDAGumbel) : F.IsInMDAGEV 0 :=
  isInMDAGEV_zero_iff.2 h

/-- **Pareto(`α`) is in `MDA(H_{1/α})`** ([EKM, Table 3.4.2]). -/
theorem isInMDAGEV_paretoCDF {α : ℝ} (hα : 0 < α) : (paretoCDF hα).IsInMDAGEV (1 / α) :=
  (isInMDAFrechet_paretoCDF hα).isInMDAGEV

/-- **`1 - (1 - x)^α` on `[0, 1]` is in `MDA(H_{-1/α})`**; for `α = 1`, the uniform law is in
`MDA(H_{-1})` ([EKM, Table 3.4.3]). -/
theorem isInMDAGEV_powerCDF {α : ℝ} (hα : 0 < α) : (powerCDF hα).IsInMDAGEV (-1 / α) :=
  (isInMDAWeibull_powerCDF hα).isInMDAGEV

/-- **The standard exponential law is in `MDA(H_0)`** ([EKM, Table 3.4.4]). -/
theorem isInMDAGEV_standardExponentialCDF : standardExponentialCDF.IsInMDAGEV 0 :=
  isInMDAGumbel_standardExponentialCDF.isInMDAGEV

/-! ### The link with `gevCDF` -/

/-- Replacing the limit `G` by a member `A • G` of its type does not change membership in the
domain of attraction: the norming maps change by the fixed map `A`. -/
private lemma exists_tendsto_smul_of_exists_tendsto {G : CumulativeDistributionFunction}
    (A : AffineIncrEquiv)
    (h : ∃ As : ℕ → AffineIncrEquiv, ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x))) :
    ∃ As : ℕ → AffineIncrEquiv,
      ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 ((A • G) x)) := by
  obtain ⟨As, hAs⟩ := h
  refine ⟨fun n ↦ A * As n, fun x ↦ ?_⟩
  simpa only [mul_smul, mulAction_apply_eq] using hAs (A⁻¹ x)

/-- `exists_tendsto_smul_of_exists_tendsto` as an equivalence. -/
private lemma exists_tendsto_iff_exists_tendsto_smul {G : CumulativeDistributionFunction}
    (A : AffineIncrEquiv) :
    (∃ As : ℕ → AffineIncrEquiv, ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x))) ↔
      ∃ As : ℕ → AffineIncrEquiv,
        ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 ((A • G) x)) := by
  refine ⟨exists_tendsto_smul_of_exists_tendsto A, fun h ↦ ?_⟩
  simpa only [inv_smul_smul] using exists_tendsto_smul_of_exists_tendsto A⁻¹ h

/-- **`IsInMDAGEV ξ` is the textbook domain of attraction of `H_ξ`** (compare [dHF, Theorem 1.1.3]):
`F` belongs to `MDA(H_ξ)` if and only if the normalized powers `F (a_n x + b_n) ^ n` converge to
`gevCDF ξ x` for every `x`.

`IsInMDAGEV` is defined as a case split on the sign of `ξ` against the standard Fréchet, Weibull and
Gumbel laws. This theorem shows that the split is only a change of normalization, by the fixed
affine maps of `mkOfCoefs_smul_gevCDF_of_pos` and `mkOfCoefs_smul_gevCDF_of_neg`.

Convergence is stated for every `x`. The limit is continuous, so this is the same as convergence at
continuity points (`isInMDAGEV_iff_exists_tendsto_gevCDF_of_continuousAt`). -/
theorem isInMDAGEV_iff_exists_tendsto_gevCDF (ξ : ℝ) :
    F.IsInMDAGEV ξ ↔ ∃ As : ℕ → AffineIncrEquiv,
      ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (gevCDF ξ x)) := by
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · rw [isInMDAGEV_iff_of_neg hξ, exists_tendsto_iff_exists_tendsto_smul
      (AffineIncrEquiv.mkOfCoefs (neg_pos.2 hξ) (-1)), mkOfCoefs_smul_gevCDF_of_neg hξ]
    rfl
  · rw [isInMDAGEV_zero_iff, gevCDF_zero]
    rfl
  · rw [isInMDAGEV_iff_of_pos hξ, exists_tendsto_iff_exists_tendsto_smul
      (AffineIncrEquiv.mkOfCoefs hξ 1), mkOfCoefs_smul_gevCDF_of_pos hξ]
    rfl

/-- `H_ξ` is continuous, as a c.d.f. -/
theorem continuous_gevCDF (ξ : ℝ) : Continuous (gevCDF ξ) := by
  rw [coe_gevCDF]
  exact continuous_gevFun ξ

/-- **`IsInMDAGEV ξ` as weak convergence**: `F` is in `MDA(H_ξ)` if and only if the normalized
powers `F (a_n x + b_n) ^ n` converge to `gevCDF ξ x` at every continuity point `x` of `gevCDF ξ`.
Every point is a continuity point (`continuous_gevCDF`). -/
theorem isInMDAGEV_iff_exists_tendsto_gevCDF_of_continuousAt (ξ : ℝ) :
    F.IsInMDAGEV ξ ↔ ∃ As : ℕ → AffineIncrEquiv, ∀ x, ContinuousAt (gevCDF ξ) x →
      Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (gevCDF ξ x)) := by
  rw [isInMDAGEV_iff_exists_tendsto_gevCDF]
  exact exists_congr fun As ↦ forall_congr' fun x ↦
    ⟨fun h _ ↦ h, fun h ↦ h (continuous_gevCDF ξ).continuousAt⟩

/-- **Fisher–Tippett–Gnedenko, domain of attraction form** ([dHF, Theorem 1.1.3]): if the normalized
powers `F (a_n x + b_n) ^ n` converge at the continuity points of a nondegenerate c.d.f. `G`, then
`F` is in `MDA(H_ξ)` for some `ξ`.

`G` itself is of the type of `gevCDF ξ`: see `IsExtremeValueDistr.exists_smul_eq_gevCDF`. -/
theorem exists_isInMDAGEV_of_tendsto {G : CumulativeDistributionFunction}
    (hG : ¬G.IsDegenerate) {As : ℕ → AffineIncrEquiv}
    (h : ∀ x, ContinuousAt G x → Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x))) :
    ∃ ξ, F.IsInMDAGEV ξ := by
  obtain ⟨A, ξ, hA⟩ := IsExtremeValueDistr.exists_smul_eq_gevCDF
    (show G.IsExtremeValueDistr from ⟨hG, F, As, h⟩)
  refine ⟨ξ, (isInMDAGEV_iff_exists_tendsto_gevCDF ξ).2 ⟨fun n ↦ A * As n, fun x ↦ ?_⟩⟩
  -- `G = H_ξ ∘ A` is continuous, since `H_ξ` and `A` are
  have hGc : Continuous G := by
    have hAy : ∀ y, A⁻¹ (A y) = y := fun y ↦ by
      rw [← AffineIncrEquiv.mul_apply_eq_comp_apply, inv_mul_cancel, AffineIncrEquiv.one_apply]
    have : (G : ℝ → ℝ) = fun y ↦ gevCDF ξ (A.coefs.1 * y + A.coefs.2) := by
      funext y
      rw [← AffineIncrEquiv.apply_eq, ← hA, mulAction_apply_eq, hAy]
    rw [this]
    exact (continuous_gevCDF ξ).comp (by fun_prop)
  have := h (A⁻¹ x) hGc.continuousAt
  simpa only [mul_smul, mulAction_apply_eq, ← hA] using this

/-- **The shape parameter is unique**: if `F` is in `MDA(H_ξ)` and in `MDA(H_η)`, then `ξ = η`. The
domains of attraction of the `H_ξ` are disjoint.

The proof compares two auxiliary functions of the tail quantile function `U`
(`isExtendedRegularlyVarying_tailQuantile`). Both `a` and `a'` are regularly varying, with indices `ξ`
and `η`, and `(U (2 t) - U t) / a t` and `(U (2 t) - U t) / a' t` have positive limits, so `a' / a` has a
positive limit. -/
theorem IsInMDAGEV.unique {ξ η : ℝ} (hξ : F.IsInMDAGEV ξ) (hη : F.IsInMDAGEV η) : ξ = η := by
  obtain ⟨a, ha⟩ := (F.isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile ξ).1 hξ
  obtain ⟨b, hb⟩ := (F.isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile η).1 hη
  have hξ2 : 0 < boxCox ξ 2 := boxCox_pos_of_one_lt one_lt_two
  have hη2 : 0 < boxCox η 2 := boxCox_pos_of_one_lt one_lt_two
  have hratio := (ha.tendsto two_pos).div (hb.tendsto two_pos) hη2.ne'
  have hab : Tendsto (fun t ↦ b t / a t) atTop (𝓝 (boxCox ξ 2 / boxCox η 2)) := by
    refine hratio.congr' ?_
    have hU : ∀ᶠ t in atTop, 0 < (F.tailQuantile (2 * t) - F.tailQuantile t) / b t :=
      (hb.tendsto two_pos).eventually (lt_mem_nhds hη2)
    filter_upwards [ha.eventually_pos, hb.eventually_pos, hU] with t hat hbt hUt
    have hne : F.tailQuantile (2 * t) - F.tailQuantile t ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hUt
      exact lt_irrefl _ hUt
    simp only [Pi.div_apply]
    field_simp
  exact (ha.isRegularlyVarying.of_tendsto_div hab (div_pos hξ2 hη2)).index_eq hb.isRegularlyVarying

end CumulativeDistributionFunction
