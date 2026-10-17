/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.SelfSimilarCDF

/-!
# Max-stable distributions

A nondegenerate distribution function `G` is **max-stable** ([EKM, Definition 3.2.1]) if for
every `n ≥ 1` there are constants `a_n > 0` and `b_n` with

  `G(a_n x + b_n) ^ n = G(x)` for all `x`,

i.e. the maximum of `n` iid copies of a random variable with law `G` has, after the affine
renormalization `(M_n - b_n) / a_n`, the law `G` again.

The class of max-stable distributions coincides with the class of extreme value distributions
([EKM, Theorem 3.2.2]; [dHF, Theorem 1.1.3]):

* a max-stable `G` is trivially the limit law of its own normalized maxima;
* conversely, an extreme value distribution is max-stable for every real power by
  `CumulativeDistributionFunction.exists_smul_eq_pow_of_isExtremeValueDistr`, a consequence of
  the convergence of types theorem.

For the three standard types the norming constants are explicit:

* Gumbel `Λ(x) = exp(-e^{-x})`: `Λ(x + log n) ^ n = Λ(x)`;
* Fréchet `Φ_α(x) = exp(-x^{-α})`: `Φ_α(n ^ (1/α) x) ^ n = Φ_α(x)`;
* Weibull `Ψ_α(x) = exp(-(-x)^α)`: `Ψ_α(n ^ (-1/α) x) ^ n = Ψ_α(x)`.

## Main definitions and results

* `CumulativeDistributionFunction.IsMaxStable`: [EKM, Definition 3.2.1].
* `CumulativeDistributionFunction.isMaxStable_iff_isExtremeValueDistr`: max-stable ⇔ extreme
  value distribution ([EKM, Theorem 3.2.2]).
* `CumulativeDistributionFunction.IsMaxStable.affineTransform`: max-stability is a property of
  the type.
* `standardGumbelCDF_pow_apply_add_log`, `standardFrechetCDF_pow_apply_rpow_mul`,
  `standardWeibullCDF_pow_apply_rpow_mul`: the explicit max-stability relations, and
  `isMaxStable_standardGumbelCDF`, `isMaxStable_standardFrechetCDF`,
  `isMaxStable_standardWeibullCDF`: these laws are max-stable (proved directly, without the
  convergence of types theorem).
* `CumulativeDistributionFunction.IsMaxStable.classification`: every max-stable law is of
  Gumbel, Fréchet or Weibull type.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  §3.2 [EKM].
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  §1.1 [dHF].
-/

open Filter Topology Real

namespace CumulativeDistributionFunction

/-- A c.d.f. `G` is **max-stable** if it is nondegenerate and for all `n ≥ 1` there are
`a_n > 0` and `b_n` with `G(a_n x + b_n) ^ n = G(x)` for all `x` ([EKM, Definition 3.2.1]). -/
def IsMaxStable (G : CumulativeDistributionFunction) : Prop :=
  ¬ G.IsDegenerate ∧
    ∀ n : ℕ, 1 ≤ n → ∃ a b : ℝ, 0 < a ∧ ∀ x, G (a * x + b) ^ n = G x

/-- Max-stability in terms of orientation preserving affine maps: `(A • G) = G ^ (1/n)`
for some affine `A`, i.e. `G(A⁻¹ x) ^ n = G x`. -/
lemma isMaxStable_iff_exists_affine (G : CumulativeDistributionFunction) :
    G.IsMaxStable ↔ ¬ G.IsDegenerate ∧
      ∀ n : ℕ, 1 ≤ n → ∃ A : AffineIncrEquiv, ∀ x, G (A x) ^ n = G x := by
  refine and_congr_right fun _ ↦ forall₂_congr fun n _ ↦ ⟨?_, ?_⟩
  · rintro ⟨a, b, ha, h⟩
    exact ⟨AffineIncrEquiv.mkOfCoefs ha b, fun x ↦ by simpa using h x⟩
  · rintro ⟨A, h⟩
    exact ⟨A.coefs.1, A.coefs.2, A.coefs_fst_pos, fun x ↦ by simpa using h x⟩

/-- A max-stable distribution is an extreme value distribution: it is the limit (indeed, it is
equal to each term) of its own normalized maxima. -/
lemma IsMaxStable.isExtremeValueDistr {G : CumulativeDistributionFunction}
    (hG : G.IsMaxStable) : G.IsExtremeValueDistr := by
  obtain ⟨hnd, h⟩ := (isMaxStable_iff_exists_affine G).1 hG
  choose A hA using h
  refine ⟨hnd, G, fun n ↦ if hn : 1 ≤ n then (A n hn)⁻¹ else 1, fun x _ ↦ ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [hn, dite_true, mulAction_apply_eq, inv_inv]
  exact (hA n hn x).symm

/-- An extreme value distribution is max-stable ([EKM, Theorem 3.2.2]). -/
lemma IsExtremeValueDistr.isMaxStable {G : CumulativeDistributionFunction}
    (hG : G.IsExtremeValueDistr) : G.IsMaxStable := by
  refine (isMaxStable_iff_exists_affine G).2 ⟨hG.nondegenerate, fun n hn ↦ ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨A, hA⟩ := exists_smul_eq_pow_of_isExtremeValueDistr hG (inv_pos.2 hn')
  refine ⟨A⁻¹, fun x ↦ ?_⟩
  have h := congrArg (fun F : CumulativeDistributionFunction ↦ F x) hA
  simp only [mulAction_apply_eq, pow_apply_eq] at h
  rw [h, ← rpow_natCast, ← rpow_mul (G.apply_nonneg x), inv_mul_cancel₀ hn'.ne', rpow_one]

/-- **Max-stable distributions are exactly the extreme value distributions**
([EKM, Theorem 3.2.2]; [dHF, Theorem 1.1.3]). -/
theorem isMaxStable_iff_isExtremeValueDistr (G : CumulativeDistributionFunction) :
    G.IsMaxStable ↔ G.IsExtremeValueDistr :=
  ⟨IsMaxStable.isExtremeValueDistr, IsExtremeValueDistr.isMaxStable⟩

/-- Max-stability is preserved by orientation preserving affine transformations: it is a
property of the type of `G`. -/
lemma IsMaxStable.affineTransform {G : CumulativeDistributionFunction} (hG : G.IsMaxStable)
    (B : AffineIncrEquiv) : (B • G).IsMaxStable := by
  obtain ⟨hnd, h⟩ := (isMaxStable_iff_exists_affine G).1 hG
  refine (isMaxStable_iff_exists_affine _).2
    ⟨by simpa [affine_isDegenerate_iff] using hnd, fun n hn ↦ ?_⟩
  obtain ⟨A, hA⟩ := h n hn
  refine ⟨B * A * B⁻¹, fun x ↦ ?_⟩
  simp only [mulAction_apply_eq, AffineIncrEquiv.mul_apply_eq_comp_apply]
  have : B⁻¹ (B (A (B⁻¹ x))) = A (B⁻¹ x) := by
    rw [← AffineIncrEquiv.mul_apply_eq_comp_apply, inv_mul_cancel, AffineIncrEquiv.one_apply]
  rw [this, hA]

/-- Every max-stable law is of Gumbel, Fréchet or Weibull type (Fisher–Tippett–Gnedenko). -/
theorem IsMaxStable.classification {G : CumulativeDistributionFunction} (hG : G.IsMaxStable) :
    (∃ (A : AffineIncrEquiv), A • G = standardGumbelCDF) ∨
      (∃ (A : AffineIncrEquiv) (α : ℝ) (hα : 0 < α), A • G = standardFrechetCDF hα) ∨
      (∃ (A : AffineIncrEquiv) (α : ℝ) (hα : 0 < α), A • G = standardWeibullCDF hα) :=
  hG.isExtremeValueDistr.classification

/-! ### The three standard types, by direct computation -/

private lemma not_isDegenerate_of_apply_eq_exp_neg_one (G : CumulativeDistributionFunction)
    {x : ℝ} (hx : G x = exp (-1)) : ¬ G.IsDegenerate := by
  intro h
  rcases h x with h0 | h1
  · exact (exp_pos _).ne' (hx ▸ h0)
  · have := exp_eq_one_iff (-1) |>.mp (hx ▸ h1)
    norm_num at this

/-- Max-stability of the Gumbel law: `Λ(x + log n) ^ n = Λ(x)`. -/
lemma standardGumbelCDF_pow_apply_add_log {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    standardGumbelCDF (1 * x + log n) ^ n = standardGumbelCDF x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [standardGumbelCDF_apply_eq, standardGumbelCDF_apply_eq, ← exp_nat_mul, one_mul, neg_add,
    exp_add, exp_neg (log _), exp_log hn']
  congr 1
  field_simp

/-- Max-stability of the Fréchet law: `Φ_α(n ^ (1/α) x) ^ n = Φ_α(x)`. -/
lemma standardFrechetCDF_pow_apply_rpow_mul {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n)
    (x : ℝ) :
    standardFrechetCDF hα ((n : ℝ) ^ (1 / α) * x + 0) ^ n = standardFrechetCDF hα x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < (n : ℝ) ^ (1 / α) := rpow_pos_of_pos hn' _
  rw [add_zero]
  by_cases hx : x ≤ 0
  · rw [standardFrechetCDF_apply_nonpos_eq hα hx,
      standardFrechetCDF_apply_nonpos_eq hα (mul_nonpos_of_nonneg_of_nonpos hc.le hx),
      zero_pow (by omega)]
  · have hx' : 0 < x := lt_of_not_ge hx
    rw [standardFrechetCDF_apply_pos_eq hα hx',
      standardFrechetCDF_apply_pos_eq hα (mul_pos hc hx'), ← exp_nat_mul]
    congr 1
    change (n : ℝ) * -(((n : ℝ) ^ (1 / α) * x) ^ (-α)) = -(x ^ (-α))
    rw [mul_rpow hc.le hx'.le, ← rpow_mul hn'.le, show 1 / α * -α = -1 by field_simp,
      rpow_neg_one]
    field_simp

/-- Max-stability of the Weibull law: `Ψ_α(n ^ (-1/α) x) ^ n = Ψ_α(x)`. -/
lemma standardWeibullCDF_pow_apply_rpow_mul {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n)
    (x : ℝ) :
    standardWeibullCDF hα ((n : ℝ) ^ (-1 / α) * x + 0) ^ n = standardWeibullCDF hα x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < (n : ℝ) ^ (-1 / α) := rpow_pos_of_pos hn' _
  rw [add_zero]
  by_cases hx : 0 ≤ x
  · rw [standardWeibullCDF_apply_nonneg_eq hα hx,
      standardWeibullCDF_apply_nonneg_eq hα (mul_nonneg hc.le hx), one_pow]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [standardWeibullCDF_apply_neg_eq hα hx',
      standardWeibullCDF_apply_neg_eq hα (mul_neg_of_pos_of_neg hc hx'), ← exp_nat_mul]
    congr 1
    change (n : ℝ) * -((-((n : ℝ) ^ (-1 / α) * x)) ^ α) = -((-x) ^ α)
    rw [← mul_neg, mul_rpow hc.le (by linarith), ← rpow_mul hn'.le,
      show -1 / α * α = -1 by field_simp, rpow_neg_one]
    field_simp

/-- The standard Gumbel law is max-stable (direct computation). -/
lemma isMaxStable_standardGumbelCDF : standardGumbelCDF.IsMaxStable :=
  ⟨not_isDegenerate_of_apply_eq_exp_neg_one _ (x := 0) (by simp [standardGumbelCDF_apply_eq]),
    fun _ hn ↦ ⟨1, _, one_pos, standardGumbelCDF_pow_apply_add_log hn⟩⟩

/-- The standard Fréchet law is max-stable (direct computation). -/
lemma isMaxStable_standardFrechetCDF {α : ℝ} (hα : 0 < α) :
    (standardFrechetCDF hα).IsMaxStable :=
  ⟨not_isDegenerate_of_apply_eq_exp_neg_one _ (x := 1)
      (by simp [standardFrechetCDF_apply_pos_eq hα one_pos]),
    fun n hn ↦ ⟨_, 0, rpow_pos_of_pos (by exact_mod_cast hn) _,
      standardFrechetCDF_pow_apply_rpow_mul hα hn⟩⟩

/-- The standard Weibull law is max-stable (direct computation). -/
lemma isMaxStable_standardWeibullCDF {α : ℝ} (hα : 0 < α) :
    (standardWeibullCDF hα).IsMaxStable :=
  ⟨not_isDegenerate_of_apply_eq_exp_neg_one _ (x := -1)
      (by simp [standardWeibullCDF_apply_neg_eq hα (by norm_num : (-1 : ℝ) < 0)]),
    fun n hn ↦ ⟨_, 0, rpow_pos_of_pos (by exact_mod_cast hn) _,
      standardWeibullCDF_pow_apply_rpow_mul hα hn⟩⟩

/-- Converse direction of [EKM, Theorem 3.2.2] by direct computation: every law of the type of
one of the three standard extreme value laws is max-stable. -/
lemma isMaxStable_of_classification {G : CumulativeDistributionFunction}
    (hG : (∃ (A : AffineIncrEquiv), A • G = standardGumbelCDF) ∨
      (∃ (A : AffineIncrEquiv) (α : ℝ) (hα : 0 < α), A • G = standardFrechetCDF hα) ∨
      (∃ (A : AffineIncrEquiv) (α : ℝ) (hα : 0 < α), A • G = standardWeibullCDF hα)) :
    G.IsMaxStable := by
  have key : ∀ (A : AffineIncrEquiv) (H : CumulativeDistributionFunction), A • G = H →
      H.IsMaxStable → G.IsMaxStable := by
    intro A H hAH hH
    have := hH.affineTransform A⁻¹
    rwa [← hAH, inv_smul_smul] at this
  rcases hG with ⟨A, hA⟩ | ⟨A, α, hα, hA⟩ | ⟨A, α, hα, hA⟩
  · exact key A _ hA isMaxStable_standardGumbelCDF
  · exact key A _ hA (isMaxStable_standardFrechetCDF hα)
  · exact key A _ hA (isMaxStable_standardWeibullCDF hα)

end CumulativeDistributionFunction
