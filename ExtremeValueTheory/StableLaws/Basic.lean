/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.Subexponential
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stable laws

A probability measure `μ` on `ℝ` is *stable* if it is not concentrated at one point and, for
every `n ≥ 1`, the `n`-fold convolution power `μ^{*n}` (the law of `X₁ + ⋯ + Xₙ` for i.i.d.
`Xᵢ ∼ μ`) is the law of `aₙ X + bₙ` for some `aₙ > 0` and `bₙ ∈ ℝ`, where `X ∼ μ`. It is
*strictly stable* if one can take `bₙ = 0`.

We follow Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II
(2nd ed., Wiley, 1971), §VI.1 and Ch. XVII [Feller]; Gnedenko and Kolmogorov, *Limit
Distributions for Sums of Independent Random Variables* (Addison-Wesley, 1954) [GK];
Samorodnitsky and Taqqu, *Stable Non-Gaussian Random Processes* (Chapman & Hall, 1994), §1.1
[ST]; and Embrechts, Klüppelberg and Mikosch, *Modelling Extremal Events* (Springer, 1997),
§2.2 [EKM].

## Main definitions

* `ExtremeValueTheory.IsStable μ`: `μ` is stable ([Feller, VI.1, Definition 1]).
* `ExtremeValueTheory.IsStrictlyStable μ`: `μ` is strictly stable.
* `ExtremeValueTheory.IsSymmStable α c μ`: `μ` is a probability measure with characteristic
  function `t ↦ exp (-c |t| ^ α)` (symmetric `α`-stable law, [ST, Definition 1.1.6 and
  (1.2.3)] with `β = 0`, `μ = 0`, `σ ^ α = c`).

## Main results

* `charFun_convPow`: `φ_{μ^{*n}} = φ_μ ^ n`.
* `convPow_eq_map_of_charFun`: the characteristic-function criterion for
  `μ^{*n} = law (a X + b)`, namely `φ(t) ^ n = φ(a t) e^{i b t}`.
* `isStable_gaussianReal`, `isStrictlyStable_gaussianReal`: Gaussian laws are stable.
* `IsSymmStable.conv`, `IsSymmStable.map_mul`, `IsSymmStable.convPow`: closure of the class
  of symmetric `α`-stable laws under convolution and scaling.
* `IsSymmStable.isStrictlyStable`: for `α > 0`, `c > 0`, a law with characteristic function
  `exp (-c |t| ^ α)` is strictly stable, with `aₙ = n ^ (1 / α)`.
* `isSymmStable_gaussianReal`: `N(0, v)` is symmetric `2`-stable with `c = v / 2`.

The Cauchy law is treated in `ExtremeValueTheory.StableLaws.Cauchy`, existence of symmetric
`α`-stable laws and the generalized central limit theorem in
`ExtremeValueTheory.StableLaws.DomainOfAttraction`.
-/

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal RealInnerProductSpace

namespace ExtremeValueTheory

open Subexp

section CharFun

variable {μ : Measure ℝ}

/-- The characteristic function of the convolution power `μ^{*n}` is `φ_μ ^ n`. -/
theorem charFun_convPow [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    charFun (convPow μ n) t = charFun μ t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [convPow_succ, charFun_conv, ih, pow_succ, mul_comm]

/-- Characteristic function of an affine image: `φ_{aX+b}(t) = φ_X(a t) e^{i b t}`. -/
theorem charFun_map_mul_add (a b t : ℝ) :
    charFun (μ.map (fun x => a * x + b)) t = charFun μ (a * t) * cexp (b * t * I) := by
  have h : (fun x : ℝ => a * x + b) = (· + b) ∘ (a * ·) := rfl
  rw [h, ← Measure.map_map (measurable_add_const b) (measurable_const_mul a),
    charFun_map_add_const, charFun_map_mul]
  simp [mul_comm]

/-- A measure whose characteristic function has modulus `< 1` somewhere is not a Dirac mass. -/
theorem ne_dirac_of_norm_charFun_lt_one {t : ℝ} (h : ‖charFun μ t‖ < 1) (x : ℝ) :
    μ ≠ Measure.dirac x := by
  rintro rfl
  rw [charFun_dirac] at h
  simp only [RCLike.inner_apply, conj_trivial] at h
  rw [Complex.norm_exp_ofReal_mul_I] at h
  exact lt_irrefl _ h

/-- **Characteristic function criterion.** If `φ_μ(t) ^ n = φ_μ(a t) e^{i b t}` for all `t`,
then `μ^{*n}` is the law of `a X + b` for `X ∼ μ`. -/
theorem convPow_eq_map_of_charFun [IsProbabilityMeasure μ] {n : ℕ} {a b : ℝ}
    (h : ∀ t, charFun μ t ^ n = charFun μ (a * t) * cexp (b * t * I)) :
    convPow μ n = μ.map (fun x => a * x + b) := by
  have : IsProbabilityMeasure (μ.map (fun x => a * x + b)) :=
    inferInstance
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_convPow, charFun_map_mul_add, h]

end CharFun

/-- A probability measure `μ` on `ℝ` is *stable* if it is not a Dirac mass and for every `n ≥ 1`
there are `aₙ > 0` and `bₙ` with `μ^{*n} = law (aₙ X + bₙ)`, `X ∼ μ`
([Feller, §VI.1, Definition 1], [GK, §33], [ST, Definition 1.1.4]). -/
structure IsStable (μ : Measure ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  ne_dirac : ∀ x : ℝ, μ ≠ Measure.dirac x
  exists_affine : ∀ n : ℕ, 1 ≤ n → ∃ a b : ℝ, 0 < a ∧ convPow μ n = μ.map (fun x => a * x + b)

/-- A probability measure `μ` on `ℝ` is *strictly stable* if it is not a Dirac mass and for every
`n ≥ 1` there is `aₙ > 0` with `μ^{*n} = law (aₙ X)`, `X ∼ μ` ([Feller, §VI.1]). -/
structure IsStrictlyStable (μ : Measure ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  ne_dirac : ∀ x : ℝ, μ ≠ Measure.dirac x
  exists_mul : ∀ n : ℕ, 1 ≤ n → ∃ a : ℝ, 0 < a ∧ convPow μ n = μ.map (fun x => a * x)

theorem IsStrictlyStable.isStable {μ : Measure ℝ} (h : IsStrictlyStable μ) : IsStable μ where
  isProbabilityMeasure := h.isProbabilityMeasure
  ne_dirac := h.ne_dirac
  exists_affine n hn := by
    obtain ⟨a, ha, h⟩ := h.exists_mul n hn
    exact ⟨a, 0, ha, by simpa using h⟩

section Gaussian

theorem norm_charFun_gaussianReal_one_lt (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ‖charFun (gaussianReal m v) 1‖ < 1 := by
  rw [charFun_gaussianReal, Complex.norm_exp]
  simp
  exact pos_iff_ne_zero.2 hv

/-- **The Gaussian law is stable** ([Feller, §VI.1]): `N(m, v)^{*n} = law (√n X + (n - √n) m)`. -/
theorem isStable_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : IsStable (gaussianReal m v) where
  isProbabilityMeasure := inferInstance
  ne_dirac := ne_dirac_of_norm_charFun_lt_one (norm_charFun_gaussianReal_one_lt m hv)
  exists_affine n _ := by
    refine ⟨Real.sqrt n, (n - Real.sqrt n) * m, Real.sqrt_pos.2 (by positivity), ?_⟩
    refine convPow_eq_map_of_charFun fun t => ?_
    have hs : ((Real.sqrt n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
      rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; simp
    simp only [charFun_gaussianReal, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination ((v : ℂ) * (t : ℂ) ^ 2 / 2) * hs

/-- **The centered Gaussian law is strictly stable**: `N(0, v)^{*n} = law (√n X)`. -/
theorem isStrictlyStable_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) :
    IsStrictlyStable (gaussianReal 0 v) where
  isProbabilityMeasure := inferInstance
  ne_dirac := (isStable_gaussianReal 0 hv).ne_dirac
  exists_mul n hn := by
    obtain ⟨a, b, ha, h⟩ := (isStable_gaussianReal 0 hv).exists_affine n hn
    refine ⟨Real.sqrt n, Real.sqrt_pos.2 (by exact_mod_cast hn), ?_⟩
    have := convPow_eq_map_of_charFun (μ := gaussianReal 0 v) (n := n) (a := Real.sqrt n) (b := 0)
      fun t => by
        have hs : ((Real.sqrt n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
          rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; simp
        simp only [charFun_gaussianReal, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        push_cast
        linear_combination ((v : ℂ) * (t : ℂ) ^ 2 / 2) * hs
    simpa using this

end Gaussian

section SymmStable

/-- `IsSymmStable α c μ`: `μ` is a probability measure on `ℝ` whose characteristic function is
`t ↦ exp (-c |t| ^ α)`. For `0 < α ≤ 2` and `c > 0` these are exactly the symmetric
`α`-stable laws `SαS` ([ST, (1.2.3)], [Feller, §XVII.4], [EKM, §2.2]). -/
def IsSymmStable (α c : ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ t : ℝ, charFun μ t = (Real.exp (-(c * |t| ^ α)) : ℂ)

namespace IsSymmStable

variable {α c d : ℝ} {μ ν : Measure ℝ}

theorem isProbabilityMeasure' (h : IsSymmStable α c μ) : IsProbabilityMeasure μ := h.1

theorem charFun_eq (h : IsSymmStable α c μ) (t : ℝ) :
    charFun μ t = (Real.exp (-(c * |t| ^ α)) : ℂ) := h.2 t

/-- A symmetric `α`-stable law is determined by `(α, c)`. -/
theorem unique (hμ : IsSymmStable α c μ) (hν : IsSymmStable α c ν) : μ = ν := by
  have := hμ.1; have := hν.1
  exact Measure.ext_of_charFun (funext fun t => by rw [hμ.2, hν.2])

/-- Closure under convolution: `SαS(c) ∗ SαS(d) = SαS(c + d)`. -/
theorem conv (hμ : IsSymmStable α c μ) (hν : IsSymmStable α d ν) :
    IsSymmStable α (c + d) (μ ∗ ν) := by
  have := hμ.1; have := hν.1
  refine ⟨inferInstance, fun t => ?_⟩
  rw [charFun_conv, hμ.2, hν.2, ← ofReal_mul, ← Real.exp_add]
  congr 2; ring

/-- Closure under scaling: if `X ∼ SαS(c)` then `r X ∼ SαS(c |r| ^ α)`. -/
theorem map_mul (hμ : IsSymmStable α c μ) (r : ℝ) :
    IsSymmStable α (c * |r| ^ α) (μ.map (r * ·)) := by
  have := hμ.1
  refine ⟨inferInstance, fun t => ?_⟩
  rw [charFun_map_mul, hμ.2, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_assoc]

/-- Symmetric stable laws are symmetric: `-X ∼ X`. -/
theorem map_neg (hμ : IsSymmStable α c μ) : μ.map (fun x => -x) = μ := by
  have h := hμ.map_mul (-1)
  simp only [abs_neg, abs_one, Real.one_rpow, mul_one, neg_one_mul] at h
  exact h.unique hμ

/-- `μ^{*n}` is `SαS(n c)`. -/
theorem convPow (hμ : IsSymmStable α c μ) (n : ℕ) : IsSymmStable α (n * c) (convPow μ n) := by
  have := hμ.1
  refine ⟨inferInstance, fun t => ?_⟩
  rw [charFun_convPow, hμ.2, ← ofReal_pow, ← Real.exp_nat_mul]
  congr 2; ring

/-- **Symmetric `α`-stable laws are strictly stable**, with `aₙ = n ^ (1 / α)`
([Feller, §VI.1], [ST, Theorem 1.1.3]). -/
theorem isStrictlyStable (hμ : IsSymmStable α c μ) (hα : 0 < α) (hc : 0 < c) :
    IsStrictlyStable μ where
  isProbabilityMeasure := hμ.1
  ne_dirac := by
    refine ne_dirac_of_norm_charFun_lt_one (t := 1) ?_
    rw [hμ.2, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp [hc]
  exists_mul n hn := by
    have := hμ.1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨(n : ℝ) ^ α⁻¹, Real.rpow_pos_of_pos hn' _, ?_⟩
    have e : (n : ℝ) * c = c * |(n : ℝ) ^ α⁻¹| ^ α := by
      rw [abs_of_pos (Real.rpow_pos_of_pos hn' _), Real.rpow_inv_rpow hn'.le hα.ne']
      ring
    have h2 : IsSymmStable α (c * |(n : ℝ) ^ α⁻¹| ^ α) (Subexp.convPow μ n) :=
      e ▸ hμ.convPow n
    exact h2.unique (hμ.map_mul ((n : ℝ) ^ α⁻¹))

theorem isStable (hμ : IsSymmStable α c μ) (hα : 0 < α) (hc : 0 < c) : IsStable μ :=
  (hμ.isStrictlyStable hα hc).isStable

end IsSymmStable

/-- The centered Gaussian law `N(0, v)` is symmetric `2`-stable with `c = v / 2`. -/
theorem isSymmStable_gaussianReal (v : ℝ≥0) : IsSymmStable 2 (v / 2) (gaussianReal 0 v) := by
  refine ⟨inferInstance, fun t => ?_⟩
  rw [charFun_gaussianReal, ofReal_exp]
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  push_cast
  ring

end SymmStable

end ExtremeValueTheory
