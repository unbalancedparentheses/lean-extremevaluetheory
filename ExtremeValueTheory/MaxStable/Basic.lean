/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Simple max-stable random vectors

A probability law `μ` on `ℝ^ι` is **simple max-stable** if its
margins are unit Fréchet, `μ {x | x i ≤ y} = exp (-1 / y)` for `y > 0`, and its distribution
function `F(y) = μ (Iic y)` satisfies

  `F(y) ^ n = F(y / n)` for all `n ≥ 1` and all `y` with positive coordinates,

i.e. the componentwise maximum of `n` i.i.d. copies of a vector `Y` with law `μ` has the law of
`n Y` ([dHF, §6.1.3]; [Res87, §5.4]).

The **exponent function** is `V(y) = -log F(y)`. It is positive and finite on `(0, ∞)^ι`, and
homogeneous of order `-1`: `V(t y) = V(y) / t`; equivalently `F(t y) = F(y) ^ (1 / t)` for all
real `t > 0`. The integer case is the definition; the rational case follows by taking roots and
the real case by monotonicity of `F` in `t` and continuity of `t ↦ F(y) ^ (1 / t)`.

## Main definitions and results

* `ExtremeValueTheory.IsSimpleMaxStable μ`: `μ` is a simple max-stable law on `ι → ℝ`.
* `ExtremeValueTheory.maxStableExponent μ y`: the exponent function `V(y) = -log F(y)`.
* `IsSimpleMaxStable.measure_Iic_pos`: `F(y) > 0` on `(0, ∞)^ι`.
* `IsSimpleMaxStable.measureReal_Iic_smul`: `F(t y) = F(y) ^ (1 / t)` for real `t > 0`.
* `IsSimpleMaxStable.maxStableExponent_smul`: `V(t y) = V(y) / t`.
* `IsSimpleMaxStable.exp_neg_maxStableExponent`: `F(y) = exp (-V(y))`.
* `IsSimpleMaxStable.inv_le_maxStableExponent`, `IsSimpleMaxStable.maxStableExponent_le_sum_inv`:
  `max_i 1 / y i ≤ V(y) ≤ ∑ i, 1 / y i` (complete dependence and independence are the extreme
  cases).

The converse of the spectral representation of `MaxStable/Spectral.lean` (every simple
max-stable law has the form `F(y) = exp (-∫ max_i w i / y i dH(w))`, [dHF, Theorem 6.1.9 "⇒"])
is not formalized: it needs the construction of the exponent measure on `[0, ∞]^ι \ {0}` from
`V`, by vague limits of `n P(Y / n ∈ ·)`.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Chapter 6 [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Chapter 5 [Res87].
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ExtremeValueTheory

variable {ι : Type*}

/-- A law `μ` on `ι → ℝ` is **simple max-stable** if it is a probability measure with unit
Fréchet margins and `F(y) ^ n = F(y / n)` for every `n ≥ 1` and every `y` with positive
coordinates, where `F(y) = μ (Iic y) = μ {x | ∀ i, x i ≤ y i}` ([dHF, §6.1.3]). -/
structure IsSimpleMaxStable (μ : Measure (ι → ℝ)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  /-- The margins are unit Fréchet: `P(Y i ≤ y) = exp (-1 / y)` for `y > 0`. -/
  measure_le : ∀ i, ∀ y : ℝ, 0 < y → μ {x | x i ≤ y} = ENNReal.ofReal (Real.exp (-y⁻¹))
  /-- Max-stability: `F(y) ^ n = F(y / n)`. -/
  measure_Iic_pow : ∀ n : ℕ, 0 < n → ∀ y : ι → ℝ, (∀ i, 0 < y i) →
    μ (Iic y) ^ n = μ (Iic ((n : ℝ)⁻¹ • y))

/-- The **exponent function** `V(y) = -log P(Y ≤ y)` of a law on `ι → ℝ`. -/
noncomputable def maxStableExponent (μ : Measure (ι → ℝ)) (y : ι → ℝ) : ℝ :=
  -Real.log (μ.real (Iic y))

namespace IsSimpleMaxStable

variable {μ : Measure (ι → ℝ)}

lemma smul_le_smul_of_le {s t : ℝ} (hst : s ≤ t) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    s • y ≤ t • y := fun i ↦ by
  simpa using mul_le_mul_of_nonneg_right hst (hy i).le

/-- `F(y) ^ n = F(y / n)` for the real-valued distribution function. -/
lemma measureReal_Iic_pow (h : IsSimpleMaxStable μ) {n : ℕ} (hn : 0 < n) {y : ι → ℝ}
    (hy : ∀ i, 0 < y i) : μ.real (Iic y) ^ n = μ.real (Iic ((n : ℝ)⁻¹ • y)) := by
  simp only [measureReal_def, ← ENNReal.toReal_pow, h.measure_Iic_pow n hn y hy]

variable [Finite ι]

/-- The distribution function of a simple max-stable law is positive on `(0, ∞)^ι`. -/
lemma measure_Iic_pos (h : IsSimpleMaxStable μ) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    0 < μ (Iic y) := by
  have := h.isProbabilityMeasure
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  have hn (n : ℕ) : μ (Iic (((n : ℝ) + 1) • y)) = 0 := by
    have hpos : ∀ i, 0 < (((n : ℝ) + 1) • y) i := fun i ↦ by
      simpa using mul_pos (by positivity : (0 : ℝ) < n + 1) (hy i)
    have := h.measure_Iic_pow (n + 1) n.succ_pos _ hpos
    rw [show ((((n + 1 : ℕ)) : ℝ)⁻¹ • (((n : ℝ) + 1) • y)) = y by
      rw [smul_smul]; push_cast; rw [inv_mul_cancel₀ (by positivity), one_smul], h0] at this
    exact pow_eq_zero_iff n.succ_ne_zero |>.1 this
  have hmono : Monotone fun n : ℕ ↦ Iic (((n : ℝ) + 1) • y) := fun m n hmn ↦
    Iic_subset_Iic.2 (smul_le_smul_of_le (by linarith [(Nat.cast_le.2 hmn : (m : ℝ) ≤ n)]) hy)
  have hunion : (⋃ n : ℕ, Iic (((n : ℝ) + 1) • y)) = univ := by
    refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    have hev : ∀ᶠ n : ℕ in atTop, ∀ i, x i ≤ ((n : ℝ) + 1) * y i := by
      refine Filter.eventually_all.2 fun i ↦ ?_
      exact ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
        (hy i)).eventually_ge_atTop (x i)
    obtain ⟨n, hn⟩ := hev.exists
    exact ⟨n, fun i ↦ by simpa using hn i⟩
  have := hmono.measure_iUnion (μ := μ)
  rw [hunion, measure_univ] at this
  simp [hn] at this

lemma measureReal_Iic_pos (h : IsSimpleMaxStable μ) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    0 < μ.real (Iic y) := by
  have := h.isProbabilityMeasure
  exact ENNReal.toReal_pos (h.measure_Iic_pos hy).ne' (measure_ne_top _ _)

omit [Finite ι] in
/-- Rational homogeneity: `F((m / n) y) = F(y) ^ (n / m)`. -/
lemma measureReal_Iic_div_smul (h : IsSimpleMaxStable μ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    μ.real (Iic (((m : ℝ) / n) • y)) = μ.real (Iic y) ^ ((n : ℝ) / m) := by
  have hz : ∀ i, 0 < (((m : ℝ) / n) • y) i := fun i ↦ by
    simpa using mul_pos (by positivity : (0 : ℝ) < m / n) (hy i)
  have h1 := h.measureReal_Iic_pow hm hz
  rw [smul_smul, show (m : ℝ)⁻¹ * (m / n) = (n : ℝ)⁻¹ by field_simp,
    ← h.measureReal_Iic_pow hn hy] at h1
  have h0 := measureReal_nonneg (μ := μ) (s := Iic (((m : ℝ) / n) • y))
  rw [← Real.pow_rpow_inv_natCast h0 hm.ne', h1, ← Real.rpow_natCast,
    ← Real.rpow_mul measureReal_nonneg, div_eq_mul_inv]

/-- **Homogeneity of the distribution function**: `F(t y) = F(y) ^ (1 / t)` for real `t > 0`. -/
theorem measureReal_Iic_smul (h : IsSimpleMaxStable μ) {t : ℝ} (ht : 0 < t) {y : ι → ℝ}
    (hy : ∀ i, 0 < y i) : μ.real (Iic (t • y)) = μ.real (Iic y) ^ t⁻¹ := by
  have := h.isProbabilityMeasure
  set g : ℝ → ℝ := fun s ↦ μ.real (Iic (s • y)) with hg
  set k : ℝ → ℝ := fun s ↦ μ.real (Iic y) ^ s⁻¹ with hk
  have gmono : Monotone g := fun s s' hss' ↦ measureReal_mono (Iic_subset_Iic.2
    (smul_le_smul_of_le hss' hy))
  have hgk {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : g ((m : ℝ) / n) = k ((m : ℝ) / n) := by
    simp only [hg, hk, h.measureReal_Iic_div_smul hm hn hy, inv_div]
  have hcont : ContinuousAt k t :=
    (Real.continuousAt_const_rpow (h.measureReal_Iic_pos hy).ne').comp
      (continuousAt_inv₀ ht.ne')
  -- rationals with positive numerator between two reals
  have hbtwn {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ a < (m : ℝ) / n ∧ (m : ℝ) / n < b := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hab)
    refine ⟨⌊a * (n + 1)⌋₊ + 1, n + 1, Nat.succ_pos _, Nat.succ_pos _, ?_, ?_⟩
    · rw [lt_div_iff₀ (by positivity)]
      push_cast
      exact Nat.lt_floor_add_one _
    · rw [div_lt_iff₀ (by positivity)]
      push_cast
      have := Nat.floor_le (mul_nonneg ha (by positivity : (0 : ℝ) ≤ n + 1))
      rw [div_lt_iff₀ (by positivity)] at hn
      nlinarith
  change g t = k t
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hlt))
    obtain ⟨m, n, hm, hn, h1, h2⟩ := hbtwn ht.le (lt_add_of_pos_right t hδ)
    have := hball (y := (m : ℝ) / n) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [← hgk hm hn] at this
    exact absurd (gmono h1.le) (not_le.2 this)
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds hlt))
    obtain ⟨m, n, hm, hn, h1, h2⟩ := hbtwn (le_max_right (t - δ) 0) (max_lt (by linarith) ht)
    have := hball (y := (m : ℝ) / n) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_left (t - δ) 0])
    rw [← hgk hm hn] at this
    exact absurd (gmono h2.le) (not_le.2 this)

/-- **Homogeneity of the exponent function**: `V(t y) = V(y) / t` for `t > 0`. -/
theorem maxStableExponent_smul (h : IsSimpleMaxStable μ) {t : ℝ} (ht : 0 < t) {y : ι → ℝ}
    (hy : ∀ i, 0 < y i) : maxStableExponent μ (t • y) = t⁻¹ * maxStableExponent μ y := by
  rw [maxStableExponent, maxStableExponent, h.measureReal_Iic_smul ht hy,
    Real.log_rpow (h.measureReal_Iic_pos hy), mul_neg]

/-- The exponent function is finite and nonnegative, and `F(y) = exp (-V(y))`. -/
theorem exp_neg_maxStableExponent (h : IsSimpleMaxStable μ) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    Real.exp (-maxStableExponent μ y) = μ.real (Iic y) := by
  rw [maxStableExponent, neg_neg, Real.exp_log (h.measureReal_Iic_pos hy)]

/-- **Lower bound of the exponent function**: `V(y) ≥ 1 / y i` for every coordinate `i`. -/
theorem inv_le_maxStableExponent (h : IsSimpleMaxStable μ) {y : ι → ℝ} (hy : ∀ i, 0 < y i)
    (i : ι) : (y i)⁻¹ ≤ maxStableExponent μ y := by
  have := h.isProbabilityMeasure
  have hle : μ.real (Iic y) ≤ Real.exp (-(y i)⁻¹) := by
    have h1 : μ.real {x | x i ≤ y i} = Real.exp (-(y i)⁻¹) := by
      rw [measureReal_def, h.measure_le i (y i) (hy i), ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [← h1]
    exact measureReal_mono fun x hx ↦ hx i
  rw [maxStableExponent, le_neg, ← Real.log_exp (-(y i)⁻¹)]
  exact Real.log_le_log (h.measureReal_Iic_pos hy) hle

omit [Finite ι] in
/-- The marginal tail: `P(Y i > c) ≤ 1 / c`. -/
lemma measureReal_lt_apply_le (h : IsSimpleMaxStable μ) (i : ι) {c : ℝ} (hc : 0 < c) :
    μ.real {x | c < x i} ≤ c⁻¹ := by
  have := h.isProbabilityMeasure
  have hmeas : MeasurableSet {x : ι → ℝ | x i ≤ c} :=
    measurableSet_le (measurable_pi_apply i) measurable_const
  rw [show {x : ι → ℝ | c < x i} = {x | x i ≤ c}ᶜ by ext; simp, probReal_compl_eq_one_sub hmeas,
    measureReal_def, h.measure_le i c hc, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  linarith [Real.add_one_le_exp (-c⁻¹)]

/-- **Upper bound of the exponent function**: `V(y) ≤ ∑ i, 1 / y i` (the value for independent
components). Together with `inv_le_maxStableExponent`, `max_i 1 / y i ≤ V(y) ≤ ∑ i, 1 / y i`. -/
theorem maxStableExponent_le_sum_inv [Fintype ι] (h : IsSimpleMaxStable μ) {y : ι → ℝ}
    (hy : ∀ i, 0 < y i) : maxStableExponent μ y ≤ ∑ i, (y i)⁻¹ := by
  have := h.isProbabilityMeasure
  set V := maxStableExponent μ y with hV
  set S := ∑ i, (y i)⁻¹ with hS
  have hV0 : 0 ≤ V := by
    rw [hV, maxStableExponent, neg_nonneg]
    exact Real.log_nonpos measureReal_nonneg measureReal_le_one
  have key {t : ℝ} (ht : 0 < t) : V ≤ S + S * V / t := by
    have hty : ∀ i, 0 < (t • y) i := fun i ↦ by simpa using mul_pos ht (hy i)
    -- `1 - F(t y) ≤ S / t` by the union bound
    have hunion : 1 - μ.real (Iic (t • y)) ≤ S / t := by
      rw [← probReal_compl_eq_one_sub measurableSet_Iic]
      have hcompl : (Iic (t • y))ᶜ = ⋃ i, {x : ι → ℝ | (t • y) i < x i} := by
        ext x; simp [Pi.le_def, not_forall]
      rw [hcompl]
      refine (measureReal_iUnion_fintype_le _).trans ?_
      refine (Finset.sum_le_sum fun i _ ↦ h.measureReal_lt_apply_le i (hty i)).trans ?_
      rw [hS, Finset.sum_div]
      refine Finset.sum_le_sum fun i _ ↦ le_of_eq ?_
      simp only [Pi.smul_apply, smul_eq_mul, mul_inv]
      field_simp
    -- `F(t y) = exp (-V / t) ≤ 1 / (1 + V / t)`
    have hF : μ.real (Iic (t • y)) = Real.exp (-(V / t)) := by
      rw [← h.exp_neg_maxStableExponent hty, h.maxStableExponent_smul ht hy, hV, inv_mul_eq_div]
    have hexp : Real.exp (-(V / t)) * (1 + V / t) ≤ 1 := by
      have h1 := Real.add_one_le_exp (V / t)
      have h2 : Real.exp (-(V / t)) * Real.exp (V / t) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      nlinarith [Real.exp_pos (-(V / t))]
    rw [hF] at hunion
    have hVt : 0 ≤ V / t := div_nonneg hV0 ht.le
    -- `(V / t) / (1 + V / t) ≤ 1 - exp (-V / t) ≤ S / t`
    have : V / t ≤ S / t * (1 + V / t) := by nlinarith [Real.exp_pos (-(V / t))]
    have h3 : V / t * t = V := div_mul_cancel₀ V ht.ne'
    have h4 : S / t * t = S := div_mul_cancel₀ S ht.ne'
    calc V = V / t * t := h3.symm
      _ ≤ S / t * (1 + V / t) * t := by gcongr
      _ = S + S * V / t := by field_simp
  have htend : Tendsto (fun t : ℝ ↦ S + S * V / t) atTop (𝓝 S) := by
    have := (tendsto_const_nhds (x := S)).add
      ((tendsto_const_nhds (x := S * V)).div_atTop (tendsto_id (x := (atTop : Filter ℝ))))
    simpa using this
  exact ge_of_tendsto htend ((eventually_gt_atTop 0).mono fun t ht ↦ key ht)

end IsSimpleMaxStable

end ExtremeValueTheory
