/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.HeavyTails.LinearProcessSeries

/-!
# Tails of infinite linear processes with regularly varying noise, all `α > 0`

This file removes the restriction `α < 1` of `HeavyTails/LinearProcessSeries.lean`. Let
`(Z_j)_{j ≥ 0}` be iid copies of `Z₀`, with `P(|Z₀| > x)` regularly varying with index `-α`,
`α > 0` arbitrary, and let `(ψ_j)` be real coefficients with

  `∑_j |ψ_j|^δ < ∞` for some `0 < δ < min(α, 1)`.

Then `X = ∑_j ψ_j Z_j` converges absolutely almost surely, and
`P(X > x) / P(|Z₀| > x) → ∑_j |ψ_j|^α (p 1{ψ_j > 0} + (1 - p) 1{ψ_j < 0})`.

For `α < 1` this is exactly the condition of `LinearProcessSeries.lean`. For `α ≥ 1` the
condition `∑ |ψ_j|^δ < ∞` for some `δ < 1` is slightly stronger than the optimal conditions of
[EKM, Lemma A3.26] / Mikosch–Samorodnitsky (2000) (`δ = 1`, resp. `δ ≤ 2` with centred noise),
but it needs **no moment, centering or independence assumption** for the remainder bound, and it
covers all exponentially (and all `j^{-r}`, `r > 1`) decaying coefficients, in particular the
AR(1) coefficients `ψ_j = φ^j`. Absolute convergence of `∑ ψ_j Z_j` (rather than conditional
convergence of a centred series) is what is proved, which is why centering is not needed.

## Main results

* `LinearProcess.tsum_mul_le_rpow_tsum`: a weighted Hölder inequality for `ℝ≥0∞`-valued series,
  `∑ a_j y_j ≤ (∑ a_j^{γ + (1-γ) q} y_j^q)^{1/q}` when `∑ a_j^γ ≤ 1`, `0 ≤ γ ≤ 1 ≤ q`.
* `LinearProcess.exists_measure_tsum_gt_le_of_lt_one`: the uniform remainder bound for all
  `α > 0`: `P(∑_j |c_j| |Z_j| > x) ≤ K (∑_j |c_j|^δ) P(|Z₀| > x)` for `x ≥ x₀`, for every
  coefficient sequence with `∑_j |c_j|^δ ≤ 1`, where `0 < δ < α`, `δ < 1`.
* `LinearProcess.ae_summable_mul_of_lt_one`: almost sure absolute convergence of `∑ ψ_j Z_j`.
* `LinearProcess.tendsto_measureReal_tsum_mul_div_of_lt_one`: the tail asymptotics of `X`.

## Proof of the remainder bound

Put `q = α + 1 - δ > 1` and `β = δ + (1 - δ) q`. By the weighted Hölder inequality with weights
`|c_j|^δ` (summing to at most `1`),

  `∑_j |c_j| |Z_j| ≤ (∑_j |c_j|^β |Z_j|^q)^{1/q}`,

so `P(∑_j |c_j| |Z_j| > x) ≤ P(∑_j |c_j|^β |Z_j|^q > x^q)`. The variables `|Z_j|^q` have a
regularly varying tail of index `-α / q`, with `α / q < 1`, so the case `α < 1`
(`exists_measure_tsum_gt_le`) applies to them with the exponent `δ' = δ / β`; one checks
`δ' < α / q` (this is `(1 - δ)(α + 1)(α - δ) > 0`), and `(|c_j|^β)^{δ'} = |c_j|^δ`.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExtremeValueTheory

/-- Composition with a power: if `f` is regularly varying with index `ρ` and `r > 0`, then
`x ↦ f (x ^ r)` is regularly varying with index `ρ * r`. -/
theorem IsRegularlyVarying.comp_rpow {f : ℝ → ℝ} {ρ r : ℝ} (hf : IsRegularlyVarying f ρ)
    (hr : 0 < r) : IsRegularlyVarying (fun x => f (x ^ r)) (ρ * r) := by
  have ht : Tendsto (fun x : ℝ => x ^ r) atTop atTop := tendsto_rpow_atTop hr
  refine ⟨ht.eventually hf.1, fun c hc => ?_⟩
  have h := (hf.2 (c ^ r) (rpow_pos_of_pos hc r)).comp ht
  rw [← rpow_mul hc.le, mul_comm r ρ] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  simp only [Function.comp, mul_rpow hc.le hx]

namespace LinearProcess

/-- **Weighted Hölder inequality for series in `ℝ≥0∞`**: if `∑_j a_j^γ ≤ 1`, `0 ≤ γ ≤ 1 ≤ q`,
then `∑_j a_j y_j ≤ (∑_j a_j^{γ + (1 - γ) q} y_j^q)^{1/q}`. -/
theorem tsum_mul_le_rpow_tsum {a y : ℕ → ℝ≥0∞} {γ q : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hq : 1 ≤ q) (ha : ∑' j, a j ^ γ ≤ 1) :
    ∑' j, a j * y j ≤ (∑' j, a j ^ (γ + (1 - γ) * q) * y j ^ q) ^ q⁻¹ := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have h1γ : 0 ≤ 1 - γ := by linarith
  have hsplit : ∀ j, a j * y j = a j ^ γ * (a j ^ (1 - γ) * y j) := fun j => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hγ0 h1γ, add_sub_cancel, ENNReal.rpow_one]
  have hpow : ∀ j, a j ^ γ * (a j ^ (1 - γ) * y j) ^ q = a j ^ (γ + (1 - γ) * q) * y j ^ q :=
    fun j => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← mul_assoc,
        ← ENNReal.rpow_add_of_nonneg _ _ hγ0 (mul_nonneg h1γ hq0.le)]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  simp only [hsplit]
  refine (ENNReal.inner_le_weight_mul_Lp_of_nonneg s hq (fun j => a j ^ γ)
    (fun j => a j ^ (1 - γ) * y j)).trans ?_
  have hw : (∑ j ∈ s, a j ^ γ) ^ (1 - q⁻¹) ≤ 1 :=
    ENNReal.rpow_le_one ((ENNReal.sum_le_tsum s).trans ha)
      (sub_nonneg.2 (inv_le_one_of_one_le₀ hq))
  simp only [hpow]
  calc (∑ j ∈ s, a j ^ γ) ^ (1 - q⁻¹) * (∑ j ∈ s, a j ^ (γ + (1 - γ) * q) * y j ^ q) ^ q⁻¹
      ≤ 1 * (∑' j, a j ^ (γ + (1 - γ) * q) * y j ^ q) ^ q⁻¹ := by
        gcongr
        exact ENNReal.sum_le_tsum s
    _ = _ := one_mul _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Uniform bound for the remainder of a linear process, all `α > 0`** (`0 < δ < α`,
`δ < 1`). Let `P(|Z₀| > x)` be regularly varying with index `-α`. There are `K > 0`, `x₀ > 0` such
that for every sequence `(Z_j)` of identically distributed copies of `Z₀` (no independence, no
moment assumption), every coefficient sequence `(c_j)` with `∑ |c_j|^δ ≤ 1`, and every `x ≥ x₀`,
`P(∑_j |c_j| |Z_j| > x) ≤ K (∑_j |c_j|^δ) P(|Z₀| > x)` (the series taken in `[0, ∞]`).

Proof: weighted Hölder (`tsum_mul_le_rpow_tsum`) with `q = α + 1 - δ` reduces this to the case
`α / q < 1` of `exists_measure_tsum_gt_le`, applied to the variables `|Z_j|^q`. -/
theorem exists_measure_tsum_gt_le_of_lt_one [IsProbabilityMeasure P] {Z₀ : Ω → ℝ}
    (hZ₀ : Measurable Z₀) {α δ : ℝ} (hδ : 0 < δ) (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z₀ ω|}) (-α)) :
    ∃ K x₀ : ℝ, 0 < K ∧ 0 < x₀ ∧ ∀ Z : ℕ → Ω → ℝ, (∀ j, Measurable (Z j)) →
      (∀ j, IdentDistrib (Z j) Z₀ P P) → ∀ c : ℕ → ℝ, Summable (fun j => |c j| ^ δ) →
      ∑' j, |c j| ^ δ ≤ 1 → ∀ x ≥ x₀,
      P {ω | ENNReal.ofReal x < ∑' j, ENNReal.ofReal (|c j| * |Z j ω|)} ≤
        ENNReal.ofReal (K * (∑' j, |c j| ^ δ) * P.real {ω | x < |Z₀ ω|}) := by
  set q := α + 1 - δ with hq_def
  have hq1 : 1 < q := by rw [hq_def]; linarith
  have hq0 : 0 < q := zero_lt_one.trans hq1
  set β := δ + (1 - δ) * q with hβ_def
  have hβ : 0 < β := by rw [hβ_def]; nlinarith
  -- the exponents for the powers `|Z_j|^q`
  have hα'1 : α / q < 1 := by rw [div_lt_one hq0, hq_def]; linarith
  have hδ'α' : δ / β < α / q := by
    rw [div_lt_div_iff₀ hβ hq0]
    have : 0 < (1 - δ) * (α + 1) * (α - δ) := by
      apply mul_pos (mul_pos _ _) <;> linarith
    have e : α * β - δ * q = (1 - δ) * (α + 1) * (α - δ) := by rw [hβ_def, hq_def]; ring
    linarith
  set Y₀ : Ω → ℝ := fun ω => |Z₀ ω| ^ q with hY₀_def
  have hY₀ : Measurable Y₀ := (continuous_abs.measurable.comp hZ₀).pow_const q
  have hset : ∀ (V : Ω → ℝ) {x : ℝ}, 0 ≤ x →
      {ω | x ^ q < |(|V ω| ^ q)|} = {ω | x < |V ω|} := by
    intro V x hx
    ext ω
    simp only [mem_ofPred_eq, abs_of_nonneg (rpow_nonneg (abs_nonneg (V ω)) q)]
    exact rpow_lt_rpow_iff hx (abs_nonneg _) hq0
  have hLY : IsRegularlyVarying (fun x => P.real {ω | x < |Y₀ ω|}) (-(α / q)) := by
    have h := hL.comp_rpow (inv_pos.2 hq0)
    rw [show -α * q⁻¹ = -(α / q) by ring] at h
    refine h.congr ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    have := hset Z₀ (rpow_nonneg hx q⁻¹)
    rw [rpow_inv_rpow hx hq0.ne'] at this
    simp only [hY₀_def, this]
  obtain ⟨K, x₁, hK, hx₁, hR⟩ := exists_measure_tsum_gt_le hY₀ hδ'α' hα'1 hLY
  refine ⟨K, max 1 x₁, hK, lt_max_of_lt_left one_pos, fun Z hZ hident c hcs hc1 x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hxq : x₁ ≤ x ^ q := ((le_max_right _ _).trans hx).trans
    (by simpa using rpow_le_rpow_of_exponent_le hx1 hq1.le)
  have hcj : ∀ j, |c j| ≤ 1 := by
    intro j
    by_contra h
    push Not at h
    have h1 := one_lt_rpow h hδ
    have h2 := hcs.le_tsum j fun i _ => rpow_nonneg (abs_nonneg (c i)) δ
    linarith
  have hcoef : ∀ j, |(|c j| ^ β)| ^ (δ / β) = |c j| ^ δ := fun j => by
    rw [abs_of_nonneg (rpow_nonneg (abs_nonneg _) _), ← rpow_mul (abs_nonneg _),
      mul_div_cancel₀ _ hβ.ne']
  have h := hR (fun j ω => |Z j ω| ^ q)
    (fun j => (continuous_abs.measurable.comp (hZ j)).pow_const q)
    (fun j => (hident j).comp (continuous_abs.measurable.pow_const q)) (fun j => |c j| ^ β)
    (fun j => by
      rw [abs_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
      exact rpow_le_one (abs_nonneg _) (hcj j) hβ.le)
    (hcs.congr fun j => (hcoef j).symm) (x ^ q) hxq
  simp only [hcoef] at h
  rw [show {ω | x ^ q < |Y₀ ω|} = {ω | x < |Z₀ ω|} from hset Z₀ hx0] at h
  refine le_trans (measure_mono fun ω hω => ?_) h
  simp only [mem_ofPred_eq] at hω ⊢
  -- weighted Hölder
  have ha : ∑' j, ENNReal.ofReal |c j| ^ δ ≤ 1 := by
    simp only [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hδ.le]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => rpow_nonneg (abs_nonneg _) _) hcs]
    exact ENNReal.ofReal_le_one.2 hc1
  have hH := tsum_mul_le_rpow_tsum (a := fun j => ENNReal.ofReal |c j|)
    (y := fun j => ENNReal.ofReal |Z j ω|) hδ.le hδ1.le hq1.le ha
  have hterm : ∀ j, ENNReal.ofReal |c j| ^ (δ + (1 - δ) * q) * ENNReal.ofReal |Z j ω| ^ q =
      ENNReal.ofReal (|(|c j| ^ β)| * |(|Z j ω| ^ q)|) := fun j => by
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hβ.le,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le,
      ← ENNReal.ofReal_mul (rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (rpow_nonneg (abs_nonneg _) _), abs_of_nonneg (rpow_nonneg (abs_nonneg _) _)]
  simp only [hterm, ← ENNReal.ofReal_mul (abs_nonneg _)] at hH
  have h3 := ENNReal.rpow_lt_rpow (hω.trans_le hH) hq0
  rwa [← ENNReal.rpow_mul, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hx0 hq0.le] at h3

end LinearProcess

end ExtremeValueTheory
