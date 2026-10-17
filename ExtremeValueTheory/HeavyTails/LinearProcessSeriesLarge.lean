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

/-- The tails `∑_{j ≥ m} |ψ_j|^δ` of a convergent series are eventually at most `1`. -/
theorem exists_tsum_add_le_one (ψ : ℕ → ℝ) (δ : ℝ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∑' j, |ψ (j + m)| ^ δ ≤ 1 := by
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    ((tendsto_sum_nat_add fun j => |ψ j| ^ δ).eventually (ge_mem_nhds zero_lt_one))
  exact ⟨m₀, hm₀⟩

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

/-- **Almost sure convergence of the linear process, all `α > 0`** (`0 < δ < α`, `δ < 1`): if
`(Z_j)` are identically distributed copies of `Z₀` with `P(|Z₀| > x)` regularly varying with
index `-α` and `∑ |ψ_j|^δ < ∞`, then `∑ ψ_j Z_j` converges absolutely almost surely. No
independence, moment or centering assumption is needed. -/
theorem ae_summable_mul_of_lt_one [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ} {Z₀ : Ω → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (hZ₀ : Measurable Z₀) (hident : ∀ j, IdentDistrib (Z j) Z₀ P P)
    {α δ : ℝ} (hδ : 0 < δ) (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z₀ ω|}) (-α))
    {ψ : ℕ → ℝ} (hψ : Summable fun j => |ψ j| ^ δ) :
    ∀ᵐ ω ∂P, Summable fun j => ψ j * Z j ω := by
  obtain ⟨K, x₀, hK, hx₀, hR⟩ := exists_measure_tsum_gt_le_of_lt_one hZ₀ hδ hδα hδ1 hL
  obtain ⟨m₀, hm₀⟩ := exists_tsum_add_le_one ψ δ
  have hR' := hR (fun j => Z (j + m₀)) (fun j => hZ _) (fun j => hident _) (fun j => ψ (j + m₀))
    ((summable_nat_add_iff m₀).2 hψ) (hm₀ m₀ le_rfl)
  set T := ∑' j, |ψ (j + m₀)| ^ δ
  set R : Ω → ℝ≥0∞ := fun ω => ∑' j, ENNReal.ofReal (|ψ (j + m₀)| * |Z (j + m₀) ω|)
  have hnull : P {ω | R ω = ⊤} = 0 := by
    refine le_antisymm ?_ zero_le
    have hlim : Tendsto (fun x => ENNReal.ofReal (K * T * P.real {ω | x < |Z₀ ω|})) atTop
        (𝓝 (ENNReal.ofReal (K * T * 0))) :=
      ENNReal.tendsto_ofReal (tendsto_const_nhds.mul
        (tendsto_measureReal_lt (continuous_abs.measurable.comp hZ₀)))
    rw [mul_zero, ENNReal.ofReal_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop x₀] with x hx
    exact (measure_mono fun ω (hω : R ω = ⊤) => (show ENNReal.ofReal x < R ω by
      rw [hω]; exact ENNReal.ofReal_lt_top)).trans (hR' x hx)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hne
  exact hω (abs_tsum_sub_sum_le (ψ := ψ) (z := fun j => Z j ω) (m := m₀) ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal hne).ge).1

/-- **Tails of infinite moving averages with regularly varying noise, all `α > 0`** ([EKM, Lemma
A3.26], [DR85], [Mikosch–Samorodnitsky 2000], [KS20, Chapter 15]). Let `(Z_j)_{j ≥ 0}` be
independent copies of `Z₀`, with `P(|Z₀| > x)` regularly varying with index `-α`, `α > 0`, and
tail balance `P(Z₀ > x) / P(|Z₀| > x) → p`. If `∑ |ψ_j|^δ < ∞` for some `0 < δ < α` with `δ < 1`, then
`X = ∑_j ψ_j Z_j` (which converges absolutely almost surely, `ae_summable_mul_of_lt_one`)
satisfies `P(X > x) / P(|Z₀| > x) → ∑_j |ψ_j|^α (p 1{ψ_j > 0} + (1 - p) 1{ψ_j < 0})`.
No moment or centering assumption on `Z₀` is needed. -/
theorem tendsto_measureReal_tsum_mul_div_of_lt_one [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ}
    {Z₀ : Ω → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (hZ₀ : Measurable Z₀) (hind : iIndepFun Z P)
    (hident : ∀ j, IdentDistrib (Z j) Z₀ P P) {α δ p : ℝ} (hδ : 0 < δ) (hδα : δ < α)
    (hδ1 : δ < 1) (hL : IsRegularlyVarying (fun x => P.real {ω | x < |Z₀ ω|}) (-α))
    (hp : Tendsto (fun x => P.real {ω | x < Z₀ ω} / P.real {ω | x < |Z₀ ω|}) atTop (𝓝 p))
    {ψ : ℕ → ℝ} (hψ : Summable fun j => |ψ j| ^ δ) :
    Tendsto (fun x => P.real {ω | x < ∑' j, ψ j * Z j ω} / P.real {ω | x < |Z₀ ω|}) atTop
      (𝓝 (∑' j, tailWeight α p (ψ j))) := by
  set L : ℝ → ℝ := fun x => P.real {ω | x < |Z₀ ω|} with hL_def
  obtain ⟨hp0, hp1⟩ := tailBalance_mem_Icc hL.1 hp
  obtain ⟨K, x₀, hK, hx₀, hR⟩ := exists_measure_tsum_gt_le_of_lt_one hZ₀ hδ hδα hδ1 hL
  obtain ⟨m₀, hm₀⟩ := exists_tsum_add_le_one ψ δ
  set w : ℕ → ℝ := fun j => tailWeight α p (ψ j) with hw_def
  have hw0 : ∀ j, 0 ≤ w j := fun j => (tailWeight_nonneg_le hp0 hp1).1
  have hws : Summable w := summable_tailWeight hδ hδα.le hp0 hp1 hψ
  set c := ∑' j, w j with hc_def
  -- the remainders
  set T : ℕ → ℝ := fun m => ∑' j, |ψ (j + m)| ^ δ with hT_def
  have hT : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add fun j => |ψ j| ^ δ
  set R : ℕ → Ω → ℝ≥0∞ := fun m ω => ∑' j, ENNReal.ofReal (|ψ (j + m)| * |Z (j + m) ω|)
    with hR_def
  -- the remainder bound, in real form
  have hRb : ∀ m ≥ m₀, ∀ y ≥ x₀, P.real {ω | ENNReal.ofReal y < R m ω} ≤ K * T m * L y := by
    intro m hm y hy
    have h := hR (fun j => Z (j + m)) (fun j => hZ _) (fun j => hident _) (fun j => ψ (j + m))
      ((summable_nat_add_iff m).2 hψ) (hm₀ m hm) y hy
    have hT0 : 0 ≤ T m := tsum_nonneg fun j => rpow_nonneg (abs_nonneg _) _
    exact ENNReal.toReal_le_of_le_ofReal (by have := hK.le; positivity) h
  -- the remainder is negligible
  have hRlim : ∀ m ≥ m₀, ∀ {ε : ℝ}, 0 < ε → ∀ {D : ℝ}, K * T m * ε ^ (-α) < D →
      ∀ᶠ x in atTop, P.real {ω | ENNReal.ofReal (ε * x) < R m ω} / L x < D := by
    intro m hm ε hε D hD
    have hlim : Tendsto (fun x => K * T m * (L (ε * x) / L x)) atTop
        (𝓝 (K * T m * ε ^ (-α))) := tendsto_const_nhds.mul (hL.2 ε hε)
    filter_upwards [hlim.eventually (gt_mem_nhds hD), hL.1,
      (tendsto_id.const_mul_atTop hε).eventually (eventually_ge_atTop x₀)] with x hx hLx hεx
    refine lt_of_le_of_lt ?_ hx
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hLx]
    exact hRb m hm _ hεx
  -- finite moving averages
  have hfin : ∀ m : ℕ, Tendsto (fun x => P.real {ω | x < ∑ j ∈ Finset.range m, ψ j * Z j ω} /
      L x) atTop (𝓝 (∑ j ∈ Finset.range m, w j)) := fun m =>
    tendsto_measureReal_sum_mul_div hZ hZ₀ hind hident hL hp ψ _
  have hcm : Tendsto (fun m => ∑ j ∈ Finset.range m, w j) atTop (𝓝 c) :=
    hws.hasSum.tendsto_sum_nat
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro A hA
    obtain ⟨ε, hε, -, hAε⟩ := exists_eps' (α := α) hA
    set D := c * (1 + ε) ^ (-α) - A with hD
    have hD0 : 0 < D := by rw [hD]; linarith
    have hm1 : ∀ᶠ m in atTop, A + D / 2 < (∑ j ∈ Finset.range m, w j) * (1 + ε) ^ (-α) := by
      have := hcm.mul_const ((1 + ε) ^ (-α))
      exact this.eventually (lt_mem_nhds (by rw [hD]; linarith))
    have hm2 : ∀ᶠ m in atTop, K * T m * ε ^ (-α) < D / 4 := by
      have : Tendsto (fun m => K * T m * ε ^ (-α)) atTop (𝓝 (K * 0 * ε ^ (-α))) :=
        (tendsto_const_nhds.mul hT).mul_const _
      rw [mul_zero, zero_mul] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm1, hm2, hm⟩ := (hm1.and (hm2.and (eventually_ge_atTop m₀))).exists
    have hS := tendsto_comp_mul_div hL (hfin m) (show (0 : ℝ) < 1 + ε by linarith)
    filter_upwards [hS.eventually (lt_mem_nhds hm1), hRlim m hm hε hm2, hL.1,
      eventually_ge_atTop 0] with x hx1 hx2 hLx hx0
    have hsub : {ω | (1 + ε) * x < ∑ j ∈ Finset.range m, ψ j * Z j ω} ⊆
        {ω | x < ∑' j, ψ j * Z j ω} ∪ {ω | ENNReal.ofReal (ε * x) < R m ω} := by
      intro ω hω
      simp only [mem_ofPred_eq, mem_union] at hω ⊢
      by_cases h : ENNReal.ofReal (ε * x) < R m ω
      · exact Or.inr h
      · left
        have := (abs_tsum_sub_sum_le (ψ := ψ) (z := fun j => Z j ω) (m := m)
          (by positivity) (not_lt.1 h)).2
        rw [abs_le] at this
        linarith
    have hle := (measureReal_mono (μ := P) hsub (measure_ne_top P _)).trans
      (measureReal_union_le _ _)
    have : P.real {ω | (1 + ε) * x < ∑ j ∈ Finset.range m, ψ j * Z j ω} / L x ≤
        P.real {ω | x < ∑' j, ψ j * Z j ω} / L x +
          P.real {ω | ENNReal.ofReal (ε * x) < R m ω} / L x := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hle hLx.le
    linarith
  · -- upper bound
    intro B hB
    obtain ⟨ε, hε, hε1, -, hBε⟩ := exists_eps (c := c) (α := α) 1 hB
    rw [one_mul] at hBε
    set D := B - c * (1 - ε) ^ (-α) with hD
    have hD0 : 0 < D := by rw [hD]; linarith
    have hm2 : ∀ᶠ m in atTop, K * T m * ε ^ (-α) < D / 2 := by
      have : Tendsto (fun m => K * T m * ε ^ (-α)) atTop (𝓝 (K * 0 * ε ^ (-α))) :=
        (tendsto_const_nhds.mul hT).mul_const _
      rw [mul_zero, zero_mul] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm2, hm⟩ := (hm2.and (eventually_ge_atTop m₀)).exists
    have hcm_le : (∑ j ∈ Finset.range m, w j) * (1 - ε) ^ (-α) ≤ c * (1 - ε) ^ (-α) :=
      mul_le_mul_of_nonneg_right (hws.sum_le_tsum _ fun j _ => hw0 j)
        (rpow_nonneg (by linarith) _)
    have hS := tendsto_comp_mul_div hL (hfin m) (show (0 : ℝ) < 1 - ε by linarith)
    filter_upwards [hS.eventually (gt_mem_nhds (show _ < B - D / 2 by rw [hD] at *; linarith)),
      hRlim m hm hε hm2, hL.1, eventually_ge_atTop 0] with x hx1 hx2 hLx hx0
    have hsub : {ω | x < ∑' j, ψ j * Z j ω} ⊆
        {ω | (1 - ε) * x < ∑ j ∈ Finset.range m, ψ j * Z j ω} ∪
          {ω | ENNReal.ofReal (ε * x) < R m ω} := by
      intro ω hω
      simp only [mem_ofPred_eq, mem_union] at hω ⊢
      by_cases h : ENNReal.ofReal (ε * x) < R m ω
      · exact Or.inr h
      · left
        have := (abs_tsum_sub_sum_le (ψ := ψ) (z := fun j => Z j ω) (m := m)
          (by positivity) (not_lt.1 h)).2
        rw [abs_le] at this
        linarith
    have hle := (measureReal_mono (μ := P) hsub (measure_ne_top P _)).trans
      (measureReal_union_le _ _)
    have : P.real {ω | x < ∑' j, ψ j * Z j ω} / L x ≤
        P.real {ω | (1 - ε) * x < ∑ j ∈ Finset.range m, ψ j * Z j ω} / L x +
          P.real {ω | ENNReal.ofReal (ε * x) < R m ω} / L x := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hle hLx.le
    linarith


end LinearProcess

end ExtremeValueTheory
