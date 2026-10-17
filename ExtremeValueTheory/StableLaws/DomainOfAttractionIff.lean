/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLTOne
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverseAsymmetric
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Domains of attraction of stable laws
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal ComplexConjugate

namespace ExtremeValueTheory

open Subexp GCLT StableIntegral GCLTConverse

section Index

/-- `IsStableIndex α μ`: `μ` is a stable law with index `α`, i.e. for every `n ≥ 1` the
convolution power `μ^{*n}` is the law of `n ^ (1 / α) X + bₙ`, `X ∼ μ`
([Feller, Vol. II, §VI.1, Theorem 1]: every stable law has norming constants `n ^ (1 / α)` for a
unique `0 < α ≤ 2`). -/
def IsStableIndex (α : ℝ) (μ : Measure ℝ) : Prop :=
  IsStable μ ∧ ∀ n : ℕ, 1 ≤ n → ∃ b : ℝ, convPow μ n = μ.map (fun x => (n : ℝ) ^ α⁻¹ * x + b)

variable {μ : Measure ℝ}

/-- Shifting a law shifts the convolution powers: if `μ^{*n} = law (a X + b)` then
`(μ ∗ δₘ)^{*n} = law (a Y + b + n m - a m)` for `Y ∼ μ ∗ δₘ`. -/
theorem convPow_map_add_eq [IsProbabilityMeasure μ] {n : ℕ} {a b : ℝ} (m : ℝ)
    (h : convPow μ n = μ.map (fun x => a * x + b)) :
    convPow (μ.map (· + m)) n = (μ.map (· + m)).map (fun x => a * x + (b + n * m - a * m)) := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have h1 := congrArg (fun ρ => charFun ρ t) h
  simp only [charFun_convPow, charFun_map_mul_add] at h1
  rw [charFun_convPow, charFun_map_mul_add, charFun_map_add_const, charFun_map_add_const, mul_pow,
    h1]
  simp only [RCLike.inner_apply, conj_trivial, ← Complex.exp_nat_mul, mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem IsStableIndex.map_add_const {α : ℝ} (h : IsStableIndex α μ) (m : ℝ) :
    IsStableIndex α (μ.map (· + m)) := by
  have := h.1.isProbabilityMeasure
  refine ⟨⟨inferInstance, fun x hx => h.1.ne_dirac (x - m) ?_, fun n hn => ?_⟩, fun n hn => ?_⟩
  · have e : μ = (μ.map (· + m)).map (· - m) := by
      rw [Measure.map_map (measurable_sub_const m) (measurable_add_const m)]
      simp only [Function.comp_def, add_sub_cancel_right, Measure.map_id']
    rw [e, hx, Measure.map_dirac' (measurable_sub_const m)]
  · obtain ⟨a, b, ha, hab⟩ := h.1.exists_affine n hn
    exact ⟨a, _, ha, convPow_map_add_eq m hab⟩
  · obtain ⟨b, hb⟩ := h.2 n hn
    exact ⟨_, convPow_map_add_eq m hb⟩

theorem IsStableIndex.of_map_add_const {α m : ℝ} (h : IsStableIndex α (μ.map (· + m))) :
    IsStableIndex α μ := by
  have e : (μ.map (· + m)).map (· + -m) = μ := by
    rw [Measure.map_map (measurable_add_const _) (measurable_add_const m)]
    simp only [Function.comp_def, add_neg_cancel_right, Measure.map_id']
  simpa [e] using h.map_add_const (-m)

/-- A law with characteristic function `exp (-c |t|^α + i e sign(t) |t|^α)`, `α, c > 0`, is
stable with index `α` (and `bₙ = 0`). -/
theorem HasStableCharFun.isStableIndex {α c e : ℝ} (h : HasStableCharFun α c e μ) (hα0 : 0 < α)
    (hc : 0 < c) : IsStableIndex α μ := by
  refine ⟨h.isStable hα0 hc, fun n hn => ⟨0, ?_⟩⟩
  have := h.1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine Measure.ext_of_charFun (funext fun t => ?_)
  simp only [add_zero]
  rw [charFun_convPow, charFun_map_mul, h.2, h.2, ← Complex.exp_nat_mul,
    stableExponent_mul (rpow_pos_of_pos hn' _), rpow_inv_rpow hn'.le hα0.ne']
  push_cast; ring_nf

/-- **`1`-stable laws are stable** ([Feller, §XVII.3], [ST, Definition 1.1.6]): a law with
characteristic function `exp (-c |t| + i e (κ t - t log |t|))`, `c > 0`, satisfies
`μ^{*n} = law (n X + e n log n)`. -/
theorem HasStableOneCharFun.isStableIndex {c e κ : ℝ} (h : HasStableOneCharFun c e κ μ)
    (hc : 0 < c) : IsStableIndex 1 μ := by
  have := h.1
  have hex : ∀ n : ℕ, 1 ≤ n →
      convPow μ n = μ.map (fun x => (n : ℝ) ^ (1 : ℝ)⁻¹ * x + e * n * Real.log n) := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_convPow, charFun_map_mul_add, h.2, h.2, ← Complex.exp_nat_mul, ← Complex.exp_add,
      inv_one, rpow_one]
    congr 1
    simp only [stableExponentOne]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · rw [abs_mul, abs_of_pos hn', Real.log_mul hn'.ne' (abs_ne_zero.2 ht)]
      push_cast; ring
  refine ⟨⟨inferInstance, ne_dirac_of_norm_charFun_lt_one (t := 1) ?_,
    fun n hn => ⟨_, _, rpow_pos_of_pos (by exact_mod_cast hn) _, hex n hn⟩⟩,
    fun n hn => ⟨_, hex n hn⟩⟩
  rw [h.2, Complex.norm_exp]
  simp [stableExponentOne, hc]

theorem HasStableOneCharFun.isStable {c e κ : ℝ} (h : HasStableOneCharFun c e κ μ)
    (hc : 0 < c) : IsStable μ :=
  (h.isStableIndex hc).1

end Index

section Scaling

variable {α c e κ r : ℝ} {ν : Measure ℝ}

theorem stableExponent_mul' (hr : 0 < r) (t : ℝ) :
    stableExponent α c e (r * t) = stableExponent α (r ^ α * c) (r ^ α * e) t := by
  rw [stableExponent_mul hr]
  simp only [stableExponent]
  push_cast
  ring

/-- If `X` has characteristic function `exp ψ_{α,c,e}` then `r X` has `exp ψ_{α, r^α c, r^α e}`. -/
theorem HasStableCharFun.map_mul (h : HasStableCharFun α c e ν) (hr : 0 < r) :
    HasStableCharFun α (r ^ α * c) (r ^ α * e) (ν.map (r * ·)) := by
  have := h.1
  exact ⟨inferInstance, fun t => by rw [charFun_map_mul, h.2, stableExponent_mul' hr]⟩

theorem stableExponentOne_mul (hr : 0 < r) (t : ℝ) :
    stableExponentOne c e κ (r * t) + ((e * r * Real.log r * t : ℝ) : ℂ) * Complex.I =
      stableExponentOne (r * c) (r * e) κ t := by
  simp only [stableExponentOne]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [abs_mul, abs_of_pos hr, Real.log_mul hr.ne' (abs_ne_zero.2 ht)]
    push_cast; ring

/-- If `X` is `1`-stable with parameters `(c, e, κ)`, then `r X + e r log r` is `1`-stable with
parameters `(r c, r e, κ)`. -/
theorem HasStableOneCharFun.map_mul_add (h : HasStableOneCharFun c e κ ν) (hr : 0 < r) :
    HasStableOneCharFun (r * c) (r * e) κ (ν.map (fun x => r * x + e * r * Real.log r)) := by
  have := h.1
  refine ⟨inferInstance, fun t => ?_⟩
  rw [charFun_map_mul_add, h.2, ← Complex.exp_add, ← stableExponentOne_mul hr]
  congr 1
  push_cast
  ring

end Scaling

section Types

/-- **Convergence of types, same scale.** If `ρₙ → ν` and the shifted laws `ρₙ ∗ δ_{cₙ}`
converge to `ν'`, then `ν'` is a shift of `ν`. The shifts are bounded by tightness, and along a
convergent subsequence `cₙ → c₀` the characteristic functions give `ν' = ν ∗ δ_{c₀}`. -/
theorem exists_map_add_eq_of_tendsto {ρ : ℕ → ProbabilityMeasure ℝ} {c : ℕ → ℝ}
    {ν ν' : ProbabilityMeasure ℝ} (h : Tendsto ρ atTop (𝓝 ν))
    (h' : Tendsto (β := ProbabilityMeasure ℝ)
      (fun n => ⟨(ρ n : Measure ℝ).map (· + c n), inferInstance⟩) atTop (𝓝 ν')) :
    ∃ c₀ : ℝ, (ν : Measure ℝ).map (· + c₀) = ν' := by
  have htight : ∀ {σ : ℕ → ProbabilityMeasure ℝ} {τ : ProbabilityMeasure ℝ},
      Tendsto σ atTop (𝓝 τ) → ∃ r : ℝ, ∀ n, (σ n : Measure ℝ) {x | r < ‖x‖} < 1 / 2 := by
    intro σ τ hσ
    have hT := isTightMeasureSet_of_tendsto_charFun (μ := fun n => (σ n : Measure ℝ))
      (f := charFun (τ : Measure ℝ)) continuous_charFun.continuousAt
      (fun t => ((continuous_charFun_probabilityMeasure t).tendsto τ).comp hσ)
    have h0 := tendsto_measure_norm_gt_of_isTightMeasureSet hT
    obtain ⟨r, hr⟩ := (h0.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 / 2 by simp))).exists
    exact ⟨r, fun n => lt_of_le_of_lt
      (le_iSup₂ (f := fun (m : Measure ℝ) (_ : m ∈ range fun n => (σ n : Measure ℝ)) =>
        m {x | r < ‖x‖}) _ (mem_range_self n)) hr⟩
  obtain ⟨r, hr⟩ := htight h
  obtain ⟨r', hr'⟩ := htight h'
  have hbd : ∀ n, |c n| ≤ r + r' := by
    intro n
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hcov : (univ : Set ℝ) ⊆ {x | r < ‖x‖} ∪ (· + c n) ⁻¹' {x | r' < ‖x‖} := by
      intro x _
      by_contra hx
      simp only [mem_union, mem_ofPred_eq, mem_preimage, not_or, not_lt, Real.norm_eq_abs] at hx
      have : |c n| ≤ |x + c n| + |x| := by
        calc |c n| = |(x + c n) + (-x)| := by ring_nf
          _ ≤ |x + c n| + |-x| := abs_add_le _ _
          _ = _ := by rw [abs_neg]
      linarith
    have h1 := hr' n
    simp only [ProbabilityMeasure.coe_mk] at h1
    rw [Measure.map_apply (measurable_add_const _)
      (measurableSet_lt measurable_const measurable_norm)] at h1
    have h2 := (measure_mono (μ := (ρ n : Measure ℝ)) hcov).trans (measure_union_le _ _)
    rw [measure_univ] at h2
    have h3 := ENNReal.add_lt_add (hr n) h1
    rw [ENNReal.add_halves] at h3
    exact lt_irrefl _ (h2.trans_lt h3)
  obtain ⟨c₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := r + r')) (x := c)
    (fun n => by simpa [Metric.mem_closedBall, Real.dist_eq] using hbd n)
  refine ⟨c₀, Measure.ext_of_charFun (funext fun t => ?_)⟩
  have hA := ((continuous_charFun_probabilityMeasure t).tendsto ν').comp
    (h'.comp hφ.tendsto_atTop)
  have hB := (((continuous_charFun_probabilityMeasure t).tendsto ν).comp
    (h.comp hφ.tendsto_atTop)).mul
    (((by fun_prop : Continuous fun y : ℝ => Complex.exp (((t * y : ℝ) : ℂ) * Complex.I)).tendsto
      c₀).comp hlim)
  rw [charFun_map_add_const]
  simp only [RCLike.inner_apply, conj_trivial]
  refine tendsto_nhds_unique hB (hA.congr fun k => ?_)
  simp only [Function.comp, ProbabilityMeasure.coe_mk, charFun_map_add_const, RCLike.inner_apply,
    conj_trivial]

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- Two limits of `(Sₙ - bₙ) / aₙ` and `(Sₙ - b'ₙ) / (s aₙ)` are of the same type:
`ν ∗ δ_{c₀} = law (s Y)`, `Y ∼ ν'`. -/
theorem exists_map_add_eq_map_mul {a b b' : ℕ → ℝ} {s : ℝ} (hs : 0 < s) (ha : ∀ n, 0 < a n)
    {ν ν' : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    (hconv' : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n * s)⁻¹ * (x - b' n)), inferInstance⟩) atTop (𝓝 ν')) :
    ∃ c₀ : ℝ, (ν : Measure ℝ).map (· + c₀) = (ν' : Measure ℝ).map (s * ·) := by
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv'
    (continuous_const_mul s)
  have hcong : ∀ n, ProbabilityMeasure.map
      (⟨(convPow μ n).map (fun x => (a n * s)⁻¹ * (x - b' n)), inferInstance⟩ :
        ProbabilityMeasure ℝ) (fun x => s * x) =
      ⟨((⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩ :
        ProbabilityMeasure ℝ) : Measure ℝ).map (· + (b n - b' n) / a n), inferInstance⟩ := by
    intro n
    apply Subtype.ext
    have := (ha n).ne'
    have := hs.ne'
    change Measure.map (fun x => s * x)
      (Measure.map (fun x => (a n * s)⁻¹ * (x - b' n)) (convPow μ n)) =
      Measure.map (· + (b n - b' n) / a n) (Measure.map (fun x => (a n)⁻¹ * (x - b n)) (convPow μ n))
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp]
    field_simp
    ring
  obtain ⟨c₀, hc₀⟩ := exists_map_add_eq_of_tendsto hconv (hm.congr hcong)
  exact ⟨c₀, by rw [hc₀, ProbabilityMeasure.toMeasure_map]⟩

end Types

section Identification

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ}

/-- **Identification of the limit**, from the symmetrized scaling limit. If `(Sₙ - bₙ) / aₙ → ν`
and `n E[min (1, (X - X')² / (aₙ x)²)] → K x ^ (-α)`, `0 < α < 2`, then (besides regular
variation and tail balance with `n P(|X| > aₙ) → B`) a shift of `ν` is the explicit stable law
of the sufficiency theorems with scale `B`: apply the generalized CLT along `aₙ B^{1/α}` (for
which `n P(|X| > aₙ B^{1/α}) → 1`) and use convergence of types with the same scale. -/
theorem identify_of_tendsto_mul_sqRatio (ha : ∀ n, 0 < a n) {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    {α K : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hK : 0 < K)
    (hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n * x)) atTop
      (𝓝 (K * x ^ (-α)))) :
    IsRegularlyVarying (absTail μ) (-α) ∧ ∃ B > 0,
      Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 B) ∧ ∃ p, 0 ≤ p ∧ p ≤ 1 ∧
      Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p) ∧ ∃ m : ℝ,
      (α ≠ 1 → HasStableCharFun α (B * stableConst α) (B * ((2 * p - 1) * stableSkewConst α))
        ((ν : Measure ℝ).map (· + m))) ∧
      (α = 1 → HasStableOneCharFun (B * stableConst 1) (B * (2 * p - 1)) stableLogConst
        ((ν : Measure ℝ).map (· + m))) := by
  obtain ⟨hG, ⟨B, hB0, hB⟩, p, hp0, hp1, hp⟩ :=
    tailBalance_of_tendsto_mul_sqRatio_symmLaw ha hconv hα0 hα2 hK hL
  have hatop : Tendsto a atTop atTop :=
    tendsto_atTop_of_tendsto_mul_comp (T := absTail μ) (L := fun _ => B)
      (absTail_antitone.antitoneOn _) (fun x _ => absTail_pos hG x) ha hB
  obtain ⟨s, hs, hsα⟩ : ∃ s : ℝ, 0 < s ∧ s ^ α = B :=
    ⟨B ^ α⁻¹, rpow_pos_of_pos hB0 _, rpow_inv_rpow hB0.le hα0.ne'⟩
  have ha' : ∀ n, 0 < a n * s := fun n => mul_pos (ha n) hs
  have hna' : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n * s)) atTop (𝓝 1) := by
    have h := tendsto_mul_comp_mul_of_tendsto hG hatop hB hs
    rwa [rpow_neg hs.le, hsα, mul_inv_cancel₀ hB0.ne'] at h
  refine ⟨hG, B, hB0, hB, p, hp0, hp1, hp, ?_⟩
  rcases lt_trichotomy α 1 with h1 | rfl | h1
  · obtain ⟨ν', hν', hlim⟩ := tendsto_map_convPow_of_isRegularlyVarying_of_lt_one hα0 h1 hG hp
      (a := fun n => a n * s) ha' hna'
    obtain ⟨c₀, hc₀⟩ := exists_map_add_eq_map_mul (b' := fun _ => 0) hs ha hconv
      (hlim.congr fun n => Subtype.ext (by simp only [sub_zero]))
    refine ⟨c₀, fun _ => ?_, fun h => absurd h h1.ne⟩
    rw [hc₀, ← hsα]
    exact hν'.map_mul hs
  · obtain ⟨ν', hν', hlim⟩ := tendsto_map_convPow_sub_of_isRegularlyVarying_one hG hp
      (a := fun n => a n * s) ha' hna'
    obtain ⟨c₀, hc₀⟩ := exists_map_add_eq_map_mul
      (b' := fun n => (n : ℝ) * ∫ y in Icc (-(a n * s)) (a n * s), y ∂μ) hs ha hconv hlim
    have hsB : s = B := by rwa [rpow_one] at hsα
    refine ⟨c₀ + (2 * p - 1) * s * Real.log s, fun h => absurd rfl h, fun _ => ?_⟩
    have e : (ν : Measure ℝ).map (· + (c₀ + (2 * p - 1) * s * Real.log s)) =
        (ν' : Measure ℝ).map (fun x => s * x + (2 * p - 1) * s * Real.log s) := by
      rw [show (fun x : ℝ => x + (c₀ + (2 * p - 1) * s * Real.log s)) =
          (· + (2 * p - 1) * s * Real.log s) ∘ (· + c₀) by
            funext x; simp only [Function.comp]; ring,
        ← Measure.map_map (measurable_add_const _) (measurable_add_const _), hc₀,
        Measure.map_map (measurable_add_const _) (measurable_const_mul _)]
      rfl
    rw [e, ← hsB]
    exact hν'.map_mul_add hs
  · obtain ⟨ν', hν', hlim⟩ := tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt h1 hα2 hG
      hp (a := fun n => a n * s) ha' hna'
    obtain ⟨c₀, hc₀⟩ := exists_map_add_eq_map_mul
      (b' := fun n => (n : ℝ) * ∫ y, y ∂μ) hs ha hconv hlim
    refine ⟨c₀, fun _ => ?_, fun h => absurd h h1.ne'⟩
    rw [hc₀, ← hsα]
    exact hν'.map_mul hs

end Identification

section ConverseLimit

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ}

/-- **The limit in the converse of the generalized CLT is stable, with the explicit
characteristic function** ([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2]). Let
`aₙ > 0`, `bₙ ∈ ℝ`, and suppose the laws of `(Sₙ - bₙ) / aₙ` converge weakly to a law `ν` which
is not a Dirac mass. Then there is `0 < α ≤ 2` such that, if `α < 2`: the tail
`P(|X| > ·)` is regularly varying with index `-α`; the Lévy measures converge,
`n P(X > aₙ u) → c₊ u^(-α)`, `n P(X < -aₙ u) → c₋ u^(-α)` with `c₊, c₋ ≥ 0`, `c₊ + c₋ > 0`;
`ν` is stable with index `α`; and a shift of `ν` has characteristic function
`exp (-C_α (c₊ + c₋) |t|^α + i E_α (c₊ - c₋) sign(t) |t|^α)` for `α ≠ 1`
(so `β = (c₊ - c₋) / (c₊ + c₋)`, scale `σ^α = C_α (c₊ + c₋)`), and
`exp (-C₁ (c₊ + c₋) |t| + i (c₊ - c₋) (κ t - t log |t|))` for `α = 1`. -/
theorem exists_stable_limit_of_tendsto (ha : ∀ n, 0 < a n) {ν : ProbabilityMeasure ℝ}
    (hnd : ∀ x, (ν : Measure ℝ) ≠ Measure.dirac x)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ α, 0 < α ∧ α ≤ 2 ∧ (α < 2 → IsRegularlyVarying (absTail μ) (-α) ∧
      ∃ cp cm : ℝ, 0 ≤ cp ∧ 0 ≤ cm ∧ 0 < cp + cm ∧
      (∀ u : ℝ, 0 < u →
        Tendsto (fun n : ℕ => (n : ℝ) * μ.real (Ioi (a n * u))) atTop (𝓝 (cp * u ^ (-α))) ∧
        Tendsto (fun n : ℕ => (n : ℝ) * μ.real (Iio (-(a n * u)))) atTop
          (𝓝 (cm * u ^ (-α)))) ∧
      IsStableIndex α ν ∧ ∃ m : ℝ,
      (α ≠ 1 → HasStableCharFun α (stableConst α * (cp + cm)) (stableSkewConst α * (cp - cm))
        ((ν : Measure ℝ).map (· + m))) ∧
      (α = 1 → HasStableOneCharFun (stableConst 1 * (cp + cm)) (cp - cm) stableLogConst
        ((ν : Measure ℝ).map (· + m)))) := by
  obtain ⟨α, hα0, hα2, K, hK, hL⟩ := exists_tendsto_mul_sqRatio_symmLaw ha hnd hconv
  refine ⟨α, hα0, hα2, fun hlt => ?_⟩
  obtain ⟨hG, B, hB0, hB, p, hp0, hp1, hp, m, hm1, hm2⟩ :=
    identify_of_tendsto_mul_sqRatio ha hconv hα0 hlt hK hL
  have hGpos := absTail_pos hG
  have hatop : Tendsto a atTop atTop :=
    tendsto_atTop_of_tendsto_mul_comp (T := absTail μ) (L := fun _ => B)
      (absTail_antitone.antitoneOn _) (fun x _ => hGpos x) ha hB
  have hq : Tendsto (fun x => μ.real (Iio (-x)) / absTail μ x) atTop (𝓝 (1 - p)) := by
    refine (tendsto_const_nhds.sub hp).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    have := (hGpos x).ne'
    rw [absTail_eq_add hx] at this ⊢
    field_simp
    ring
  have hcp : B * p + B * (1 - p) = B := by ring
  have hstab : IsStableIndex α ν := by
    rcases eq_or_ne α 1 with h1 | h1
    · subst h1
      exact ((hm2 rfl).isStableIndex
        (mul_pos hB0 (stableConst_pos one_pos (by norm_num)))).of_map_add_const
    · exact ((hm1 h1).isStableIndex hα0 (mul_pos hB0 (stableConst_pos hα0 hlt))).of_map_add_const
  refine ⟨hG, B * p, B * (1 - p), mul_nonneg hB0.le hp0, mul_nonneg hB0.le (by linarith),
    by rw [hcp]; exact hB0, fun u hu => ⟨?_, ?_⟩, hstab, m, fun h1 => ?_, fun h1 => ?_⟩
  · have h1 := (tendsto_mul_comp_mul_of_tendsto hG hatop hB hu).mul
      (hp.comp (hatop.atTop_mul_const hu))
    rw [show B * u ^ (-α) * p = B * p * u ^ (-α) by ring] at h1
    refine h1.congr fun n => ?_
    have := (hGpos (a n * u)).ne'
    simp only [Function.comp]
    field_simp
  · have h1 := (tendsto_mul_comp_mul_of_tendsto hG hatop hB hu).mul
      (hq.comp (hatop.atTop_mul_const hu))
    rw [show B * u ^ (-α) * (1 - p) = B * (1 - p) * u ^ (-α) by ring] at h1
    refine h1.congr fun n => ?_
    have := (hGpos (a n * u)).ne'
    simp only [Function.comp]
    field_simp
  · rw [hcp, show stableSkewConst α * (B * p - B * (1 - p)) =
      B * ((2 * p - 1) * stableSkewConst α) by ring, mul_comm]
    exact hm1 h1
  · rw [hcp, show B * p - B * (1 - p) = B * (2 * p - 1) by ring, mul_comm]
    exact hm2 h1

end ConverseLimit

section IndexBound

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ}

theorem one_sub_cosTransform_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {s : ℝ} (hs : s ≠ 0) :
    1 - cosTransform ρ s ≤ 2 * sqRatio ρ s⁻¹ := by
  rw [sqRatio_eq_integral_min' (inv_ne_zero hs), cosTransform, ← integral_const_mul]
  have hint : Integrable (fun x : ℝ => min 1 ((s⁻¹⁻¹ * x) ^ 2)) ρ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (sq_nonneg _))]
      exact min_le_left _ _)
  calc 1 - ∫ x, cos (s * x) ∂ρ = ∫ x, (1 - cos (s * x)) ∂ρ := by
        rw [integral_sub (integrable_const _) (integrable_cos s)]; simp
    _ ≤ ∫ x, 2 * min 1 ((s⁻¹⁻¹ * x) ^ 2) ∂ρ :=
        integral_mono ((integrable_const _).sub (integrable_cos s)) (hint.const_mul 2)
          fun x => by rw [inv_inv]; exact one_sub_cos_le_two_mul_min _

theorem exp_neg_two_mul_le {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    Real.exp (-(2 * d)) ≤ 1 - d := by
  have h1 : 1 + 2 * d ≤ Real.exp (2 * d) := by linarith [Real.add_one_le_exp (2 * d)]
  have hpos := Real.exp_pos (-(2 * d))
  have hE : Real.exp (-(2 * d)) * Real.exp (2 * d) = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- **A lower bound for the limit**, from the symmetrized scaling limit: if `(Sₙ - bₙ) / aₙ → ν`
and `n E[min (1, (X - X')² / (aₙ x)²)] → K x ^ (-α)`, then `|φ_ν(t)|² ≥ exp (-6 K t^α)`. -/
theorem exp_le_norm_charFun_sq (ha : ∀ n, 0 < a n) {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    {α K : ℝ} (hK : 0 < K)
    (hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n * x)) atTop
      (𝓝 (K * x ^ (-α)))) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(6 * K * t ^ α)) ≤ ‖charFun (ν : Measure ℝ) t‖ ^ 2 := by
  set f : ℝ → ℝ := fun s => ‖charFun μ s‖ ^ 2 with hfdef
  have hf : ∀ s, f s = cosTransform (symmLaw μ) s := by
    intro s
    rw [cosTransform_eq_re, charFun_symmLaw, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hlim : Tendsto (fun n : ℕ => f ((a n)⁻¹ * t) ^ n) atTop
      (𝓝 (‖charFun (ν : Measure ℝ) t‖ ^ 2)) := by
    have h := ((continuous_norm.pow 2).tendsto _).comp
      (((continuous_charFun_probabilityMeasure t).tendsto ν).comp hconv)
    refine h.congr fun n => ?_
    simp only [Function.comp, ProbabilityMeasure.coe_mk, hfdef, Pi.pow_apply]
    have e : (fun x => (a n)⁻¹ * (x - b n)) = fun x => (a n)⁻¹ * x + (-((a n)⁻¹ * b n)) := by
      funext x; ring
    rw [e, charFun_map_mul_add, charFun_convPow, norm_mul, norm_pow,
      show (((-((a n)⁻¹ * b n) : ℝ) : ℂ) * (t : ℂ) * Complex.I) =
        ((-((a n)⁻¹ * b n) * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    ring
  set D := 3 * K * t ^ α with hD
  have hKt : 0 < K * t ^ α := mul_pos hK (rpow_pos_of_pos ht _)
  have hL' := hL t⁻¹ (inv_pos.2 ht)
  rw [inv_rpow ht.le, rpow_neg ht.le, inv_inv] at hL'
  refine ge_of_tendsto hlim ?_
  filter_upwards [(tendsto_order.1 hL').2 (3 / 2 * (K * t ^ α)) (by linarith),
    eventually_ge_atTop ⌈2 * D⌉₊, eventually_gt_atTop 0] with n hn hn2 hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  set d := 1 - f ((a n)⁻¹ * t) with hd
  have hs : (a n)⁻¹ * t ≠ 0 := mul_ne_zero (inv_ne_zero (ha n).ne') ht.ne'
  have hd0 : 0 ≤ d := by
    have : f ((a n)⁻¹ * t) ≤ 1 := by
      simp only [hfdef]
      exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
    linarith
  have hdle : (n : ℝ) * d ≤ D := by
    have h1 := one_sub_cosTransform_le (symmLaw μ) hs
    rw [mul_inv, inv_inv, ← hf] at h1
    calc (n : ℝ) * d ≤ (n : ℝ) * (2 * sqRatio (symmLaw μ) (a n * t⁻¹)) :=
          mul_le_mul_of_nonneg_left h1 hn0'.le
      _ = 2 * ((n : ℝ) * sqRatio (symmLaw μ) (a n * t⁻¹)) := by ring
      _ ≤ 2 * (3 / 2 * (K * t ^ α)) := by linarith
      _ = D := by rw [hD]; ring
  have hd2 : d ≤ 1 / 2 := by
    have h2 : 2 * D ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
    have hD0 : 0 < D := by rw [hD]; linarith
    nlinarith
  have h1 : f ((a n)⁻¹ * t) = 1 - d := by rw [hd]; ring
  rw [h1]
  calc Real.exp (-(6 * K * t ^ α)) ≤ Real.exp (n * -(2 * d)) := by
        rw [Real.exp_le_exp]; nlinarith
    _ = Real.exp (-(2 * d)) ^ n := Real.exp_nat_mul _ _
    _ ≤ (1 - d) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_two_mul_le hd0 hd2) n

theorem exists_norm_charFun_lt_one {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h : ∀ x, ν ≠ Measure.dirac x) : ∃ t, 0 < t ∧ ‖charFun ν t‖ < 1 := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  have hnorm : ∀ t, ‖charFun ν t‖ = 1 := by
    intro t
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have := hc (-t) (neg_pos.2 ht)
      rw [charFun_neg, Complex.norm_conj] at this
      exact le_antisymm (norm_charFun_le_one _) this
    · simp
    · exact le_antisymm (norm_charFun_le_one _) (hc t ht)
  apply symmLaw_ne_dirac h
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_symmLaw, charFun_dirac, Complex.normSq_eq_norm_sq, hnorm t]
  simp

theorem IsStableIndex.norm_charFun_pow {α : ℝ} {ν : Measure ℝ} (h : IsStableIndex α ν) {n : ℕ}
    (hn : 1 ≤ n) (t : ℝ) : ‖charFun ν t‖ ^ n = ‖charFun ν ((n : ℝ) ^ α⁻¹ * t)‖ := by
  have := h.1.isProbabilityMeasure
  obtain ⟨b, hb⟩ := h.2 n hn
  have h1 := congrArg (fun ρ => charFun ρ t) hb
  simp only [charFun_convPow, charFun_map_mul_add] at h1
  rw [← norm_pow, h1, norm_mul, show (b : ℂ) * (t : ℂ) * Complex.I = ((b * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- If `ν` is stable with index `α` and `|φ_ν(t)|² ≥ exp (-C t^β)` for `t > 0`, then `β ≤ α`:
`|φ_ν(t₀)|² = |φ_ν(k^{-1/α} t₀)|^{2k} ≥ exp (-C t₀^β k^{1 - β/α})`, which tends to `1` if
`β > α`. -/
theorem IsStableIndex.le_of_exp_le {α β C : ℝ} {ν : Measure ℝ} (h : IsStableIndex α ν)
    (hα0 : 0 < α) (hb : ∀ t, 0 < t → Real.exp (-(C * t ^ β)) ≤ ‖charFun ν t‖ ^ 2) : β ≤ α := by
  have := h.1.isProbabilityMeasure
  obtain ⟨t₀, ht₀, hlt⟩ := exists_norm_charFun_lt_one h.1.ne_dirac
  by_contra hβ
  replace hβ := not_le.1 hβ
  have hq1 : ‖charFun ν t₀‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hlt two_ne_zero
  have hk : ∀ k : ℕ, 1 ≤ k →
      Real.exp (-(C * t₀ ^ β * (k : ℝ) ^ (1 - β / α))) ≤ ‖charFun ν t₀‖ ^ 2 := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    set tk := (k : ℝ) ^ (-α⁻¹) * t₀ with htkdef
    have htk : 0 < tk := mul_pos (rpow_pos_of_pos hk0 _) ht₀
    have hrel : (k : ℝ) ^ α⁻¹ * tk = t₀ := by
      rw [htkdef, ← mul_assoc, ← rpow_add hk0]; simp
    have h1 := h.norm_charFun_pow hk tk
    rw [hrel] at h1
    have h2 : Real.exp (-(C * tk ^ β)) ^ k ≤ (‖charFun ν tk‖ ^ 2) ^ k :=
      pow_le_pow_left₀ (Real.exp_pos _).le (hb tk htk) k
    rw [← Real.exp_nat_mul, ← pow_mul, mul_comm 2 k, pow_mul, h1] at h2
    have h3 : (k : ℝ) * (C * tk ^ β) = C * t₀ ^ β * (k : ℝ) ^ (1 - β / α) := by
      rw [htkdef, mul_rpow (rpow_nonneg hk0.le _) ht₀.le, ← rpow_mul hk0.le, rpow_sub hk0,
        rpow_one, show -α⁻¹ * β = -(β / α) by ring, rpow_neg hk0.le]
      field_simp
    calc Real.exp (-(C * t₀ ^ β * (k : ℝ) ^ (1 - β / α))) = Real.exp (k * -(C * tk ^ β)) := by
          rw [mul_neg, h3]
      _ ≤ _ := h2
  have hlim : Tendsto (fun k : ℕ => Real.exp (-(C * t₀ ^ β * (k : ℝ) ^ (1 - β / α)))) atTop
      (𝓝 1) := by
    have hneg : 0 < -(1 - β / α) := by
      have : 1 < β / α := (one_lt_div hα0).2 hβ
      linarith
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) ^ (1 - β / α)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop
      simpa only [neg_neg, Function.comp_def] using this
    have := (Real.continuous_exp.tendsto _).comp ((h1.const_mul (C * t₀ ^ β)).neg)
    simpa only [mul_zero, neg_zero, Real.exp_zero, Function.comp_def] using this
  have : 1 ≤ ‖charFun ν t₀‖ ^ 2 := le_of_tendsto hlim (eventually_atTop.2 ⟨1, hk⟩)
  linarith

/-- The index of a stable law is unique: if `ν` is stable with index `α` and
`|φ_ν(t)| = exp (-c |t|^β)` with `c > 0`, then `β = α`. -/
theorem IsStableIndex.eq_of_norm_charFun {α β c : ℝ} {ν : Measure ℝ} (h : IsStableIndex α ν)
    (hc : 0 < c) (hφ : ∀ t, ‖charFun ν t‖ = Real.exp (-(c * |t| ^ β))) : β = α := by
  have h2 := h.norm_charFun_pow (n := 2) (by norm_num) 1
  rw [hφ, hφ, ← Real.exp_nat_mul, Real.exp_eq_exp, mul_one, abs_one, one_rpow, Nat.cast_ofNat,
    abs_of_pos (rpow_pos_of_pos two_pos _), ← rpow_mul zero_le_two] at h2
  have hx : (2 : ℝ) ^ (α⁻¹ * β) = 2 := by
    refine mul_left_cancel₀ hc.ne' ?_
    linarith
  have hl := congrArg Real.log hx
  rw [Real.log_rpow two_pos] at hl
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have h1 : α⁻¹ * β = 1 := mul_right_cancel₀ hl2 (hl.trans (one_mul _).symm)
  have hα : α ≠ 0 := by
    rintro rfl
    simp at h1
  field_simp at h1
  linarith

theorem norm_charFun_map_add_const {ν : Measure ℝ} (m t : ℝ) :
    ‖charFun (ν.map (· + m)) t‖ = ‖charFun ν t‖ := by
  rw [charFun_map_add_const, norm_mul]
  simp only [RCLike.inner_apply, conj_trivial, Complex.norm_exp_ofReal_mul_I, mul_one]

end IndexBound

section Iff

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}

/-- The centering of the generalized CLT: `bₙ = 0` for `α < 1`, the truncated mean
`n E[X 1{|X| ≤ aₙ}]` for `α = 1`, and `n E X` for `α > 1`. -/
noncomputable def stableCentering (μ : Measure ℝ) (α : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  if α < 1 then 0 else if α = 1 then n * ∫ y in Icc (-a n) (a n), y ∂μ else n * ∫ y, y ∂μ

/-- **Generalized CLT with the canonical normalization** (asymmetric case). If
`P(|X| > ·) ∈ RV(-α)`, `0 < α < 2`, and `P(X > x) / P(|X| > x) → p`, then with
`aₙ = normSeq μ n = inf {x : P(|X| > x) ≤ 1 / n}` and `bₙ = stableCentering μ α aₙ n`, the laws
of `(Sₙ - bₙ) / aₙ` converge weakly to a law `ν` which is stable with index `α`, with
characteristic function `exp (-C_α |t|^α + i (2p - 1) E_α sign(t) |t|^α)` (`α ≠ 1`) or
`exp (-C₁ |t| + i (2p - 1) (κ t - t log |t|))` (`α = 1`). -/
theorem tendsto_map_convPow_sub_normSeq (hα0 : 0 < α) (hα2 : α < 2)
    (hRV : IsRegularlyVarying (absTail μ) (-α)) {p : ℝ}
    (hp : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p)) :
    ∃ ν : ProbabilityMeasure ℝ, IsStableIndex α ν ∧
      (α ≠ 1 → HasStableCharFun α (stableConst α) ((2 * p - 1) * stableSkewConst α) ν) ∧
      (α = 1 → HasStableOneCharFun (stableConst 1) (2 * p - 1) stableLogConst ν) ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map (fun x => (normSeq μ n)⁻¹ * (x - stableCentering μ α (normSeq μ) n)),
          inferInstance⟩) atTop (𝓝 ν) := by
  obtain ⟨a', ha', hea⟩ := exists_pos_eventuallyEq (tendsto_normSeq hRV)
  have hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a' n)) atTop (𝓝 1) :=
    (tendsto_mul_absTail_normSeq hRV).congr' (hea.mono fun n hn => by simp [hn])
  have hC := stableConst_pos hα0 hα2
  rcases lt_trichotomy α 1 with h1 | rfl | h1
  · obtain ⟨ν, hν, hlim⟩ :=
      tendsto_map_convPow_of_isRegularlyVarying_of_lt_one hα0 h1 hRV hp ha' hna
    refine ⟨ν, hν.isStableIndex hα0 hC, fun _ => hν, fun h => absurd h h1.ne,
      hlim.congr' (hea.mono fun n hn => Subtype.ext ?_)⟩
    simp only [stableCentering, h1, ↓reduceIte, sub_zero, hn]
  · obtain ⟨ν, hν, hlim⟩ := tendsto_map_convPow_sub_of_isRegularlyVarying_one hRV hp ha' hna
    refine ⟨ν, hν.isStableIndex hC, fun h => absurd rfl h, fun _ => hν,
      hlim.congr' (hea.mono fun n hn => Subtype.ext ?_)⟩
    simp only [stableCentering, lt_self_iff_false, ↓reduceIte, hn]
  · obtain ⟨ν, hν, hlim⟩ :=
      tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt h1 hα2 hRV hp ha' hna
    refine ⟨ν, hν.isStableIndex hα0 hC, fun _ => hν, fun h => absurd h h1.ne',
      hlim.congr' (hea.mono fun n hn => Subtype.ext ?_)⟩
    simp only [stableCentering, not_lt.2 h1.le, h1.ne', ↓reduceIte, hn]

/-- **Feller's criterion for the domain of attraction of a stable law**
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2], [EKM, Theorem 2.2.8]). Let
`0 < α < 2`. There are `aₙ > 0`, `bₙ` and a law `ν`, stable with index `α`, such that
`(X₁ + ⋯ + Xₙ - bₙ) / aₙ → ν` weakly, if and only if the two-sided tail `P(|X| > ·)` is
regularly varying with index `-α` and the tails are balanced, `P(X > x) / P(|X| > x) → p` for
some `p ∈ [0, 1]`. In that case `aₙ = normSeq μ n` and `bₙ = stableCentering μ α aₙ n` work
(`tendsto_map_convPow_sub_normSeq`).

Necessity: the converse GCLT gives an index `α'` and the symmetrized scaling limit; the lower
bound `|φ_ν(t)|² ≥ exp (-6 K t^{α'})` forces `α' ≤ α < 2`
(`IsStableIndex.le_of_exp_le`), the limit is then identified as an explicit `α'`-stable law up
to a shift (`identify_of_tendsto_mul_sqRatio`), and uniqueness of the index gives `α' = α`. -/
theorem domainOfAttraction_isStableIndex_iff (hα0 : 0 < α) (hα2 : α < 2) :
    (∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∃ b : ℕ → ℝ, ∃ ν : ProbabilityMeasure ℝ,
      IsStableIndex α ν ∧ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) ↔
      IsRegularlyVarying (absTail μ) (-α) ∧ ∃ p, 0 ≤ p ∧ p ≤ 1 ∧
        Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p) := by
  constructor
  · rintro ⟨a, ha, b, ν, hν, hconv⟩
    obtain ⟨α', hα'0, -, K, hK, hL⟩ := exists_tendsto_mul_sqRatio_symmLaw ha hν.1.ne_dirac hconv
    have hle : α' ≤ α := hν.le_of_exp_le hα0 (C := 6 * K) fun t ht => by
      simpa [mul_assoc] using exp_le_norm_charFun_sq ha hconv hK hL ht
    obtain ⟨hG, B, hB0, -, p, hp0, hp1, hp, m, hm1, hm2⟩ :=
      identify_of_tendsto_mul_sqRatio ha hconv hα'0 (hle.trans_lt hα2) hK hL
    have heq : α' = α := by
      rcases eq_or_ne α' 1 with h1 | h1
      · subst h1
        have hc := mul_pos hB0 (stableConst_pos one_pos (by norm_num : (1 : ℝ) < 2))
        refine hν.eq_of_norm_charFun hc fun t => ?_
        rw [← norm_charFun_map_add_const m, (hm2 rfl).2, Complex.norm_exp, rpow_one]
        simp [stableExponentOne]
      · have hc := mul_pos hB0 (stableConst_pos hα'0 (hle.trans_lt hα2))
        refine hν.eq_of_norm_charFun hc fun t => ?_
        rw [← norm_charFun_map_add_const m, (hm1 h1).2, Complex.norm_exp]
        simp [stableExponent]
    subst heq
    exact ⟨hG, p, hp0, hp1, hp⟩
  · rintro ⟨hRV, p, -, -, hp⟩
    obtain ⟨ν, hν, -, -, hlim⟩ := tendsto_map_convPow_sub_normSeq hα0 hα2 hRV hp
    obtain ⟨a', ha', hea⟩ := exists_pos_eventuallyEq (tendsto_normSeq hRV)
    refine ⟨a', ha', stableCentering μ α (normSeq μ), ν, hν,
      hlim.congr' (hea.mono fun n hn => Subtype.ext ?_)⟩
    simp only [hn]

end Iff

end ExtremeValueTheory
