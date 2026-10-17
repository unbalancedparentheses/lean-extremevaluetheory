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

end ExtremeValueTheory
