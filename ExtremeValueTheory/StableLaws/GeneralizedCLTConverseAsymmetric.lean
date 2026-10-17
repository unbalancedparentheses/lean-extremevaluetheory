/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverse

/-!
# The converse of the generalized central limit theorem (general case)

WIP
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

namespace GCLTConverse

open GCLT Subexp

section NormSeq

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}

/-- The canonical normalizing sequence `aₙ = inf {x : P(|X| > x) ≤ 1 / n}`. -/
noncomputable def normSeq (μ : Measure ℝ) (n : ℕ) : ℝ :=
  sInf {x : ℝ | absTail μ x ≤ (n : ℝ)⁻¹}

/-- `P(|X| > x)` is right-continuous: if `P(|X| > y) ≤ c` for all `y > x`, then
`P(|X| > x) ≤ c`. -/
theorem absTail_le_of_forall_gt {x c : ℝ} (h : ∀ y, x < y → absTail μ y ≤ c) :
    absTail μ x ≤ c := by
  have hU : {y : ℝ | x < |y|} = ⋃ k : ℕ, {y : ℝ | x + 1 / ((k : ℝ) + 1) < |y|} := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun k : ℕ => {y : ℝ | x + 1 / ((k : ℝ) + 1) < |y|} := by
    intro i j hij y (hy : x + 1 / ((i : ℝ) + 1) < |y|)
    show x + 1 / ((j : ℝ) + 1) < |y|
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
    linarith
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [← hU] at hlim
  have hlim' : Tendsto (fun k : ℕ => absTail μ (x + 1 / ((k : ℝ) + 1))) atTop
      (𝓝 (absTail μ x)) := by
    have := (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hlim
    exact this.congr fun k => by simp [absTail, measureReal_def, Function.comp]
  exact le_of_tendsto hlim' (Eventually.of_forall fun k => h _ (by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith))

/-- `P(|X| > x) → 0` as `x → ∞`. -/
theorem tendsto_absTail_zero : Tendsto (absTail μ) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun x : ℝ => {y : ℝ | x < |y|})
    (fun x => (measurableSet_abs_gt x).nullMeasurableSet)
    (fun x x' hxx' y (hy : x' < |y|) => (lt_of_le_of_lt hxx' hy : x < |y|))
    ⟨0, measure_ne_top μ _⟩
  have hempty : (⋂ x : ℝ, {y : ℝ | x < |y|}) = ∅ := by
    ext y
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact ⟨|y|, le_rfl⟩
  rw [hempty, measure_empty] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  exact this.congr fun x => by simp [absTail, measureReal_def, Function.comp]

variable (hRV : IsRegularlyVarying (absTail μ) (-α))
include hRV

theorem absTail_pos (x : ℝ) : 0 < absTail μ x :=
  IsRegularlyVarying.pos_of_antitone absTail_antitone hRV.1 x

/-- For `n` large the set `{x : P(|X| > x) ≤ 1 / n}` is the half-line above `aₙ`, contains
`aₙ`, and lies above any given `M`. -/
theorem normSeq_spec (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, M ≤ normSeq μ n ∧ absTail μ (normSeq μ n) ≤ (n : ℝ)⁻¹ ∧
      ∀ x, x < normSeq μ n → (n : ℝ)⁻¹ < absTail μ x := by
  have hpos := absTail_pos hRV
  have h0 : Tendsto (absTail μ) atTop (𝓝 0) := tendsto_absTail_zero
  filter_upwards [(tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds (hpos M)), eventually_gt_atTop 0] with n hn hn0
  simp only [Function.comp] at hn
  set S := {x : ℝ | absTail μ x ≤ (n : ℝ)⁻¹}
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  obtain ⟨x₁, hx₁⟩ : S.Nonempty := by
    obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 ((tendsto_order.1 h0).2 _ hninv)
    exact ⟨x₁, (hx₁ x₁ le_rfl).le⟩
  have hlow : ∀ x ∈ S, M < x := by
    intro x hx
    by_contra h
    exact absurd ((absTail_antitone (not_lt.1 h)).trans hx) (not_le.2 hn)
  have hbdd : BddBelow S := ⟨M, fun x hx => (hlow x hx).le⟩
  have hup : ∀ y, sInf S < y → y ∈ S := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt ⟨x₁, hx₁⟩ hy
    exact (absTail_antitone hsy.le).trans hs
  refine ⟨le_csInf ⟨x₁, hx₁⟩ fun x hx => (hlow x hx).le,
    absTail_le_of_forall_gt fun y hy => hup y hy, fun x hx => ?_⟩
  by_contra h
  exact absurd (csInf_le hbdd (not_lt.1 h)) (not_le.2 hx)

theorem tendsto_normSeq : Tendsto (normSeq μ) atTop atTop :=
  tendsto_atTop.2 fun M => (normSeq_spec hRV M).mono fun _ h => h.1

/-- **Normalizing sequences**: if `P(|X| > ·)` is regularly varying with index `-α`, `α > 0`,
then `aₙ = inf {x : P(|X| > x) ≤ 1 / n}` satisfies `n P(|X| > aₙ) → 1`. -/
theorem tendsto_mul_absTail_normSeq :
    Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (normSeq μ n)) atTop (𝓝 1) := by
  have hpos := absTail_pos hRV
  have hatop := tendsto_normSeq hRV
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower bound: `n G(aₙ) ≥ G(aₙ) / G(r aₙ) → r ^ α` for `r < 1`
    obtain ⟨r, hr0, hr1, hbr⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ b < r ^ α := by
      have hc : Tendsto (fun r : ℝ => r ^ α) (𝓝[<] 1) (𝓝 1) := by
        have := (Real.continuousAt_rpow_const 1 α (Or.inl one_ne_zero)).tendsto
        rw [Real.one_rpow] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h1 := (hc.eventually (lt_mem_nhds hb)).and (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))
      obtain ⟨r, hr, hr'⟩ := h1.exists
      exact ⟨r, hr'.1, hr'.2, hr⟩
    have hlim := (hRV.2 r hr0).comp hatop
    have hlim' : Tendsto (fun n => absTail μ (normSeq μ n) / absTail μ (r * normSeq μ n)) atTop
        (𝓝 (r ^ α)) := by
      have := hlim.inv₀ (Real.rpow_pos_of_pos hr0 _).ne'
      rw [Real.rpow_neg hr0.le, inv_inv] at this
      exact this.congr fun n => by simp [Function.comp, inv_div]
    filter_upwards [(tendsto_order.1 hlim').1 b hbr, normSeq_spec hRV 1,
      eventually_gt_atTop 0] with n hn hs hn0'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn0'
    obtain ⟨h1, -, h3⟩ := hs
    have hlt := h3 (r * normSeq μ n) (by nlinarith)
    refine hn.trans_le ?_
    rw [div_le_iff₀ (hpos _)]
    calc absTail μ (normSeq μ n) = (n : ℝ) * absTail μ (normSeq μ n) * (n : ℝ)⁻¹ := by
          field_simp
      _ ≤ (n : ℝ) * absTail μ (normSeq μ n) * absTail μ (r * normSeq μ n) :=
          mul_le_mul_of_nonneg_left hlt.le (mul_nonneg hn0.le (hpos _).le)
  · filter_upwards [normSeq_spec hRV 0, eventually_gt_atTop 0] with n hn hn0
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    calc (n : ℝ) * absTail μ (normSeq μ n) ≤ (n : ℝ) * (n : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hn.2.1 this.le
      _ = 1 := by field_simp
      _ < b := hb

omit hRV in
/-- A positive version of a sequence, equal to it eventually when it tends to `∞`. -/
theorem exists_pos_eventuallyEq {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    ∃ a' : ℕ → ℝ, (∀ n, 0 < a' n) ∧ a' =ᶠ[atTop] a := by
  refine ⟨fun n => if 0 < a n then a n else 1, fun n => ?_, ?_⟩
  · dsimp only; split_ifs with h
    · exact h
    · exact one_pos
  · filter_upwards [ha.eventually_gt_atTop 0] with n hn
    simp [hn]

/-- **Generalized CLT with the canonical normalization** (symmetric case): if `μ` is symmetric
and `P(|X| > ·)` is regularly varying with index `-α`, `0 < α < 2`, then with
`aₙ = inf {x : P(|X| > x) ≤ 1 / n}` the laws of `Sₙ / aₙ` converge weakly to the symmetric
`α`-stable law with characteristic function `exp (-C_α |t| ^ α)`. -/
theorem tendsto_map_convPow_normSeq (hsymm : μ.map (fun x => -x) = μ) (hα0 : 0 < α)
    (hα2 : α < 2) :
    ∃ ν : ProbabilityMeasure ℝ, IsSymmStable α (StableIntegral.stableConst α) (ν : Measure ℝ) ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map ((normSeq μ n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν) := by
  obtain ⟨a', ha', hea⟩ := exists_pos_eventuallyEq (tendsto_normSeq hRV)
  have hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a' n)) atTop (𝓝 1) :=
    (tendsto_mul_absTail_normSeq hRV).congr' (hea.mono fun n hn => by simp [hn])
  obtain ⟨ν, hν, hlim⟩ := tendsto_map_convPow_of_isRegularlyVarying hsymm hα0 hα2 hRV ha' hna
  refine ⟨ν, hν, hlim.congr' (hea.mono fun n hn => ?_)⟩
  exact Subtype.ext (by simp only [hn])

end NormSeq

section FellerIff

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}

/-- **Feller's criterion for the domain of attraction of a symmetric stable law**
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2], symmetric case). Let `μ` be
symmetric and `0 < α < 2`. There are `aₙ > 0` such that `Sₙ / aₙ` converges weakly to a
symmetric `α`-stable law `SαS(c)`, `c > 0`, if and only if `P(|X| > ·)` is regularly varying with
index `-α`; and then `aₙ = inf {x : P(|X| > x) ≤ 1 / n}` works, with limit `SαS(C_α)`
(`tendsto_map_convPow_normSeq`). -/
theorem domainOfAttraction_isSymmStable_iff (hsymm : μ.map (fun x => -x) = μ) (hα0 : 0 < α)
    (hα2 : α < 2) :
    (∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∃ c > 0, ∃ ν : ProbabilityMeasure ℝ,
      IsSymmStable α c (ν : Measure ℝ) ∧ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν)) ↔
      IsRegularlyVarying (absTail μ) (-α) := by
  refine ⟨fun h => (isRegularlyVarying_truncSecondMoment_of_domainOfAttraction hsymm hα0 hα2
    h).2, fun hRV => ?_⟩
  obtain ⟨a', ha', hea⟩ := exists_pos_eventuallyEq (tendsto_normSeq hRV)
  obtain ⟨ν, hν, hlim⟩ := tendsto_map_convPow_normSeq hRV hsymm hα0 hα2
  refine ⟨a', ha', _, StableIntegral.stableConst_pos hα0 hα2, ν, hν,
    hlim.congr' (hea.mono fun n hn => ?_)⟩
  exact Subtype.ext (by simp only [hn])

end FellerIff

end GCLTConverse

end ExtremeValueTheory
