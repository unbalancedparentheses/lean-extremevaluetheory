/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLT
import ExtremeValueTheory.StableLaws.LevyContinuity
import ExtremeValueTheory.RegularVariation.KaramataConverse
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverse.IndexGiven

/-!
# The converse of the generalized central limit theorem (symmetric case)

Let `X₁, X₂, …` be i.i.d. with a *symmetric* law `μ`, let `aₙ > 0`, and suppose that the laws
of `Sₙ / aₙ = (X₁ + ⋯ + Xₙ) / aₙ` converge weakly to a law `ν ≠ δ₀`. We prove the necessity half
of Feller's criterion for the domain of attraction of a stable law
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2]): the truncated second moment
`U(x) = E[X² 1{|X| ≤ x}]` is regularly varying with index `2 - α` for some `0 < α ≤ 2`, and for
`α < 2` the two-sided tail `P(|X| > x)` is regularly varying with index `-α`. This is the converse
of `tendsto_map_convPow_of_isRegularlyVarying` (in
`ExtremeValueTheory.StableLaws.DomainOfAttraction`).

## Main definitions

* `minSqMoment μ x = E[min (x², X²)]` and `truncSecondMoment μ x = E[X² 1{|X| ≤ x}]`.
* `GCLTConverse.nh μ a n t = n (1 - f(t / aₙ))`, `f(s) = ∫ cos (s x) dμ`.
* `GCLTConverse.lamMeasure μ a n`, the finite measure `y² / (1 + y²) · law(X / aₙ)(dy)`, and
  `GCLTConverse.lamNorm` its normalization (a version of Feller's canonical measures).

## Main results

* `GCLTConverse.exists_isRegularlyVarying_of_tendsto`: **converse GCLT, index derived.** If
  `Sₙ / aₙ → ν ≠ δ₀` weakly, there is `0 < α ≤ 2` with `U ∈ RV(2 - α)` and, if `α < 2`,
  `P(|X| > ·) ∈ RV(-α)`. Its scaling form `exists_tendsto_mul_sqRatio_of_tendsto`
  (`n E[min (1, X² / (aₙ x)²)] → K x^(-α)`) is reused in the asymmetric case
  (`ExtremeValueTheory.StableLaws.GeneralizedCLTConverseAsymmetric`).
* `GCLTConverse.isRegularlyVarying_of_tendsto_isSymmStable`: **converse GCLT, index given.**
  If `Sₙ / aₙ → SαS(c)` with `0 < α < 2`, `c > 0`, then `P(|X| > ·) ∈ RV(-α)`,
  `U ∈ RV(2 - α)` and `n P(|X| > aₙ) → K > 0`.
* `GCLTConverse.isRegularlyVarying_truncSecondMoment_iff_absTail`: Feller's criterion in
  regular-variation form: for `0 < α < 2`, `U ∈ RV(2 - α) ↔ P(|X| > ·) ∈ RV(-α)` (via the
  identities `Z(x) = ∫₀^x 2u P(|X| > u) du`, `T(x) = 2 ∫_x^∞ U(y) y⁻³ dy` and Karamata's
  theorem); `isRegularlyVarying_truncSecondMoment_of_domainOfAttraction` (necessity) and
  `tendsto_map_convPow_of_isRegularlyVarying_truncSecondMoment` (sufficiency) give the two
  directions of Feller's domain-of-attraction criterion in the symmetric case.
* `GCLTConverse.tendsto_sq_mul_absTail_div_minSqMoment`: the elementary Tauberian step: if
  `Z(x) = E[min (x², X²)]` is `RV(ρ)` then `x² P(|X| > x) / Z(x) → ρ / 2`, hence the tail is
  `RV(ρ - 2)` (`ρ > 0`) and `U ∈ RV(ρ)` (`ρ < 2`).
* `GCLTConverse.tendsto_div_of_tendsto_mul_comp`: from sequences to functions: for monotone
  `T`, `n T(aₙ x) → L(x) > 0` implies `T(l x) / T(x) → L(l) / L(1)`
  ([Feller, §VIII.8, Lemma 3], [BGT, Theorem 1.9.2]).
* `GCLTConverse.exists_rpow_of_tendsto_div`: the limit of `T(l x) / T(x)` is a power of `l`.

## Proof outline

1. *Tightness* (`exists_forall_norm_charFun_sub_one_le`, `exists_nh_le`): the characteristic
   functions `f(t / aₙ)ⁿ` of `Sₙ / aₙ` are uniformly close to `1` for `|t| ≤ δ`; with
   `f(2s) ≥ 2 f(s)² - 1` and `1 - f(k s) ≤ k² (1 - f(s))` this gives the quadratic bound
   `hₙ(t) = n (1 - f(t / aₙ)) ≤ log 2 (|t| / δ + 1)²`.
2. *Logarithms* (`tendsto_nh`): `ψ = Re φ_ν > 0` and `hₙ(t) → h(t) = -log ψ(t)`.
3. *Canonical measures* (`charFun_kMeasure`, `charFun_lamMeasure`): with
   `1 / (1 + y²) = ∫₀^∞ e^{-s} cos (s y) ds`, the measures
   `Λₙ(dy) = n y² / (1 + y²) P(X / aₙ ∈ dy)` have characteristic functions
   `λ_{hₙ}(t) = ∫₀^∞ e^{-s} ((hₙ(t + s) + hₙ(t - s)) / 2 - hₙ(t)) ds`, which converge to
   `λ_h(t)` by dominated convergence (`tendsto_lap`).
4. *Lévy* (`exists_charFun_eq_lap`, `tendsto_mul_sqRatio`): `Λₙ / Λₙ(ℝ)` converges weakly to a
   probability `P`, so testing against the bounded continuous `(1 + y²) / max (y², x²)` gives
   `n T(aₙ x) → L(x) > 0` with `T(x) = E[min (1, X² / x²)] = Z(x) / x²`.
5. *Regular variation*: `T` is monotone, so `T(l x) / T(x) → L(l) / L(1) = l ^ (-α)`; then the
   elementary Tauberian step transfers this to `U` and to the tail. With `ν = SαS(c)` the
   scaling `aₙ ↦ r aₙ` identifies `α` (`isRegularlyVarying_of_tendsto_isSymmStable`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

namespace GCLTConverse

open Subexp

section General

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a : ℕ → ℝ}

theorem tendsto_integral_gfun_atTop (P : ProbabilityMeasure ℝ) :
    Tendsto (fun x : ℝ => ∫ y, (1 + y ^ 2) / max (y ^ 2) (x ^ 2) ∂(P : Measure ℝ)) atTop
      (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _y, (0 : ℝ) ∂(P : Measure ℝ) := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => gfun one_pos y) ?_ ?_
    ((gfun one_pos).integrable _) (ae_of_all _ fun y => ?_)
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact (gfun hx).continuous.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with x hx
    refine ae_of_all _ fun y => ?_
    have hM : 0 < max (y ^ 2) (1 ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    rw [gfun_apply, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity)
      (le_max_of_le_right (sq_nonneg _)))]
    exact div_le_div_of_nonneg_left (by positivity) hM
      (max_le_max le_rfl (pow_le_pow_left₀ zero_le_one hx 2))
  · have h1 : Tendsto (fun x : ℝ => (1 + y ^ 2) / x ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · exact Eventually.of_forall fun x =>
        div_nonneg (by positivity) (le_max_of_le_left (sq_nonneg _))
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (le_max_right _ _)

/-- If `n E[min (1, X² / (aₙ x)²)] → K x ^ (-α)` for all `x > 0`, with `K > 0`, then
`Z(x) = E[min (x², X²)]` is regularly varying with index `2 - α`. -/
theorem isRegularlyVarying_minSqMoment_of_tendsto_mul_sqRatio {μ : Measure ℝ}
    [IsFiniteMeasure μ] {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) {K α : ℝ} (hK : 0 < K)
    (hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n * x)) atTop
      (𝓝 (K * x ^ (-α)))) :
    IsRegularlyVarying (minSqMoment μ) (2 - α) := by
  have hL1 : Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n)) atTop (𝓝 K) := by
    simpa using hL 1 one_pos
  have hTpos : ∀ x, 0 < x → 0 < sqRatio μ x := by
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hL1).1 0 hK).exists
    have h1 : 0 < sqRatio μ (a n) := by
      by_contra hc
      have : sqRatio μ (a n) = 0 := le_antisymm (not_lt.1 hc) (sqRatio_nonneg _)
      rw [this, mul_zero] at hn
      exact lt_irrefl _ hn
    exact fun x hx => sqRatio_pos_of_pos (ha n) h1 hx
  have hT : IsRegularlyVarying (sqRatio μ) (-α) :=
    isRegularlyVarying_of_tendsto_mul_comp sqRatio_antitoneOn hTpos ha hK hL
  have := (IsRegularlyVarying.rpow_id 2).mul hT
  rw [← sub_eq_add_neg] at this
  refine this.congr ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [sqRatio_eq_div hx.ne', Real.rpow_two]
  field_simp

/-- **The scaling limit behind the converse GCLT** (symmetric case). Let `μ` be a symmetric
probability law on `ℝ`, `aₙ > 0`, and suppose the laws of `(X₁ + ⋯ + Xₙ) / aₙ` converge weakly
to a law `ν ≠ δ₀`. Then there are `0 < α ≤ 2` and `K > 0` with
`n E[min (1, X² / (aₙ x)²)] → K x ^ (-α)` for every `x > 0`. -/
theorem exists_tendsto_mul_sqRatio_of_tendsto (hsymm : μ.map (fun x => -x) = μ)
    (ha : ∀ n, 0 < a n) {ν : ProbabilityMeasure ℝ} (hnd : (ν : Measure ℝ) ≠ Measure.dirac 0)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 2 ∧ ∃ K > 0, ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n * x)) atTop (𝓝 (K * x ^ (-α))) := by
  obtain ⟨δ, hδ, hb⟩ := exists_nh_le hsymm hconv
  set B := Real.log 2
  have hB0 : 0 ≤ B := Real.log_nonneg one_le_two
  set ψ : ℝ → ℝ := fun u => (charFun (ν : Measure ℝ) u).re with hψ
  set h : ℝ → ℝ := fun u => -Real.log (ψ u) with hh
  have hψpos : ∀ u, 0 < ψ u := fun u => (tendsto_nh hsymm hconv hb u).1
  have hlim : ∀ u, Tendsto (fun n => nh μ a n u) atTop (𝓝 (h u)) :=
    fun u => (tendsto_nh hsymm hconv hb u).2
  have hBa : ∀ᶠ n in atTop, ∀ u, |nh μ a n u| ≤ B * (|u| / δ + 1) ^ 2 := by
    filter_upwards [eventually_ge_atTop 3] with n hn u
    rw [abs_of_nonneg (nh_nonneg _ _)]
    exact hb n hn u
  have hhnn : ∀ u, 0 ≤ h u := fun u =>
    ge_of_tendsto (hlim u) (Eventually.of_forall fun n => nh_nonneg _ _)
  have hhc : Continuous h :=
    ((Complex.continuous_re.comp continuous_charFun).log fun u => (hψpos u).ne').neg
  have hhb : ∀ u, |h u| ≤ B * (|u| / δ + 1) ^ 2 := by
    intro u
    rw [abs_of_nonneg (hhnn u)]
    exact le_of_tendsto (hlim u) (by
      filter_upwards [hBa] with n hn
      exact (le_abs_self _).trans (hn u))
  have hh0 : h 0 = 0 := by
    simp [hh, hψ, charFun_zero]
  have hheven : ∀ u, h (-u) = h u := fun u =>
    tendsto_nhds_unique (hlim (-u)) (by simpa only [nh_neg] using hlim u)
  -- non-degeneracy gives `h(s₀) > 0` for some `s₀ > 0`
  obtain ⟨s₀, hs₀, hhs₀⟩ : ∃ s₀ > 0, 0 < h s₀ := by
    have : ∃ t, charFun (ν : Measure ℝ) t ≠ 1 := by
      by_contra hc
      apply hnd
      refine Measure.ext_of_charFun (funext fun t => ?_)
      have h1 : charFun (ν : Measure ℝ) t = 1 := by
        by_contra h'
        exact hc ⟨t, h'⟩
      rw [h1, charFun_dirac]
      simp
    obtain ⟨t, ht⟩ := this
    have hlt : ψ t < 1 := by
      have hn1 : ‖charFun (ν : Measure ℝ) t‖ ≤ 1 := norm_charFun_le_one t
      refine lt_of_le_of_ne ((Complex.re_le_norm _).trans hn1) fun heq => ht ?_
      have hsq : ‖charFun (ν : Measure ℝ) t‖ ^ 2 = (charFun (ν : Measure ℝ) t).re ^ 2 +
          (charFun (ν : Measure ℝ) t).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have him : (charFun (ν : Measure ℝ) t).im = 0 := by
        have : ‖charFun (ν : Measure ℝ) t‖ ^ 2 ≤ 1 := by
          have := norm_nonneg (charFun (ν : Measure ℝ) t); nlinarith
        simp only [hψ] at heq
        rw [hsq, heq] at this
        nlinarith [sq_nonneg (charFun (ν : Measure ℝ) t).im]
      exact Complex.ext (by simpa [hψ] using heq) (by simpa using him)
    have hpos : 0 < h t := by
      simp only [hh]
      exact neg_pos.2 (Real.log_neg (hψpos t) hlt)
    have ht0 : t ≠ 0 := by rintro rfl; rw [hh0] at hpos; exact lt_irrefl _ hpos
    refine ⟨|t|, abs_pos.2 ht0, ?_⟩
    rcases le_or_gt 0 t with h0 | h0
    · rwa [abs_of_nonneg h0]
    · rwa [abs_of_neg h0, hheven]
  have hpos : 0 < lap h 0 := lap_pos hB0 hδ hhc hhb hh0 hhnn hs₀ hhs₀
  obtain ⟨P, hP⟩ := exists_charFun_eq_lap hsymm hB0 hδ hBa hlim hpos hhc hhb
  set L : ℝ → ℝ := fun x => lap h 0 * ∫ y, (1 + y ^ 2) / max (y ^ 2) (x ^ 2) ∂(P : Measure ℝ)
  have hlimL : ∀ x, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n * x)) atTop
      (𝓝 (L x)) := fun x hx => tendsto_mul_sqRatio hsymm ha hB0 hδ hBa hlim hpos P hP hx
  have hLpos : ∀ x, 0 < x → 0 < L x := fun x hx => mul_pos hpos (integral_gfun_pos P hx)
  have hL1 : Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n)) atTop (𝓝 (L 1)) := by
    simpa using hlimL 1 one_pos
  have hTpos : ∀ x, 0 < x → 0 < sqRatio μ x := by
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hL1).1 0 (hLpos 1 one_pos)).exists
    have h1 : 0 < sqRatio μ (a n) := by
      by_contra hc
      have : sqRatio μ (a n) = 0 := le_antisymm (not_lt.1 hc) (sqRatio_nonneg _)
      rw [this, mul_zero] at hn
      exact lt_irrefl _ hn
    exact fun x hx => sqRatio_pos_of_pos (ha n) h1 hx
  have hratio : ∀ l, 0 < l → Tendsto (fun x => sqRatio μ (l * x) / sqRatio μ x) atTop
      (𝓝 (L l / L 1)) := fun l hl =>
    tendsto_div_of_tendsto_mul_comp sqRatio_antitoneOn hTpos ha hlimL hLpos hl
  obtain ⟨ρ, hρ0, hρ⟩ := exists_rpow_of_tendsto_div sqRatio_antitoneOn hTpos
    (fun l hl => div_pos (hLpos l hl) (hLpos 1 one_pos)) hratio
  have hLρ : ∀ x, 0 < x → L x = L 1 * x ^ ρ := fun x hx => by
    have := hρ x hx
    rw [div_eq_iff (hLpos 1 one_pos).ne'] at this
    rw [this, mul_comm]
  -- `α = -ρ > 0`: otherwise `L` would be constant, but `L x → 0`
  have hρneg : ρ < 0 := by
    rcases lt_or_eq_of_le hρ0 with hρz | hρz
    · exact hρz
    · exfalso
      have hconst : ∀ x, 0 < x → L x = L 1 := fun x hx => by
        rw [hLρ x hx, hρz]; simp
      have hto : Tendsto L atTop (𝓝 0) := by
        have := (tendsto_integral_gfun_atTop P).const_mul (lap h 0)
        simpa [L] using this
      have : Tendsto L atTop (𝓝 (L 1)) := tendsto_const_nhds.congr' (by
        filter_upwards [eventually_gt_atTop 0] with x hx
        exact (hconst x hx).symm)
      exact (hLpos 1 one_pos).ne' (tendsto_nhds_unique this hto)
  set α := -ρ with hα
  have hα0 : 0 < α := by linarith
  have hTRV : IsRegularlyVarying (sqRatio μ) (-α) := by
    rw [hα, neg_neg]
    refine ⟨(eventually_gt_atTop 0).mono hTpos, fun l hl => ?_⟩
    rw [← hρ l hl]
    exact hratio l hl
  have hZ : IsRegularlyVarying (minSqMoment μ) (2 - α) := by
    have := (IsRegularlyVarying.rpow_id 2).mul hTRV
    rw [← sub_eq_add_neg] at this
    refine this.congr ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [sqRatio_eq_div hx.ne', Real.rpow_two]
    field_simp
  have hα2 : α ≤ 2 := by
    by_contra hc
    replace hc : 2 < α := not_le.1 hc
    have h2 := hZ.2 2 two_pos
    have hle : (1 : ℝ) ≤ 2 ^ (2 - α) := ge_of_tendsto h2 (by
      filter_upwards [hZ.1, eventually_gt_atTop 0] with x hx hx0
      rw [le_div_iff₀ hx, one_mul]
      exact minSqMoment_mono hx0.le (by linarith))
    have : (2 : ℝ) ^ (2 - α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    linarith
  refine ⟨α, hα0, hα2, L 1, hLpos 1 one_pos, fun x hx => ?_⟩
  rw [hα, neg_neg, ← hLρ x hx]
  exact hlimL x hx

/-- **Converse of the generalized central limit theorem, symmetric case, with the index
derived** (Feller's criterion, necessity: [Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35]).
Let `μ` be a symmetric probability law on `ℝ`, `aₙ > 0`, and suppose the laws of
`(X₁ + ⋯ + Xₙ) / aₙ` converge weakly to a law `ν ≠ δ₀`. Then there is `0 < α ≤ 2` such that
the truncated second moment `U(x) = E[X² 1{|X| ≤ x}]` is regularly varying with index `2 - α`,
and, if `α < 2`, the two-sided tail `P(|X| > x)` is regularly varying with index `-α`. -/
theorem exists_isRegularlyVarying_of_tendsto (hsymm : μ.map (fun x => -x) = μ)
    (ha : ∀ n, 0 < a n) {ν : ProbabilityMeasure ℝ} (hnd : (ν : Measure ℝ) ≠ Measure.dirac 0)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ α, 0 < α ∧ α ≤ 2 ∧ IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧
      (α < 2 → IsRegularlyVarying (absTail μ) (-α)) := by
  obtain ⟨α, hα0, hα2, K, hK, hL⟩ := exists_tendsto_mul_sqRatio_of_tendsto hsymm ha hnd hconv
  have hZ : IsRegularlyVarying (minSqMoment μ) (2 - α) :=
    isRegularlyVarying_minSqMoment_of_tendsto_mul_sqRatio ha hK hL
  refine ⟨α, hα0, hα2, isRegularlyVarying_truncSecondMoment_of_minSqMoment (by linarith) hZ,
    fun hlt => ?_⟩
  have hG := isRegularlyVarying_absTail_of_minSqMoment (by linarith) hZ
  rwa [show 2 - α - 2 = -α by ring] at hG

end General

section Sufficiency

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem truncSecondMoment_eq_integral (y : ℝ) :
    truncSecondMoment μ y = ∫ z, {z : ℝ | |z| ≤ y}.indicator (fun z => z ^ 2) z ∂μ :=
  (integral_indicator (measurableSet_abs_le y)).symm

theorem integrable_indicator_sq (y : ℝ) :
    Integrable ({z : ℝ | |z| ≤ y}.indicator (fun z => z ^ 2)) μ := by
  refine (integrable_const (y ^ 2)).mono' ?_ (ae_of_all _ fun z => ?_)
  · exact ((continuous_pow 2).aestronglyMeasurable).indicator (measurableSet_abs_le y)
  · by_cases h : |z| ≤ y
    · rw [Set.indicator_of_mem (show z ∈ {z : ℝ | |z| ≤ y} from h), Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq_of_abs_le h
    · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | |z| ≤ y} from h), norm_zero]
      positivity

theorem truncSecondMoment_mono : Monotone (truncSecondMoment μ) := by
  intro y y' hyy'
  rw [truncSecondMoment_eq_integral, truncSecondMoment_eq_integral]
  refine integral_mono (integrable_indicator_sq y) (integrable_indicator_sq y') fun z => ?_
  by_cases h : |z| ≤ y
  · rw [Set.indicator_of_mem (show z ∈ {z : ℝ | |z| ≤ y} from h),
      Set.indicator_of_mem (show z ∈ {z : ℝ | |z| ≤ y'} from h.trans hyy')]
  · rw [Set.indicator_of_notMem (show z ∉ {z : ℝ | |z| ≤ y} from h)]
    exact Set.indicator_nonneg (fun z _ => sq_nonneg z) z

/-- `z² ∫_{(x, ∞)} 1{|z| ≤ y} y⁻³ dy = (z² / max (z², x²)) / 2`. -/
theorem setIntegral_indicator_rpow {x : ℝ} (hx : 0 < x) (z : ℝ) :
    ∫ y in Ioi x, {y : ℝ | |z| ≤ y}.indicator (fun y => z ^ 2 * y ^ (-3 : ℝ)) y =
      z ^ 2 / max (z ^ 2) (x ^ 2) / 2 := by
  have hset : {y : ℝ | |z| ≤ y} = Ici |z| := rfl
  rw [hset, setIntegral_indicator measurableSet_Ici, integral_const_mul]
  have key : ∀ m : ℝ, 0 < m → m ^ 2 = max (z ^ 2) (x ^ 2) →
      ∫ y in Ioi m, y ^ (-3 : ℝ) = 1 / (2 * max (z ^ 2) (x ^ 2)) := by
    intro m hm hm2
    rw [integral_Ioi_rpow_of_lt (by norm_num) hm, ← hm2]
    rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hm.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hM : 0 < max (z ^ 2) (x ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  rcases le_or_gt |z| x with h | h
  · have e : Ioi x ∩ Ici |z| = Ioi x := by
      ext y; simp only [mem_inter_iff, mem_Ioi, mem_Ici]
      exact ⟨fun h' => h'.1, fun h' => ⟨h', h.trans h'.le⟩⟩
    rw [e, key x hx (max_eq_right (sq_le_sq_of_abs_le h)).symm]
    field_simp
  · have e : Ioi x ∩ Ici |z| = Ici |z| := by
      ext y; simp only [mem_inter_iff, mem_Ioi, mem_Ici]
      exact ⟨fun h' => h'.2, fun h' => ⟨h.trans_le h', h'⟩⟩
    rw [e, integral_Ici_eq_integral_Ioi, key |z| (hx.trans h)
      (by rw [sq_abs, max_eq_left (sq_le_sq_of_le_abs hx.le h.le)])]
    field_simp

/-- **Integral representation of `T`.** `E[min (1, X² / x²)] = 2 ∫_{(x, ∞)} U(y) y⁻³ dy`. -/
theorem sqRatio_eq_integral {x : ℝ} (hx : 0 < x) :
    sqRatio μ x = 2 * ∫ y in Ioi x, truncSecondMoment μ y * y ^ (-3 : ℝ) := by
  set K : ℝ → ℝ → ℝ := fun z y => {y : ℝ | |z| ≤ y}.indicator (fun y => z ^ 2 * y ^ (-3 : ℝ)) y
    with hK
  have hKm : Measurable (Function.uncurry K) := by
    have : Function.uncurry K = {p : ℝ × ℝ | |p.1| ≤ p.2}.indicator
        (fun p => p.1 ^ 2 * p.2 ^ (-3 : ℝ)) := rfl
    rw [this]
    exact Measurable.indicator (by fun_prop) (measurableSet_le (by fun_prop) (by fun_prop))
  have hKnn : ∀ z y, 0 ≤ K z y := fun z y => by
    simp only [hK]
    by_cases h : |z| ≤ y
    · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | |z| ≤ y} from h)]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ((abs_nonneg _).trans h) _)
    · rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | |z| ≤ y} from h)]
  have hgcont : Continuous fun z : ℝ => z ^ 2 / max (z ^ 2) (x ^ 2) / 2 :=
    (Continuous.div (by fun_prop) (by fun_prop) fun z =>
      ne_of_gt (lt_of_lt_of_le (by positivity) (le_max_right _ _))).div_const _
  have hint : Integrable (Function.uncurry K) (μ.prod (volume.restrict (Ioi x))) := by
    refine (integrable_prod_iff hKm.aestronglyMeasurable).2 ⟨ae_of_all _ fun z => ?_, ?_⟩
    · refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hx).const_mul
        (z ^ 2)).mono' (by
          have : Measurable fun y => K z y := hKm.comp (measurable_const.prodMk measurable_id)
          exact this.aestronglyMeasurable) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun y (hy : x < y) => ?_
      simp only [Function.uncurry_apply_pair]
      rw [Real.norm_eq_abs, abs_of_nonneg (hKnn z y)]
      simp only [hK]
      by_cases h : |z| ≤ y
      · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | |z| ≤ y} from h)]
      · rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | |z| ≤ y} from h)]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hx.trans hy).le _)
    · have e : (fun z => ∫ y in Ioi x, ‖Function.uncurry K (z, y)‖) =
          fun z => z ^ 2 / max (z ^ 2) (x ^ 2) / 2 := by
        funext z
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (hKnn _ _)]
        exact setIntegral_indicator_rpow hx z
      rw [e]
      refine (integrable_const (1 : ℝ)).mono' hgcont.aestronglyMeasurable
        (ae_of_all _ fun z => ?_)
      have hM : 0 < max (z ^ 2) (x ^ 2) := lt_of_lt_of_le (by positivity) (le_max_right _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one two_pos]
      exact ((div_le_one hM).2 (le_max_left _ _)).trans one_le_two
  have hswap := integral_integral_swap hint
  have e1 : ∀ y, truncSecondMoment μ y * y ^ (-3 : ℝ) = ∫ z, K z y ∂μ := by
    intro y
    rw [truncSecondMoment_eq_integral, ← integral_mul_const]
    congr 1; funext z
    simp only [hK]
    by_cases h : |z| ≤ y
    · rw [Set.indicator_of_mem (show y ∈ {y : ℝ | |z| ≤ y} from h),
        Set.indicator_of_mem (show z ∈ {z : ℝ | |z| ≤ y} from h)]
    · rw [Set.indicator_of_notMem (show y ∉ {y : ℝ | |z| ≤ y} from h),
        Set.indicator_of_notMem (show z ∉ {z : ℝ | |z| ≤ y} from h), zero_mul]
  simp_rw [e1]
  rw [← hswap]
  simp_rw [hK, setIntegral_indicator_rpow hx]
  rw [integral_div, sqRatio]
  ring

/-- If `U` is regularly varying with index `ρ < 2`, then `Z(x) / U(x) → 2 / (2 - ρ)`. -/
theorem tendsto_minSqMoment_div_truncSecondMoment {ρ : ℝ} (hρ2 : ρ < 2)
    (hU : IsRegularlyVarying (truncSecondMoment μ) ρ) :
    Tendsto (fun x => minSqMoment μ x / truncSecondMoment μ x) atTop (𝓝 (2 / (2 - ρ))) := by
  set F : ℝ → ℝ := fun y => truncSecondMoment μ y * y ^ (-3 : ℝ)
  have hF : IsRegularlyVarying F (-(3 - ρ)) := by
    have := hU.mul (IsRegularlyVarying.rpow_id (-3))
    rwa [show ρ + -3 = -(3 - ρ) by ring] at this
  have hFm : Measurable F :=
    truncSecondMoment_mono.measurable.mul (measurable_id.pow_const _)
  have hK := IsRegularlyVarying.tendsto_integral_Ioi_div_of_measurable hFm hF (by linarith)
  rw [show 3 - ρ - 1 = 2 - ρ by ring] at hK
  have := hK.const_mul 2
  rw [show 2 * (1 / (2 - ρ)) = 2 / (2 - ρ) by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hU.1] with x hx hUx
  have hZ : minSqMoment μ x = x ^ 2 * sqRatio μ x := by
    rw [sqRatio_eq_div hx.ne']; field_simp
  rw [hZ, sqRatio_eq_integral hx]
  simp only [F]
  rw [Real.rpow_neg hx.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- **Feller's criterion, sufficiency of the second-moment condition.** If the truncated second
moment `U` is regularly varying with index `ρ ∈ (0, 2)`, then the two-sided tail is regularly
varying with index `ρ - 2`. -/
theorem isRegularlyVarying_absTail_of_truncSecondMoment {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ < 2)
    (hU : IsRegularlyVarying (truncSecondMoment μ) ρ) :
    IsRegularlyVarying (absTail μ) (ρ - 2) :=
  isRegularlyVarying_absTail_of_minSqMoment hρ0
    (hU.of_tendsto_div (tendsto_minSqMoment_div_truncSecondMoment hρ2 hU)
      (div_pos two_pos (by linarith)))

end Sufficiency

section Necessity

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- **Layer cake for `Z`.** `E[min (x², X²)] = ∫_{(0, x)} 2 u P(|X| > u) du` for `x ≥ 0`. -/
theorem minSqMoment_eq_setIntegral {x : ℝ} (hx : 0 ≤ x) :
    minSqMoment μ x = ∫ u in Ioo 0 x, 2 * u * absTail μ u := by
  set g : ℝ → ℝ := fun u => 2 * max (min u x) 0 with hg
  have hgm : Measurable g := by fun_prop
  have hgB : ∀ u, |g u| ≤ 2 * x := fun u => by
    simp only [hg]
    rw [abs_of_nonneg (by positivity)]
    have : max (min u x) 0 ≤ x := max_le (min_le_right _ _) hx
    linarith
  have hlc := GCLT.integral_setIntegral_Ioo_min (ν := μ.map (fun z => |z|)) hgm hgB one_pos x
  have hinner : ∀ w : ℝ, 0 ≤ w → ∫ u in Ioo 0 (min (w / 1) x), g u = min (x ^ 2) (w ^ 2) := by
    intro w hw
    rw [div_one]
    have hcongr : ∫ u in Ioo 0 (min w x), g u = ∫ u in Ioo 0 (min w x), 2 * u :=
      setIntegral_congr_fun measurableSet_Ioo fun u hu => by
        simp only [hg]
        rw [min_eq_left (hu.2.le.trans (min_le_right _ _)), max_eq_left hu.1.le]
    rw [hcongr, GCLT.setIntegral_Ioo_eq_sub (F := fun u => u ^ 2) (fun u => by
      simpa [mul_comm] using hasDerivAt_pow 2 u) (by fun_prop),
      max_eq_left (le_min hw hx)]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
    rcases le_total w x with h | h
    · rw [min_eq_left h, min_eq_right (pow_le_pow_left₀ hw h 2)]
    · rw [min_eq_right h, min_eq_left (pow_le_pow_left₀ hx h 2)]
  rw [integral_map (by fun_prop) (by
    have : Measurable fun w : ℝ => ∫ u in Ioo 0 (min (w / 1) x), g u := by
      have h1 : (fun w : ℝ => ∫ u in Ioo 0 (min (w / 1) x), g u) =
          fun w => if 0 ≤ w then min (x ^ 2) (w ^ 2) else 0 := by
        funext w
        split_ifs with hw
        · exact hinner w hw
        · rw [Ioo_eq_empty (not_lt.2 (min_le_left _ _ |>.trans (by
            rw [div_one]; exact (not_le.1 hw).le))), Measure.restrict_empty,
            integral_zero_measure]
      rw [h1]
      exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
    exact this.aestronglyMeasurable)] at hlc
  rw [minSqMoment]
  have e1 : ∫ z, min (x ^ 2) (z ^ 2) ∂μ = ∫ z, (∫ u in Ioo 0 (min (|z| / 1) x), g u) ∂μ :=
    integral_congr_ae (ae_of_all _ fun z => by simp only; rw [hinner |z| (abs_nonneg z), sq_abs])
  rw [e1, hlc]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  simp only [hg, one_mul]
  rw [min_eq_left hu.2.le, max_eq_left hu.1.le, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Ioi, absTail, measureReal_def]
  rfl

/-- If the two-sided tail is regularly varying with index `-α`, `α < 2`, then
`Z(x) / (x² P(|X| > x)) → 2 / (2 - α)`. -/
theorem tendsto_minSqMoment_div_sq_mul_absTail {α : ℝ} (hα2 : α < 2)
    (hG : IsRegularlyVarying (absTail μ) (-α)) :
    Tendsto (fun x => minSqMoment μ x / (x ^ 2 * absTail μ x)) atTop (𝓝 (2 / (2 - α))) := by
  set f : ℝ → ℝ := fun u => 2 * u * absTail μ u with hfdef
  have hf : IsRegularlyVarying f (1 + -α) := by
    have := ((IsRegularlyVarying.rpow_id 1).const_mul two_pos).mul hG
    refine this.congr ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    simp [f, Real.rpow_one]
  have hfm : Measurable f := by
    have : Measurable (absTail μ) := GCLT.absTail_antitone.measurable
    fun_prop
  have hfi : ∀ x, IntervalIntegrable f volume 0 x := fun x =>
    (GCLT.absTail_antitone (μ := μ)).intervalIntegrable.continuousOn_mul
      (by fun_prop : Continuous fun u : ℝ => 2 * u).continuousOn
  have hK := IsRegularlyVarying.tendsto_integral_zero_div hf hfm (by linarith) hfi
  rw [show 1 + -α + 1 = 2 - α by ring] at hK
  have := hK.const_mul 2
  rw [show 2 * (1 / (2 - α)) = 2 / (2 - α) by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [minSqMoment_eq_setIntegral hx.le, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hx.le]
  simp only [hfdef]
  rcases eq_or_ne (absTail μ x) 0 with h0 | h0
  · simp [h0]
  · field_simp

/-- **Feller's criterion, tails to second moments.** If the two-sided tail is regularly varying
with index `-α`, `0 < α < 2`, then the truncated second moment `U` is regularly varying with
index `2 - α`. -/
theorem isRegularlyVarying_truncSecondMoment_of_absTail {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hG : IsRegularlyVarying (absTail μ) (-α)) :
    IsRegularlyVarying (truncSecondMoment μ) (2 - α) := by
  have hsq : IsRegularlyVarying (fun x => x ^ 2 * absTail μ x) (2 + -α) := by
    have := (IsRegularlyVarying.rpow_id 2).mul hG
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← sub_eq_add_neg] at hsq
  have hZ := hsq.of_tendsto_div (tendsto_minSqMoment_div_sq_mul_absTail hα2 hG)
    (div_pos two_pos (by linarith))
  exact isRegularlyVarying_truncSecondMoment_of_minSqMoment (by linarith) hZ

end Necessity

section Feller

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}

/-- **Feller's criterion, regular-variation form** ([Feller, Vol. II, §VIII.9, Theorem 2 and
§XVII.5]): for `0 < α < 2`, the truncated second moment `U(x) = E[X² 1{|X| ≤ x}]` is regularly
varying with index `2 - α` if and only if the two-sided tail `P(|X| > x)` is regularly varying
with index `-α`. -/
theorem isRegularlyVarying_truncSecondMoment_iff_absTail (hα0 : 0 < α) (hα2 : α < 2) :
    IsRegularlyVarying (truncSecondMoment μ) (2 - α) ↔ IsRegularlyVarying (absTail μ) (-α) := by
  refine ⟨fun hU => ?_, isRegularlyVarying_truncSecondMoment_of_absTail hα0 hα2⟩
  have := isRegularlyVarying_absTail_of_truncSecondMoment (by linarith) (by linarith) hU
  rwa [show 2 - α - 2 = -α by ring] at this

/-- **Generalized CLT from the second-moment condition** (sufficiency in Feller's criterion,
symmetric case): if `μ` is symmetric, `U ∈ RV(2 - α)` with `0 < α < 2`, and `n P(|X| > aₙ) → 1`,
then `Sₙ / aₙ` converges weakly to the symmetric `α`-stable law with characteristic function
`exp (-C_α |t| ^ α)`. -/
theorem tendsto_map_convPow_of_isRegularlyVarying_truncSecondMoment
    (hsymm : μ.map (fun x => -x) = μ) (hα0 : 0 < α) (hα2 : α < 2)
    (hU : IsRegularlyVarying (truncSecondMoment μ) (2 - α)) {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) :
    ∃ ν : ProbabilityMeasure ℝ, IsSymmStable α (StableIntegral.stableConst α) (ν : Measure ℝ) ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν) :=
  tendsto_map_convPow_of_isRegularlyVarying hsymm hα0 hα2
    ((isRegularlyVarying_truncSecondMoment_iff_absTail hα0 hα2).1 hU) ha hna

/-- **Feller's criterion, necessity** (symmetric case): if `Sₙ / aₙ` converges weakly to a
symmetric `α`-stable law with `0 < α < 2` for some `aₙ > 0`, then `U ∈ RV(2 - α)` and
`P(|X| > ·) ∈ RV(-α)`. -/
theorem isRegularlyVarying_truncSecondMoment_of_domainOfAttraction
    (hsymm : μ.map (fun x => -x) = μ) (hα0 : 0 < α) (hα2 : α < 2)
    (h : ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∃ c > 0, ∃ ν : ProbabilityMeasure ℝ,
      IsSymmStable α c (ν : Measure ℝ) ∧ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν)) :
    IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧ IsRegularlyVarying (absTail μ) (-α) := by
  obtain ⟨a, ha, c, hc, ν, hν, hconv⟩ := h
  obtain ⟨hG, hU, -⟩ := isRegularlyVarying_of_tendsto_isSymmStable hsymm ha hα0 hα2 hc hν hconv
  exact ⟨hU, hG⟩

end Feller

end GCLTConverse

end ExtremeValueTheory
