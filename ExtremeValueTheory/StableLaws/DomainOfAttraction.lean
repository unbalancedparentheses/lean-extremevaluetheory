/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.Basic
import ExtremeValueTheory.StableLaws.TailIntegral
import ExtremeValueTheory.StableLaws.LevyContinuity
import ExtremeValueTheory.RegularVariation.Karamata
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Pareto

/-!
# The generalized central limit theorem (symmetric case)

Let `X₁, X₂, …` be i.i.d. with a *symmetric* law `μ` whose two-sided tail
`G(x) = P(|X| > x)` is regularly varying with index `-α`, `0 < α < 2`, and let `aₙ > 0` with
`n G(aₙ) → 1`. Then
`(X₁ + ⋯ + Xₙ) / aₙ → SαS`, the symmetric `α`-stable law with characteristic function
`exp (-C_α |t| ^ α)`, `C_α = α ∫₀^∞ (1 - cos u) u^(-α-1) du`
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2], [EKM, Theorem 2.2.8],
[ST, §1.1]).

## Main results

* `GCLT.tendsto_mul_integral_one_sub_cos`: the Tauberian step
  `n (1 - φ(t / aₙ)) = n ∫ (1 - cos (t x / aₙ)) dμ → C_α |t| ^ α`.
* `GCLT.tendsto_charFun_map_convPow`: `φ_{Sₙ / aₙ}(t) = φ(t / aₙ) ^ n → exp (-C_α |t| ^ α)`.
* `tendsto_map_convPow_of_isRegularlyVarying`: **generalized CLT**, in the form: there is a
  probability measure `ν`, symmetric `α`-stable with `c = C_α`, and `law (Sₙ / aₙ) → ν`
  weakly. The limit is produced by our Lévy continuity theorem
  `exists_tendsto_of_tendsto_charFun`, so this also proves *existence* of `SαS` laws.
* `tendstoInDistribution_inv_mul_sum_of_isRegularlyVarying`: the same statement for
  i.i.d. random variables, as convergence in distribution (mirroring Mathlib's CLT
  `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`).
* `exists_isSymmStable`: for every `0 < α ≤ 2` and `c > 0` there is a probability measure with
  characteristic function `exp (-c |t| ^ α)` (for `α < 2` via the generalized CLT applied to a
  symmetrized Pareto law, for `α = 2` the Gaussian).

## Proof outline

With `ν_n(du)` the image of `n μ` under `x ↦ |x| / aₙ` (so `ν_n (u, ∞) = n G(aₙ u)`):

1. *Layer-cake/Fubini* (`integral_one_sub_cos_min`): for every `M > 0`,
   `∫ (1 - cos (t min (|x| / a, M))) dμ = ∫₀^M t sin (t u) G(a u) du`.
2. *Truncation* (`abs_integral_sub_le`): replacing `min (|x| / a, M)` by `|x| / a` costs at
   most `2 G(a M)`, so after multiplying by `n` at most `2 n G(aₙ M) → 2 M^(-α)`.
3. *Dominated convergence* (`tendsto_setIntegral_sin_mul`): `n G(aₙ u) → u^(-α)` pointwise
   (regular variation), dominated on `(0, M)` by `K (u^(-α-δ) + u^(-α+δ))` thanks to the
   Potter bounds `IsRegularlyVarying.potter_bound`; since `|t sin (t u)| ≤ t² u` and
   `α < 2`, `t² u · u^(-α-δ)` is integrable at `0`.
4. *Integration by parts* (`StableIntegral.tendsto_intervalIntegral_sin_mul_rpow`):
   `∫₀^M t sin (t u) u^(-α) du → C_α |t|^α` as `M → ∞`.
5. `(1 + gₙ)ⁿ → e^{-c}` when `n gₙ → -c`, and Lévy's continuity theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

open Subexp StableIntegral

/-- The two-sided tail `G(x) = μ {y | x < |y|} = P(|X| > x)`. -/
noncomputable def absTail (μ : Measure ℝ) (x : ℝ) : ℝ := μ.real {y | x < |y|}

namespace GCLT

theorem measurableSet_abs_gt (x : ℝ) : MeasurableSet {y : ℝ | x < |y|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

variable {μ : Measure ℝ}

theorem absTail_antitone [IsFiniteMeasure μ] : Antitone (absTail μ) := fun x x' h =>
  measureReal_mono (fun y (hy : x' < |y|) => (lt_of_le_of_lt h hy : x < |y|))

theorem absTail_le_one [IsProbabilityMeasure μ] (x : ℝ) : absTail μ x ≤ 1 := measureReal_le_one

/-- An abstract `ε/4`-approximation argument: if `Lₙ` is within `R_M(n)` of `I_M(n)`, with
`I_M(n) → J(M)`, `R_M(n) → r(M)`, `J(M) → c` and `r(M) → 0`, then `Lₙ → c`. -/
theorem tendsto_of_approx {L : ℕ → ℝ} {I R : ℝ → ℕ → ℝ} {J r : ℝ → ℝ} {c : ℝ}
    (hLI : ∀ M, 0 < M → ∀ n, |L n - I M n| ≤ R M n)
    (hI : ∀ M, 0 < M → Tendsto (I M) atTop (𝓝 (J M)))
    (hR : ∀ M, 0 < M → Tendsto (R M) atTop (𝓝 (r M)))
    (hJ : Tendsto J atTop (𝓝 c)) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto L atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨M, hM0, hMJ, hMr⟩ : ∃ M, 0 < M ∧ |J M - c| < ε / 4 ∧ |r M| < ε / 4 := by
    have h1 := (Metric.tendsto_nhds.1 hJ) _ hε4
    have h2 := (Metric.tendsto_nhds.1 hr) _ hε4
    obtain ⟨M, hM⟩ := (h1.and (h2.and (eventually_gt_atTop 0))).exists
    refine ⟨M, hM.2.2, ?_, ?_⟩
    · simpa [Real.dist_eq] using hM.1
    · simpa [Real.dist_eq] using hM.2.1
  have h3 := (Metric.tendsto_nhds.1 (hI M hM0)) _ hε4
  have h4 := (Metric.tendsto_nhds.1 (hR M hM0)) _ hε4
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h3.and h4)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h5, h6⟩ := hN n hn
  rw [Real.dist_eq] at h5 h6 ⊢
  have h7 := hLI M hM0 n
  have h8 : R M n < ε / 2 := by
    have := (abs_lt.1 h6).2; have := le_abs_self (r M); linarith
  calc |L n - c| = |(L n - I M n) + (I M n - J M) + (J M - c)| := by ring_nf
    _ ≤ |L n - I M n| + |I M n - J M| + |J M - c| := abs_add_three _ _ _
    _ < ε := by linarith

section Fubini

variable [IsProbabilityMeasure μ]

theorem integrable_one_sub_cos (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable (fun x => 1 - cos (f x)) μ := by
  refine Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_nonneg _)]
  exact one_sub_cos_le_two _

/-- **Layer-cake formula**: `∫ (1 - cos (t min (|x| / a, M))) dμ = ∫₀^M t sin (t u) G(a u) du`. -/
theorem integral_one_sub_cos_min (t : ℝ) {a M : ℝ} (ha : 0 < a) (hM : 0 < M) :
    ∫ x, (1 - cos (t * min (|x| / a) M)) ∂μ =
      ∫ u in Ioo 0 M, t * sin (t * u) * absTail μ (a * u) := by
  set K : ℝ → ℝ → ℝ := fun u x => {x : ℝ | a * u < |x|}.indicator (fun _ => t * sin (t * u)) x
    with hK
  have hK1 : ∀ u, ∫ x, K u x ∂μ = t * sin (t * u) * absTail μ (a * u) := by
    intro u
    simp only [hK]
    rw [integral_indicator_const _ (measurableSet_abs_gt _), smul_eq_mul, absTail, mul_comm]
  have hK2 : ∀ x, ∫ u in Ioo 0 M, K u x = 1 - cos (t * min (|x| / a) M) := by
    intro x
    have hfun : (fun u => K u x) = (Iio (|x| / a)).indicator (fun u => t * sin (t * u)) := by
      funext u
      simp only [hK, indicator, mem_ofPred_eq, mem_Iio, lt_div_iff₀ ha, mul_comm a u]
    rw [hfun, setIntegral_indicator measurableSet_Iio]
    have hI : Ioo 0 M ∩ Iio (|x| / a) = Ioo 0 (min (|x| / a) M) := by
      ext u; simp only [mem_inter_iff, mem_Ioo, mem_Iio, lt_min_iff]; tauto
    have hm : 0 ≤ min (|x| / a) M := le_min (by positivity) hM.le
    rw [hI, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hm,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => -cos (t * u))]
    · simp; ring
    · intro u _
      have := ((hasDerivAt_id' u).const_mul t).cos.neg
      convert this using 1; ring
    · exact (by fun_prop : Continuous fun u : ℝ => t * sin (t * u)).intervalIntegrable _ _
  have hint : Integrable (Function.uncurry K) ((volume.restrict (Ioo 0 M)).prod μ) := by
    have hmeas : Measurable (Function.uncurry K) := by
      have : Function.uncurry K =
          {p : ℝ × ℝ | a * p.1 < |p.2|}.indicator (fun p => t * sin (t * p.1)) := rfl
      rw [this]
      exact (by fun_prop : Measurable fun p : ℝ × ℝ => t * sin (t * p.1)).indicator
        (measurableSet_lt (by fun_prop) (by fun_prop))
    refine Integrable.of_bound hmeas.aestronglyMeasurable |t| (ae_of_all _ fun p => ?_)
    show ‖K p.1 p.2‖ ≤ |t|
    simp only [hK]
    refine (norm_indicator_le_norm_self (fun _ => t * sin (t * p.1)) p.2).trans ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg t) (abs_sin_le_one _)
  calc ∫ x, (1 - cos (t * min (|x| / a) M)) ∂μ = ∫ x, (∫ u in Ioo 0 M, K u x) ∂μ :=
        integral_congr_ae (ae_of_all _ fun x => (hK2 x).symm)
    _ = ∫ u in Ioo 0 M, ∫ x, K u x ∂μ := (integral_integral_swap hint).symm
    _ = _ := by simp_rw [hK1]

/-- **Truncation error**: `|∫ (1 - cos (t x / a)) dμ - ∫ (1 - cos (t min (|x| / a, M))) dμ|
≤ 2 G(a M)`. -/
theorem abs_integral_sub_le (t : ℝ) {a M : ℝ} (ha : 0 < a) :
    |∫ x, (1 - cos (a⁻¹ * t * x)) ∂μ - ∫ x, (1 - cos (t * min (|x| / a) M)) ∂μ| ≤
      2 * absTail μ (a * M) := by
  rw [← integral_sub (integrable_one_sub_cos _ (by fun_prop))
    (integrable_one_sub_cos _ (by fun_prop))]
  have hb : ∀ x, ‖(1 - cos (a⁻¹ * t * x)) - (1 - cos (t * min (|x| / a) M))‖ ≤
      {y : ℝ | a * M < |y|}.indicator (fun _ => (2 : ℝ)) x := by
    intro x
    rw [Real.norm_eq_abs]
    by_cases h : a * M < |x|
    · rw [indicator_of_mem (show x ∈ {y : ℝ | a * M < |y|} from h)]
      rw [abs_le]
      constructor <;> linarith [neg_one_le_cos (a⁻¹ * t * x), cos_le_one (a⁻¹ * t * x),
        neg_one_le_cos (t * min (|x| / a) M), cos_le_one (t * min (|x| / a) M)]
    · rw [indicator_of_notMem (show x ∉ {y : ℝ | a * M < |y|} from h)]
      rw [not_lt] at h
      have hle : |x| / a ≤ M := by rw [div_le_iff₀ ha]; linarith
      rw [min_eq_left hle]
      have : cos (t * (|x| / a)) = cos (a⁻¹ * t * x) := by
        rcases abs_cases x with ⟨hx, -⟩ | ⟨hx, -⟩
        · rw [hx]; ring_nf
        · rw [hx, ← cos_neg]; ring_nf
      rw [this, sub_self, abs_zero]
  calc ‖∫ x, ((1 - cos (a⁻¹ * t * x)) - (1 - cos (t * min (|x| / a) M))) ∂μ‖
      ≤ ∫ x, {y : ℝ | a * M < |y|}.indicator (fun _ => (2 : ℝ)) x ∂μ :=
        norm_integral_le_of_norm_le ((integrable_const 2).indicator (measurableSet_abs_gt _))
          (ae_of_all _ hb)
    _ = 2 * absTail μ (a * M) := by
        rw [integral_indicator_const _ (measurableSet_abs_gt _), smul_eq_mul, mul_comm, absTail]

end Fubini

section Tail

variable {G : ℝ → ℝ} {α : ℝ} {a : ℕ → ℝ}

/-- If `n G(aₙ) → 1` with `G` antitone and positive, then `aₙ → ∞`. -/
theorem tendsto_atTop_of_tendsto_mul (hG : Antitone G) (hpos : ∀ x, 0 < G x)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * G (a n)) atTop (𝓝 1)) : Tendsto a atTop atTop := by
  have hG0 : Tendsto (fun n : ℕ => G (a n)) atTop (𝓝 0) := by
    have h := hna.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp only [Function.comp]
    field_simp
  rw [tendsto_atTop]
  intro K
  filter_upwards [hG0.eventually (gt_mem_nhds (hpos K))] with n hn
  by_contra h
  rw [not_le] at h
  exact absurd (hG h.le) (not_le.2 hn)

/-- `n G(aₙ u) → u^(-α)`. -/
theorem tendsto_mul_comp_mul (hRV : IsRegularlyVarying G (-α)) (hpos : ∀ x, 0 < G x)
    (ha : Tendsto a atTop atTop) (hna : Tendsto (fun n : ℕ => (n : ℝ) * G (a n)) atTop (𝓝 1))
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * G (a n * u)) atTop (𝓝 (u ^ (-α))) := by
  have h := hna.mul ((hRV.2 u hu).comp ha)
  rw [one_mul] at h
  refine h.congr fun n => ?_
  have := (hpos (a n)).ne'
  simp only [Function.comp, mul_comm u (a n)]
  field_simp

/-- **Uniform domination via Potter bounds**: eventually in `n`, for all `u > 0`,
`n G(aₙ u) ≤ K (u^(-α-δ) + u^(-α+δ))`. -/
theorem eventually_mul_comp_mul_le (hα0 : 0 < α) (hG : Antitone G) (hRV : IsRegularlyVarying G (-α))
    (hG1 : ∀ x, G x ≤ 1) (hpos : ∀ x, 0 < G x) (ha : Tendsto a atTop atTop)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * G (a n)) atTop (𝓝 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 < u →
      (n : ℝ) * G (a n * u) ≤ K * (u ^ (-α - δ) + u ^ (-α + δ)) := by
  obtain ⟨x₀, hx₀, -, hP⟩ := hRV.potter_bound (a := 0) (Or.inr (hG.antitoneOn _)) hδ one_lt_two
  have hGx₀ := hpos x₀
  refine ⟨4 + 4 / G x₀, by positivity, ?_⟩
  filter_upwards [ha.eventually (eventually_ge_atTop x₀),
    hna.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))] with n hn hn2 u hu
  have han : 0 < a n := hx₀.trans_le hn
  have hGa := hpos (a n)
  have hp1 := rpow_pos_of_pos hu (-α - δ)
  have hp2 := rpow_pos_of_pos hu (-α + δ)
  have hS : 0 < u ^ (-α - δ) + u ^ (-α + δ) := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hcase : x₀ ≤ a n * u
  · have h := hP (a n) hn (a n * u) hcase
    rw [show a n * u / a n = u by field_simp] at h
    have hmax : max (u ^ (-α + δ)) (u ^ (-α - δ)) ≤ u ^ (-α - δ) + u ^ (-α + δ) :=
      max_le (by linarith) (by linarith)
    have e : (n : ℝ) * G (a n * u) = ((n : ℝ) * G (a n)) * (G (a n * u) / G (a n)) := by
      field_simp
    rw [e]
    have hq : 0 ≤ G (a n * u) / G (a n) := div_nonneg (hpos _).le hGa.le
    calc ((n : ℝ) * G (a n)) * (G (a n * u) / G (a n))
        ≤ 2 * (2 * max (u ^ (-α + δ)) (u ^ (-α - δ))) := mul_le_mul hn2 h hq (by norm_num)
      _ ≤ 4 * (u ^ (-α - δ) + u ^ (-α + δ)) := by linarith
      _ ≤ (4 + 4 / G x₀) * (u ^ (-α - δ) + u ^ (-α + δ)) := by
        gcongr; linarith [div_pos (by norm_num : (0 : ℝ) < 4) hGx₀]
  · rw [not_le] at hcase
    have h := hP (a n) hn x₀ le_rfl
    set q := x₀ / a n with hq
    have hq0 : 0 < q := div_pos hx₀ han
    have hq1 : q ≤ 1 := (div_le_one han).2 hn
    have huq : u < q := by rw [hq, lt_div_iff₀ han]; linarith [mul_comm u (a n)]
    rw [max_eq_right (rpow_le_rpow_of_exponent_ge hq0 hq1 (by linarith))] at h
    have hqu : q ^ (-α - δ) ≤ u ^ (-α - δ) :=
      rpow_le_rpow_of_nonpos hu huq.le (by linarith)
    have h1 : (n : ℝ) * G (a n * u) ≤ n := mul_le_of_le_one_right hn0 (hG1 _)
    have h2 : (n : ℝ) ≤ 2 / G (a n) := by rw [le_div_iff₀ hGa]; exact hn2
    have h3 : 2 / G (a n) = (2 / G x₀) * (G x₀ / G (a n)) := by field_simp
    have h4 : G x₀ / G (a n) ≤ 2 * u ^ (-α - δ) := h.trans (by linarith)
    have h5 : 0 < 4 / G x₀ := div_pos (by norm_num) hGx₀
    calc (n : ℝ) * G (a n * u) ≤ (2 / G x₀) * (2 * u ^ (-α - δ)) := by
          rw [h3] at h2
          exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left h4 (by positivity)))
      _ = (4 / G x₀) * u ^ (-α - δ) := by ring
      _ ≤ (4 + 4 / G x₀) * (u ^ (-α - δ) + u ^ (-α + δ)) := by nlinarith

/-- **Dominated convergence on `(0, M)`**:
`∫₀^M t sin (t u) · n G(aₙ u) du → ∫₀^M t sin (t u) u^(-α) du`. -/
theorem tendsto_setIntegral_sin_mul (hα0 : 0 < α) (hα2 : α < 2) (hG : Antitone G)
    (hRV : IsRegularlyVarying G (-α)) (hG1 : ∀ x, G x ≤ 1) (hpos : ∀ x, 0 < G x)
    (ha : Tendsto a atTop atTop) (hna : Tendsto (fun n : ℕ => (n : ℝ) * G (a n)) atTop (𝓝 1))
    (t : ℝ) {M : ℝ} (hM : 0 < M) :
    Tendsto (fun n : ℕ => ∫ u in Ioo 0 M, t * sin (t * u) * ((n : ℝ) * G (a n * u))) atTop
      (𝓝 (∫ u in Ioo 0 M, t * sin (t * u) * u ^ (-α))) := by
  set δ := (2 - α) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨K, hK0, hK⟩ := eventually_mul_comp_mul_le hα0 hG hRV hG1 hpos ha hna hδ
  have hGm : Measurable G := hG.measurable
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => t ^ 2 * K * (u ^ (1 - α - δ) + u ^ (1 - α + δ))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun n =>
      (by fun_prop : Measurable fun u : ℝ => t * sin (t * u) * ((n : ℝ) * G (a n * u)))
        |>.aestronglyMeasurable
  · filter_upwards [hK] with n hn
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : 0 < u := hu.1
    have hnG : 0 ≤ (n : ℝ) * G (a n * u) := mul_nonneg (Nat.cast_nonneg n) (hpos _).le
    have hsin : |t * sin (t * u)| ≤ t ^ 2 * u := by
      have h0 := abs_sin_le_abs (x := t * u)
      rw [abs_mul, abs_of_pos hu0] at h0
      rw [abs_mul]
      calc |t| * |sin (t * u)| ≤ |t| * (|t| * u) := by gcongr
        _ = t ^ 2 * u := by rw [← sq_abs t]; ring
    have e1 : u ^ (1 - α - δ) = u * u ^ (-α - δ) := by
      rw [show 1 - α - δ = 1 + (-α - δ) by ring, rpow_add hu0, rpow_one]
    have e2 : u ^ (1 - α + δ) = u * u ^ (-α + δ) := by
      rw [show 1 - α + δ = 1 + (-α + δ) by ring, rpow_add hu0, rpow_one]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnG, e1, e2]
    calc |t * sin (t * u)| * ((n : ℝ) * G (a n * u))
        ≤ (t ^ 2 * u) * (K * (u ^ (-α - δ) + u ^ (-α + δ))) :=
          mul_le_mul hsin (hn u hu0) hnG (by positivity)
      _ = _ := by ring
  · have h1 : IntegrableOn (fun u : ℝ => u ^ (1 - α - δ)) (Ioo 0 M) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by rw [hδ_def]; linarith))).mono_set Ioo_subset_Ioc_self
    have h2 : IntegrableOn (fun u : ℝ => u ^ (1 - α + δ)) (Ioo 0 M) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by rw [hδ_def]; linarith))).mono_set Ioo_subset_Ioc_self
    exact (h1.add h2).const_mul _
  · rw [ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun u hu =>
      tendsto_const_nhds.mul (tendsto_mul_comp_mul hRV hpos ha hna hu.1)

end Tail

section Main

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ} {a : ℕ → ℝ}

/-- **Tauberian step** of the generalized CLT ([Feller, §XVII.5, Lemma], [GK, §35]): if
`G(x) = P(|X| > x)` is regularly varying with index `-α`, `0 < α < 2`, and `n G(aₙ) → 1`, then
`n ∫ (1 - cos (t x / aₙ)) dμ(x) → C_α |t| ^ α`. (No symmetry is needed for this step.) -/
theorem tendsto_mul_integral_one_sub_cos (hα0 : 0 < α) (hα2 : α < 2)
    (hRV : IsRegularlyVarying (absTail μ) (-α)) (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, (1 - cos ((a n)⁻¹ * t * x)) ∂μ) atTop
      (𝓝 (stableConst α * |t| ^ α)) := by
  have hG : Antitone (absTail μ) := absTail_antitone
  have hpos : ∀ x, 0 < absTail μ x := IsRegularlyVarying.pos_of_antitone hG hRV.1
  have hatop := tendsto_atTop_of_tendsto_mul hG hpos hna
  refine tendsto_of_approx
    (I := fun M n => ∫ u in Ioo 0 M, t * sin (t * u) * ((n : ℝ) * absTail μ (a n * u)))
    (R := fun M n => 2 * ((n : ℝ) * absTail μ (a n * M)))
    (J := fun M => ∫ u in Ioo 0 M, t * sin (t * u) * u ^ (-α))
    (r := fun M => 2 * M ^ (-α)) ?_ ?_ ?_ ?_ ?_
  · intro M hM n
    have e : ∫ u in Ioo 0 M, t * sin (t * u) * ((n : ℝ) * absTail μ (a n * u)) =
        (n : ℝ) * ∫ x, (1 - cos (t * min (|x| / a n) M)) ∂μ := by
      rw [integral_one_sub_cos_min t (ha n) hM, ← integral_const_mul]
      congr 1; funext u; ring
    rw [e, ← mul_sub, abs_mul, Nat.abs_cast]
    have := abs_integral_sub_le (μ := μ) t (M := M) (ha n)
    calc (n : ℝ) * |∫ x, (1 - cos ((a n)⁻¹ * t * x)) ∂μ -
          ∫ x, (1 - cos (t * min (|x| / a n) M)) ∂μ|
        ≤ (n : ℝ) * (2 * absTail μ (a n * M)) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)
      _ = _ := by ring
  · intro M hM
    exact tendsto_setIntegral_sin_mul hα0 hα2 hG hRV (fun _ => absTail_le_one _) hpos hatop hna
      t hM
  · intro M hM
    exact (tendsto_mul_comp_mul hRV hpos hatop hna hM).const_mul 2
  · refine (tendsto_intervalIntegral_sin_mul_rpow hα0 hα2 t).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [intervalIntegral.integral_of_le hM.le, integral_Ioc_eq_integral_Ioo]
  · simpa using (tendsto_rpow_neg_atTop hα0).const_mul 2

/-- For a symmetric law, `φ(s) = ∫ cos (s x) dμ(x)` is real. -/
theorem charFun_eq_integral_cos (hsymm : μ.map (fun x => -x) = μ) (s : ℝ) :
    charFun μ s = ((∫ x, cos (s * x) ∂μ : ℝ) : ℂ) := by
  have hneg : charFun μ (-s) = charFun μ s := by
    have h := charFun_map_mul (μ := μ) (-1) s
    rw [show (fun x : ℝ => -1 * x) = (fun x => -x) by funext x; ring, hsymm] at h
    rw [h]; ring_nf
  have hreal : (starRingEnd ℂ) (charFun μ s) = charFun μ s := by rw [← charFun_neg, hneg]
  have hint : Integrable (fun x : ℝ => Complex.exp (s * x * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  have hre : (charFun μ s).re = ∫ x, cos (s * x) ∂μ := by
    rw [charFun_apply_real, ← RCLike.re_to_complex, ← integral_re hint]
    congr 1; funext x
    rw [RCLike.re_to_complex, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [← hre]
  exact (Complex.conj_eq_iff_re.1 hreal).symm

/-- `φ_{Sₙ / aₙ}(t) = φ(t / aₙ) ^ n → exp (-C_α |t| ^ α)`. -/
theorem tendsto_charFun_map_convPow (hsymm : μ.map (fun x => -x) = μ) (hα0 : 0 < α)
    (hα2 : α < 2) (hRV : IsRegularlyVarying (absTail μ) (-α)) (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) (t : ℝ) :
    Tendsto (fun n : ℕ => charFun ((convPow μ n).map ((a n)⁻¹ * ·)) t) atTop
      (𝓝 ((Real.exp (-(stableConst α * |t| ^ α)) : ℂ))) := by
  set φ : ℕ → ℝ := fun n => ∫ x, cos ((a n)⁻¹ * t * x) ∂μ with hφ
  have h1 : ∀ n : ℕ, charFun ((convPow μ n).map ((a n)⁻¹ * ·)) t = ((φ n ^ n : ℝ) : ℂ) := by
    intro n
    rw [charFun_map_mul, charFun_convPow, charFun_eq_integral_cos hsymm, Complex.ofReal_pow]
  have h2 : ∀ n : ℕ, ∫ x, (1 - cos ((a n)⁻¹ * t * x)) ∂μ = 1 - φ n := by
    intro n
    rw [integral_sub (integrable_const (1 : ℝ)) ((integrable_const (1 : ℝ)).mono (by fun_prop)
      (ae_of_all _ fun x => by simpa using abs_cos_le_one ((a n)⁻¹ * t * x)))]
    simp [hφ]
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) * (φ n - 1)) atTop (𝓝 (-(stableConst α * |t| ^ α))) := by
    have := (tendsto_mul_integral_one_sub_cos hα0 hα2 hRV ha hna t).neg
    refine this.congr fun n => ?_
    rw [h2]; ring
  have h4 := Real.tendsto_one_add_pow_exp_of_tendsto h3
  simp only [add_sub_cancel] at h4
  simp_rw [h1]
  exact (Complex.continuous_ofReal.tendsto _).comp h4

end Main

end GCLT

open GCLT

/-- **Generalized central limit theorem, symmetric case** ([Feller, Vol. II, §XVII.5,
Theorem 2], [GK, §35, Theorem 2], [EKM, Theorem 2.2.8]). Let `μ` be a symmetric probability
law on `ℝ` whose two-sided tail `G(x) = μ {y | x < |y|}` is regularly varying with index
`-α`, `0 < α < 2`, and let `aₙ > 0` with `n G(aₙ) → 1`. Then the laws of
`(X₁ + ⋯ + Xₙ) / aₙ` (the push-forwards of `μ^{*n}` under `x ↦ aₙ⁻¹ x`) converge weakly to a
probability measure `ν` with characteristic function `exp (-C_α |t| ^ α)`,
`C_α = stableConst α > 0`. -/
theorem tendsto_map_convPow_of_isRegularlyVarying {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (hRV : IsRegularlyVarying (absTail μ) (-α)) {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) :
    ∃ ν : ProbabilityMeasure ℝ, IsSymmStable α (stableConst α) (ν : Measure ℝ) ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν) := by
  have hf : ContinuousAt (fun t : ℝ => ((Real.exp (-(stableConst α * |t| ^ α)) : ℝ) : ℂ)) 0 :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp ((continuous_const.mul
      (continuous_abs.rpow_const fun _ => Or.inr hα0.le)).neg))).continuousAt
  obtain ⟨ν, hν, hlim⟩ := exists_tendsto_of_tendsto_charFun
    (μ := fun n => ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) hf
    (fun t => tendsto_charFun_map_convPow hsymm hα0 hα2 hRV ha hna t)
  exact ⟨ν, ⟨inferInstance, fun t => congrFun hν t⟩, hlim⟩

/-- Characteristic function of a normalized partial sum of i.i.d. random variables
(the analogue of Mathlib's `ProbabilityTheory.charFun_inv_sqrt_mul_sum`). -/
theorem charFun_map_mul_sum {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (c : ℝ) (n : ℕ) (t : ℝ) :
    charFun (P.map (fun ω ↦ c * ∑ k ∈ Finset.range n, X k ω)) t =
      (charFun (P.map (X 0)) (c * t)) ^ n := by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul_comp, (hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ ↦ mX _)]
  · simp [fun i ↦ (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ ↦ mX _

/-- **Generalized central limit theorem for i.i.d. random variables, symmetric case**
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35], [EKM, Theorem 2.2.8]). Let `X₀, X₁, …` be
independent and identically distributed with symmetric law `μ = law (X₀)` whose two-sided tail
`P(|X₀| > x)` is regularly varying with index `-α`, `0 < α < 2`, and let `aₙ > 0` with
`n P(|X₀| > aₙ) → 1`. If `Y` has the symmetric `α`-stable law with characteristic function
`exp (-C_α |t| ^ α)`, then `aₙ⁻¹ (X₀ + ⋯ + X_{n-1}) → Y` in distribution. -/
theorem tendstoInDistribution_inv_mul_sum_of_isRegularlyVarying {Ω Ω' : Type*}
    {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    {ν : Measure ℝ} (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hsymm : (P.map (X 0)).map (fun x => -x) = P.map (X 0)) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < 2) (hRV : IsRegularlyVarying (absTail (P.map (X 0))) (-α)) {a : ℕ → ℝ}
    (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail (P.map (X 0)) (a n)) atTop (𝓝 1))
    (hν : IsSymmStable α (stableConst α) ν) (hY : HasLaw Y ν P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (a n)⁻¹ * ∑ k ∈ Finset.range n, X k ω) atTop Y
      (fun _ ↦ P) P' where
  forall_aemeasurable n :=
    .const_mul (Finset.aemeasurable_fun_sum _ fun _ _ ↦ (hident _).aemeasurable_fst) _
  aemeasurable_limit := hY.aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    simp only [ProbabilityMeasure.coe_mk]
    rw [hY.map_eq, hν.charFun_eq]
    refine (tendsto_charFun_map_convPow hsymm hα0 hα2 hRV ha hna t).congr fun n => ?_
    rw [charFun_map_mul_sum hindep hident, charFun_map_mul, charFun_convPow]

namespace SymmPareto

/-- The symmetrized Pareto law `½ (Pareto(1, α) + law (-X))`, with `P(|X| > x) = x^(-α)` for
`x ≥ 1`. -/
noncomputable def law (α : ℝ) : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • (paretoMeasure 1 α + (paretoMeasure 1 α).map (fun x => -x))

variable {α : ℝ}

theorem pareto_Ioi (hα0 : 0 < α) {x : ℝ} (hx : 1 ≤ x) :
    paretoMeasure 1 α (Ioi x) = ENNReal.ofReal (x ^ (-α)) := by
  have hx0 : 0 < x := one_pos.trans_le hx
  rw [paretoMeasure, withDensity_apply _ measurableSet_Ioi,
    setLIntegral_congr_fun measurableSet_Ioi
      (g := fun y => ENNReal.ofReal (α * y ^ (-(α + 1)))) (fun y hy => by
        rw [paretoPDF_of_le (hx.trans (le_of_lt hy)), one_rpow, mul_one])]
  have hint : IntegrableOn (fun y : ℝ => α * y ^ (-(α + 1))) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx0).const_mul α
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx0,
      show -(α + 1) + 1 = -α by ring]
    field_simp
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun y hy =>
      mul_nonneg hα0.le (rpow_pos_of_pos (hx0.trans hy) _).le

theorem pareto_Iio_one : paretoMeasure 1 α (Iio 1) = 0 := by
  rw [paretoMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_paretoPDF_of_le le_rfl

theorem isProbabilityMeasure (hα0 : 0 < α) : IsProbabilityMeasure (law α) := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα0
  constructor
  rw [law, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

theorem map_neg : (law α).map (fun x => -x) = law α := by
  rw [law, Measure.map_smul, Measure.map_add _ _ measurable_neg,
    Measure.map_map measurable_neg measurable_neg]
  have : ((fun x : ℝ => -x) ∘ fun x => -x) = id := by funext x; simp
  rw [this, Measure.map_id, add_comm]
  exact measurable_neg.aemeasurable

theorem absTail_eq (hα0 : 0 < α) {x : ℝ} (hx : 1 ≤ x) : absTail (law α) x = x ^ (-α) := by
  set S := {y : ℝ | x < |y|}
  have hS := measurableSet_abs_gt x
  have hneg : (fun y : ℝ => -y) ⁻¹' S = S := by ext y; simp [S]
  have hPS : paretoMeasure 1 α S = paretoMeasure 1 α (Ioi x) := by
    have hsub : S ⊆ Ioi x ∪ Iio 1 := fun y (hy : x < |y|) => by
      rcases lt_abs.1 hy with h | h
      · exact Or.inl h
      · exact Or.inr (by simp; linarith)
    refine le_antisymm ?_ (measure_mono fun y (hy : x < y) => (show x < |y| from
      hy.trans_le (le_abs_self y)))
    calc paretoMeasure 1 α S ≤ paretoMeasure 1 α (Ioi x ∪ Iio 1) := measure_mono hsub
      _ ≤ paretoMeasure 1 α (Ioi x) + paretoMeasure 1 α (Iio 1) := measure_union_le _ _
      _ = _ := by rw [pareto_Iio_one, add_zero]
  have : law α S = paretoMeasure 1 α (Ioi x) := by
    rw [law, Measure.smul_apply, Measure.add_apply, Measure.map_apply measurable_neg hS, hneg,
      hPS, smul_eq_mul, ← two_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  rw [absTail, measureReal_def, this, pareto_Ioi hα0 hx,
    ENNReal.toReal_ofReal (rpow_pos_of_pos (one_pos.trans_le hx) _).le]

theorem isRegularlyVarying (hα0 : 0 < α) : IsRegularlyVarying (absTail (law α)) (-α) :=
  (IsRegularlyVarying.rpow_id (-α)).congr (by
    filter_upwards [eventually_ge_atTop 1] with x hx using (absTail_eq hα0 hx).symm)

theorem tendsto_mul_absTail (hα0 : 0 < α) :
    Tendsto (fun n : ℕ => (n : ℝ) * absTail (law α) (((n : ℝ) + 1) ^ α⁻¹)) atTop (𝓝 1) := by
  refine (tendsto_natCast_div_add_atTop (1 : ℝ)).congr fun n => ?_
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [absTail_eq hα0 (one_le_rpow hn (inv_nonneg.2 hα0.le)), ← rpow_mul (by linarith),
    show α⁻¹ * -α = -1 by field_simp, rpow_neg_one, div_eq_mul_inv]

end SymmPareto


/-- **Existence of symmetric `α`-stable laws for `0 < α < 2` with the canonical constant**:
there is a probability measure with characteristic function `exp (-C_α |t| ^ α)`, obtained as
the weak limit of normalized sums of symmetrized Pareto variables. -/
theorem exists_isSymmStable_stableConst {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    ∃ ν : Measure ℝ, IsSymmStable α (stableConst α) ν := by
  have := SymmPareto.isProbabilityMeasure hα0
  obtain ⟨ν, hν, -⟩ := tendsto_map_convPow_of_isRegularlyVarying SymmPareto.map_neg hα0 hα2
    (SymmPareto.isRegularlyVarying hα0)
    (a := fun n : ℕ => ((n : ℝ) + 1) ^ α⁻¹) (fun n => rpow_pos_of_pos (by positivity) _)
    (SymmPareto.tendsto_mul_absTail hα0)
  exact ⟨ν, hν⟩

/-- **Existence of symmetric `α`-stable laws** ([Feller, §XVII.4], [ST, §1.1]): for every
`0 < α ≤ 2` and `c ≥ 0` there is a probability measure on `ℝ` with characteristic function
`t ↦ exp (-c |t| ^ α)`. -/
theorem exists_isSymmStable {α c : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) (hc : 0 ≤ c) :
    ∃ ν : Measure ℝ, IsSymmStable α c ν := by
  rcases hα2.lt_or_eq with hα2 | rfl
  · obtain ⟨ν, hν⟩ := exists_isSymmStable_stableConst hα0 hα2
    have hC := stableConst_pos hα0 hα2
    set r : ℝ := (c / stableConst α) ^ α⁻¹
    have hr : 0 ≤ r := rpow_nonneg (div_nonneg hc hC.le) _
    have e : stableConst α * |r| ^ α = c := by
      rw [abs_of_nonneg hr, rpow_inv_rpow (div_nonneg hc hC.le) hα0.ne']
      field_simp
    exact ⟨_, e ▸ hν.map_mul r⟩
  · refine ⟨gaussianReal 0 (2 * c).toNNReal, ?_⟩
    have h := isSymmStable_gaussianReal (2 * c).toNNReal
    rwa [Real.coe_toNNReal _ (by positivity), mul_div_cancel_left₀ c two_ne_zero] at h

end ExtremeValueTheory
