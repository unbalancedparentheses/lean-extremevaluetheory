/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.DomainOfAttraction
import Mathlib.Basic.Real.Sign
import ExtremeValueTheory.StableLaws.GeneralizedCLT.StableIntegral

/-!
# Characteristic-function asymptotics for the generalized CLT

The analytic core of the generalized central limit theorem for asymmetric tails: truncated and
untruncated one-sided layer-cake formulas, the tails of `μ` and of `law (-X)` under the tail
balance condition, the asymptotics of the sine part of `n (φ(t / aₙ) - 1)` by dominated
convergence with Potter bounds, and their assembly into `n (φ(t / aₙ) - 1 - i t bₙ / (n aₙ)) → ψ(t)`.

## Main results

* `GCLT.integrable_id_of_isRegularlyVarying`: A law whose two-sided tail is regularly varying with
  index `-α`, `α > 1`, has a finite first moment.
* `GCLT.integral_odd_eq_sub`: Splitting an odd integrand into the contributions of the right and
  left tails.

This file is part of the proof in `ExtremeValueTheory.StableLaws.GeneralizedCLT`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), §XVII.5 [Feller].
* B. V. Gnedenko and A. N. Kolmogorov, *Limit Distributions for Sums of Independent Random
  Variables*, Addison-Wesley (1954), §35 [GK].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Theorem 2.2.8 [EKM].
* G. Samorodnitsky and M. S. Taqqu, *Stable Non-Gaussian Random Processes*, Chapman & Hall
  (1994) [ST].
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace ExtremeValueTheory

namespace GCLT

open StableIntegral

section LayerCake

variable {ν : Measure ℝ}

/-- `∫_{(0, w)} F' = F (max w 0) - F 0`. -/
theorem setIntegral_Ioo_eq_sub {F g : ℝ → ℝ} (hF : ∀ u, HasDerivAt F (g u) u)
    (hg : Continuous g) (w : ℝ) : ∫ u in Ioo 0 w, g u = F (max w 0) - F 0 := by
  rcases le_or_gt w 0 with hw | hw
  · rw [Ioo_eq_empty (not_lt.2 hw), Measure.restrict_empty, integral_zero_measure,
      max_eq_right hw, sub_self]
  · rw [max_eq_left hw.le, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hw.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u) (hg.intervalIntegrable _ _)]

theorem setIntegral_indicator_Ioi (S : Set ℝ) (g : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∫ u in S, (Ioi (a * u)).indicator (fun _ => g u) x = ∫ u in S ∩ Iio (x / a), g u := by
  have hfun : (fun u => (Ioi (a * u)).indicator (fun _ => g u) x) = (Iio (x / a)).indicator g := by
    funext u
    simp only [indicator, mem_Ioi, mem_Iio, lt_div_iff₀ ha, mul_comm a u]
  rw [hfun, setIntegral_indicator measurableSet_Iio]

theorem measurable_uncurry_indicator {g : ℝ → ℝ} (hg : Measurable g) (a : ℝ) :
    Measurable (Function.uncurry fun u x : ℝ => (Ioi (a * u)).indicator (fun _ => g u) x) := by
  have : (Function.uncurry fun u x : ℝ => (Ioi (a * u)).indicator (fun _ => g u) x) =
      {p : ℝ × ℝ | a * p.1 < p.2}.indicator (fun p => g p.1) := rfl
  rw [this]
  exact (hg.comp measurable_fst).indicator (measurableSet_lt (by fun_prop) (by fun_prop))

/-- **One-sided layer-cake formula, truncated**: with `R(y) = ν (y, ∞)`,
`∫ (∫_{(0, min (x / a, M))} g) dν(x) = ∫_{(0, M)} g(u) R(a u) du`. -/
theorem integral_setIntegral_Ioo_min [IsFiniteMeasure ν] {g : ℝ → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ u, |g u| ≤ B) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∫ x, (∫ u in Ioo 0 (min (x / a) M), g u) ∂ν =
      ∫ u in Ioo 0 M, g u * ν.real (Ioi (a * u)) := by
  set K : ℝ → ℝ → ℝ := fun u x => (Ioi (a * u)).indicator (fun _ => g u) x with hK
  have hK1 : ∀ u, ∫ x, K u x ∂ν = g u * ν.real (Ioi (a * u)) := by
    intro u
    simp only [hK]
    rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm]
  have hK2 : ∀ x, ∫ u in Ioo 0 M, K u x = ∫ u in Ioo 0 (min (x / a) M), g u := by
    intro x
    rw [hK, setIntegral_indicator_Ioi _ g ha x]
    congr 2
    ext u; simp only [mem_inter_iff, mem_Ioo, mem_Iio, lt_min_iff]; tauto
  have hint : Integrable (Function.uncurry K) ((volume.restrict (Ioo 0 M)).prod ν) := by
    refine Integrable.of_bound (measurable_uncurry_indicator hg a).aestronglyMeasurable B
      (ae_of_all _ fun p => ?_)
    show ‖K p.1 p.2‖ ≤ B
    simp only [hK]
    refine (norm_indicator_le_norm_self (fun _ => g p.1) p.2).trans ?_
    rw [Real.norm_eq_abs]; exact hB _
  calc ∫ x, (∫ u in Ioo 0 (min (x / a) M), g u) ∂ν = ∫ x, (∫ u in Ioo 0 M, K u x) ∂ν :=
        integral_congr_ae (ae_of_all _ fun x => (hK2 x).symm)
    _ = ∫ u in Ioo 0 M, ∫ x, K u x ∂ν := (integral_integral_swap hint).symm
    _ = _ := by simp_rw [hK1]

/-- **One-sided layer-cake formula**: if `ν` has a first moment, then with `R(y) = ν (y, ∞)`,
`∫ (∫_{(0, x / a)} g) dν(x) = ∫_{(0, ∞)} g(u) R(a u) du`. -/
theorem integral_setIntegral_Ioo_eq_Ioi [IsFiniteMeasure ν] (hν : Integrable (fun x => x) ν)
    {g : ℝ → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ u, |g u| ≤ B) {a : ℝ} (ha : 0 < a) :
    ∫ x, (∫ u in Ioo 0 (x / a), g u) ∂ν = ∫ u in Ioi 0, g u * ν.real (Ioi (a * u)) := by
  set K : ℝ → ℝ → ℝ := fun u x => (Ioi (a * u)).indicator (fun _ => g u) x with hK
  have hK1 : ∀ u, ∫ x, K u x ∂ν = g u * ν.real (Ioi (a * u)) := by
    intro u
    simp only [hK]
    rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm]
  have hK2 : ∀ (f : ℝ → ℝ) x, ∫ u in Ioi 0, (Ioi (a * u)).indicator (fun _ => f u) x =
      ∫ u in Ioo 0 (x / a), f u := by
    intro f x
    rw [setIntegral_indicator_Ioi _ f ha x, Ioi_inter_Iio]
  have hmeas := measurable_uncurry_indicator hg a
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hint : Integrable (Function.uncurry K) ((volume.restrict (Ioi 0)).prod ν) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    constructor
    · refine Eventually.of_forall fun x => ?_
      have hfun : (fun u => Function.uncurry K (u, x)) = (Iio (x / a)).indicator g := by
        funext u
        simp only [hK, Function.uncurry_apply_pair, indicator, mem_Ioi, mem_Iio, lt_div_iff₀ ha,
          mul_comm a u]
      rw [hfun, integrable_indicator_iff measurableSet_Iio]
      show Integrable g ((volume.restrict (Ioi 0)).restrict (Iio (x / a)))
      rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
      exact Measure.integrableOn_of_bounded measure_Ioo_lt_top.ne hg.aestronglyMeasurable
        (ae_of_all _ fun u => (Real.norm_eq_abs _).trans_le (hB u))
    · refine (hν.norm.const_mul (B / a)).mono' ?_ (ae_of_all _ fun x => ?_)
      · exact (hmeas.norm.stronglyMeasurable.integral_prod_left'
          (μ := volume.restrict (Ioi 0))).aestronglyMeasurable
      · show ‖∫ u in Ioi 0, ‖K u x‖‖ ≤ B / a * ‖x‖
        simp only [hK, norm_indicator_eq_indicator_norm]
        have h2 := hK2 (fun u => ‖g u‖) x
        rw [h2]
        refine (norm_setIntegral_le_of_norm_le_const (C := B) measure_Ioo_lt_top fun u _ => ?_).trans ?_
        · rw [norm_norm, Real.norm_eq_abs]; exact hB u
        · rw [Real.volume_real_Ioo, sub_zero, Real.norm_eq_abs]
          have : max (x / a) 0 ≤ |x| / a :=
            max_le (div_le_div_of_nonneg_right (le_abs_self x) ha.le) (by positivity)
          calc B * max (x / a) 0 ≤ B * (|x| / a) := mul_le_mul_of_nonneg_left this hB0
            _ = B / a * |x| := by ring
  calc ∫ x, (∫ u in Ioo 0 (x / a), g u) ∂ν = ∫ x, (∫ u in Ioi 0, K u x) ∂ν :=
        integral_congr_ae (ae_of_all _ fun x => (hK2 g x).symm)
    _ = ∫ u in Ioi 0, ∫ x, K u x ∂ν := (integral_integral_swap hint).symm
    _ = _ := by simp_rw [hK1]

/-- **Truncation error**: for `|F| ≤ 1`, replacing `max (x / a) 0` by `max (min (x / a) M) 0`
costs at most `2 ν (a M, ∞)`. -/
theorem abs_integral_sub_min_le [IsFiniteMeasure ν] {F : ℝ → ℝ} (hF : Continuous F)
    (hFb : ∀ v, |F v| ≤ 1) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    |∫ x, F (max (x / a) 0) ∂ν - ∫ x, F (max (min (x / a) M) 0) ∂ν| ≤
      2 * ν.real (Ioi (a * M)) := by
  have hi : ∀ f : ℝ → ℝ, Continuous f → Integrable (fun x => F (f x)) ν := fun f hf =>
    Integrable.of_bound (hF.comp hf).aestronglyMeasurable 1
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hFb _))
  rw [← integral_sub (hi _ (by fun_prop)) (hi _ (by fun_prop))]
  have hb : ∀ x, ‖F (max (x / a) 0) - F (max (min (x / a) M) 0)‖ ≤
      (Ioi (a * M)).indicator (fun _ => (2 : ℝ)) x := by
    intro x
    rw [Real.norm_eq_abs]
    by_cases h : a * M < x
    · rw [indicator_of_mem (show x ∈ Ioi (a * M) from h)]
      obtain ⟨h1, h2⟩ := abs_le.1 (hFb (max (x / a) 0))
      obtain ⟨h3, h4⟩ := abs_le.1 (hFb (max (min (x / a) M) 0))
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · rw [indicator_of_notMem (show x ∉ Ioi (a * M) from h)]
      rw [not_lt] at h
      have hle : x / a ≤ M := by rw [div_le_iff₀ ha]; linarith
      rw [min_eq_left hle, sub_self, abs_zero]
  calc ‖∫ x, (F (max (x / a) 0) - F (max (min (x / a) M) 0)) ∂ν‖
      ≤ ∫ x, (Ioi (a * M)).indicator (fun _ => (2 : ℝ)) x ∂ν :=
        norm_integral_le_of_norm_le ((integrable_const 2).indicator measurableSet_Ioi)
          (ae_of_all _ hb)
    _ = 2 * ν.real (Ioi (a * M)) := by
        rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm]

/-- Dominated convergence for `∫_S g(u) hₙ(u) du` when `hₙ(u) → c u^(-α)` with a uniform
Potter-type bound `|hₙ(u)| ≤ K (u^(-α-δ) + u^(-α+δ))`. -/
theorem tendsto_setIntegral_mul_of_le {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    {h : ℕ → ℝ → ℝ} (hhm : ∀ n, Measurable (h n)) {g : ℝ → ℝ} (hg : Measurable g)
    {c α δ K : ℝ} (hlim : ∀ u, 0 < u → Tendsto (fun n => h n u) atTop (𝓝 (c * u ^ (-α))))
    (hbd : ∀ᶠ n in atTop, ∀ u, 0 < u → |h n u| ≤ K * (u ^ (-α - δ) + u ^ (-α + δ)))
    (hint : IntegrableOn (fun u => |g u| * (u ^ (-α - δ) + u ^ (-α + δ))) S) :
    Tendsto (fun n => ∫ u in S, g u * h n u) atTop (𝓝 (c * ∫ u in S, g u * u ^ (-α))) := by
  rw [← integral_const_mul]
  have e : (fun u => c * (g u * u ^ (-α))) = fun u => g u * (c * u ^ (-α)) := by
    funext u; ring
  rw [e]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => K * (|g u| * (u ^ (-α - δ) + u ^ (-α + δ)))) ?_ ?_ (hint.const_mul K) ?_
  · exact Eventually.of_forall fun n => (hg.mul (hhm n)).aestronglyMeasurable
  · filter_upwards [hbd] with n hn
    rw [ae_restrict_iff' hS]
    refine Eventually.of_forall fun u hu => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |g u| * |h n u| ≤ |g u| * (K * (u ^ (-α - δ) + u ^ (-α + δ))) :=
          mul_le_mul_of_nonneg_left (hn u (hS0 hu)) (abs_nonneg _)
      _ = _ := by ring
  · rw [ae_restrict_iff' hS]
    exact Eventually.of_forall fun u hu => tendsto_const_nhds.mul (hlim u (hS0 hu))

end LayerCake

section Tails

variable {μ : Measure ℝ}

theorem measureReal_Ioi_le_absTail [IsFiniteMeasure μ] (x : ℝ) :
    μ.real (Ioi x) ≤ absTail μ x :=
  measureReal_mono (fun y (hy : x < y) => (show x < |y| from hy.trans_le (le_abs_self y)))

theorem measurable_measureReal_Ioi [IsFiniteMeasure μ] : Measurable fun x => μ.real (Ioi x) :=
  Antitone.measurable fun _ _ hxy => measureReal_mono (Ioi_subset_Ioi hxy)

theorem absTail_map_neg : absTail (μ.map (fun x => -x)) = absTail μ := by
  funext x
  rw [absTail, absTail, measureReal_def, measureReal_def,
    Measure.map_apply measurable_neg (measurableSet_abs_gt x)]
  congr 2; ext y; simp

theorem measureReal_Ioi_map_neg (x : ℝ) :
    (μ.map (fun x => -x)).real (Ioi x) = μ.real (Iio (-x)) := by
  rw [measureReal_def, measureReal_def, Measure.map_apply measurable_neg measurableSet_Ioi]
  congr 2; ext y; simp

theorem absTail_eq_add [IsFiniteMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    absTail μ x = μ.real (Ioi x) + μ.real (Iio (-x)) := by
  have hset : {y : ℝ | x < |y|} = Ioi x ∪ Iio (-x) := by
    ext y; simp only [mem_ofPred_eq, mem_union, mem_Ioi, mem_Iio, lt_abs, lt_neg]
  rw [absTail, hset, measureReal_union _ measurableSet_Iio]
  rw [Set.disjoint_left]
  intro y (h1 : x < y) (h2 : y < -x)
  linarith

variable [IsProbabilityMeasure μ] {α c : ℝ} {a : ℕ → ℝ}

/-- One-sided tail balance: `n ν (aₙ u, ∞) → c u^(-α)`. -/
theorem tendsto_mul_measureReal_Ioi (hRV : IsRegularlyVarying (absTail μ) (-α))
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1))
    (hc : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 c)) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * μ.real (Ioi (a n * u))) atTop (𝓝 (c * u ^ (-α))) := by
  have hG : Antitone (absTail μ) := absTail_antitone
  have hpos : ∀ x, 0 < absTail μ x := IsRegularlyVarying.pos_of_antitone hG hRV.1
  have hatop := tendsto_atTop_of_tendsto_mul hG hpos hna
  have h3 : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n * u) *
      (μ.real (Ioi (a n * u)) / absTail μ (a n * u))) atTop (𝓝 (u ^ (-α) * c)) :=
    (tendsto_mul_comp_mul hRV hpos hatop hna hu).mul (hc.comp (hatop.atTop_mul_const hu))
  rw [mul_comm (u ^ (-α)) c] at h3
  refine h3.congr fun n => ?_
  have := (hpos (a n * u)).ne'
  field_simp

theorem eventually_abs_mul_measureReal_Ioi_le (hα0 : 0 < α)
    (hRV : IsRegularlyVarying (absTail μ) (-α))
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 0 < u →
      |(n : ℝ) * μ.real (Ioi (a n * u))| ≤ K * (u ^ (-α - δ) + u ^ (-α + δ)) := by
  have hG : Antitone (absTail μ) := absTail_antitone
  have hpos : ∀ x, 0 < absTail μ x := IsRegularlyVarying.pos_of_antitone hG hRV.1
  have hatop := tendsto_atTop_of_tendsto_mul hG hpos hna
  obtain ⟨K, -, hK⟩ :=
    eventually_mul_comp_mul_le hα0 hG hRV (fun _ => absTail_le_one _) hpos hatop hna hδ
  refine ⟨K, hK.mono fun n hn u hu => ?_⟩
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg)]
  exact (mul_le_mul_of_nonneg_left (measureReal_Ioi_le_absTail _) (Nat.cast_nonneg n)).trans
    (hn u hu)

/-- The left tail balance follows from the right one: `P(X < -x) / P(|X| > x) → 1 - p`. -/
theorem tendsto_measureReal_Ioi_map_neg_div
    (hRV : IsRegularlyVarying (absTail μ) (-α)) {p : ℝ}
    (hp : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p)) :
    Tendsto (fun x => (μ.map (fun x => -x)).real (Ioi x) / absTail (μ.map (fun x => -x)) x)
      atTop (𝓝 (1 - p)) := by
  have hpos : ∀ x, 0 < absTail μ x :=
    IsRegularlyVarying.pos_of_antitone absTail_antitone hRV.1
  refine (tendsto_const_nhds.sub hp).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [absTail_map_neg, measureReal_Ioi_map_neg, absTail_eq_add hx]
  have := (hpos x).ne'
  rw [absTail_eq_add hx] at this
  field_simp
  ring

/-- A law whose two-sided tail is regularly varying with index `-α`, `α > 1`, has a finite
first moment. -/
theorem integrable_id_of_isRegularlyVarying (hα1 : 1 < α)
    (hRV : IsRegularlyVarying (absTail μ) (-α)) : Integrable (fun x => x) μ := by
  have hi := IsRegularlyVarying.integrableOn_Ioi absTail_antitone hRV hα1 0
  refine ⟨aestronglyMeasurable_id, ?_⟩
  have h1 : ∫⁻ x, ‖x‖ₑ ∂μ = ∫⁻ t in Ioi 0, ‖absTail μ t‖ₑ := by
    simp_rw [Real.enorm_eq_ofReal_abs]
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ fun x => abs_nonneg x) (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [absTail, abs_of_nonneg measureReal_nonneg, ofReal_measureReal (measure_ne_top _ _)]
  rw [HasFiniteIntegral, h1]
  exact hi.2

/-- For `α < 2`, `x² P(|X| > x) → ∞`. -/
theorem tendsto_sq_mul_absTail (hα2 : α < 2) (hRV : IsRegularlyVarying (absTail μ) (-α)) :
    Tendsto (fun x => x ^ 2 * absTail μ x) atTop atTop := by
  set δ := (2 - α) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨x₀, hx₀, hpos, hP⟩ :=
    hRV.potter_bound (a := 0) (Or.inr (absTail_antitone.antitoneOn _)) hδ one_lt_two
  have hG0 := hpos x₀ le_rfl
  have hlim : Tendsto (fun x : ℝ => absTail μ x₀ * x₀ ^ (α + δ) / 2 * x ^ (2 - α - δ))
      atTop atTop :=
    (tendsto_rpow_atTop (by rw [hδ_def]; linarith)).const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [eventually_ge_atTop x₀] with x hx
  have hx0 : 0 < x := hx₀.trans_le hx
  have h := hP x hx x₀ le_rfl
  have hq0 : 0 < x₀ / x := div_pos hx₀ hx0
  have hq1 : x₀ / x ≤ 1 := (div_le_one hx0).2 hx
  rw [max_eq_right (rpow_le_rpow_of_exponent_ge hq0 hq1 (by linarith)),
    div_le_iff₀ (hpos x hx)] at h
  have e : (x₀ / x) ^ (-α - δ) * x₀ ^ (α + δ) = x ^ (α + δ) := by
    rw [show -α - δ = -(α + δ) by ring, rpow_neg hq0.le, div_rpow hx₀.le hx0.le, inv_div,
      div_mul_cancel₀ _ (rpow_pos_of_pos hx₀ _).ne']
  calc absTail μ x₀ * x₀ ^ (α + δ) / 2 * x ^ (2 - α - δ)
      ≤ (2 * (x₀ / x) ^ (-α - δ) * absTail μ x) * x₀ ^ (α + δ) / 2 * x ^ (2 - α - δ) := by
        gcongr
    _ = ((x₀ / x) ^ (-α - δ) * x₀ ^ (α + δ)) * x ^ (2 - α - δ) * absTail μ x := by ring
    _ = x ^ 2 * absTail μ x := by
        rw [e, ← rpow_add hx0, show α + δ + (2 - α - δ) = 2 by ring, rpow_two]

/-- For `α < 2` and `n P(|X| > aₙ) → 1`, `n / aₙ² → 0`. -/
theorem tendsto_mul_inv_sq (hα2 : α < 2) (hRV : IsRegularlyVarying (absTail μ) (-α))
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) / a n ^ 2) atTop (𝓝 0) := by
  have hG : Antitone (absTail μ) := absTail_antitone
  have hpos : ∀ x, 0 < absTail μ x := IsRegularlyVarying.pos_of_antitone hG hRV.1
  have hatop := tendsto_atTop_of_tendsto_mul hG hpos hna
  have h := hna.div_atTop ((tendsto_sq_mul_absTail hα2 hRV).comp hatop)
  refine h.congr fun n => ?_
  have := (hpos (a n)).ne'
  simp only [Function.comp]
  rcases eq_or_ne (a n) 0 with h0 | h0
  · simp [h0]
  · field_simp

end Tails

section Imag

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α c : ℝ} {a : ℕ → ℝ}

theorem hasDerivAt_sin_mul (t u : ℝ) :
    HasDerivAt (fun v => sin (t * v)) (t * cos (t * u)) u := by
  have := ((hasDerivAt_id' u).const_mul t).sin
  convert this using 1; ring

theorem hasDerivAt_sin_mul_sub (t u : ℝ) :
    HasDerivAt (fun v => sin (t * v) - t * v) (t * cos (t * u) - t) u := by
  have := (hasDerivAt_sin_mul t u).sub ((hasDerivAt_id' u).const_mul t)
  convert this using 1; ring

/-- **The sine part, `0 < α < 1`**: if `P(X > x) / P(|X| > x) → c`, then
`n ∫ sin (t max (x / aₙ, 0)) dμ → c E_α sign t |t|^α`. -/
theorem tendsto_mul_integral_sin_max (hα0 : 0 < α) (hα1 : α < 1)
    (hRV : IsRegularlyVarying (absTail μ) (-α)) (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1))
    (hc : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 c)) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * ∫ x, sin (t * max (x / a n) 0) ∂μ) atTop
      (𝓝 (c * (stableSkewConst α * Real.sign t * |t| ^ α))) := by
  set δ := (1 - α) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨K, hK⟩ := eventually_abs_mul_measureReal_Ioi_le hα0 hRV hna hδ
  have hlay : ∀ w : ℝ, ∫ u in Ioo 0 w, t * cos (t * u) = sin (t * max w 0) := fun w => by
    rw [setIntegral_Ioo_eq_sub (hasDerivAt_sin_mul t) (by fun_prop) w]; simp
  have hgB : ∀ u : ℝ, |t * cos (t * u)| ≤ |t| := fun u => by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  refine tendsto_of_approx
    (I := fun M n => ∫ u in Ioo 0 M, t * cos (t * u) * ((n : ℝ) * μ.real (Ioi (a n * u))))
    (R := fun M n => 2 * ((n : ℝ) * μ.real (Ioi (a n * M))))
    (J := fun M => c * ∫ u in Ioo 0 M, t * cos (t * u) * u ^ (-α))
    (r := fun M => 2 * (c * M ^ (-α))) ?_ ?_ ?_ ?_ ?_
  · intro M _ n
    have e1 := integral_setIntegral_Ioo_min (ν := μ) (g := fun u => t * cos (t * u))
      (by fun_prop) hgB (ha n) M
    simp only [hlay] at e1
    have e : ∫ u in Ioo 0 M, t * cos (t * u) * ((n : ℝ) * μ.real (Ioi (a n * u))) =
        (n : ℝ) * ∫ x, sin (t * max (min (x / a n) M) 0) ∂μ := by
      rw [e1, ← integral_const_mul]; congr 1; funext u; ring
    rw [e, ← mul_sub, abs_mul, Nat.abs_cast]
    have := abs_integral_sub_min_le (ν := μ) (F := fun v => sin (t * v)) (by fun_prop)
      (fun v => abs_sin_le_one _) (ha n) M
    calc (n : ℝ) * |∫ x, sin (t * max (x / a n) 0) ∂μ -
          ∫ x, sin (t * max (min (x / a n) M) 0) ∂μ|
        ≤ (n : ℝ) * (2 * μ.real (Ioi (a n * M))) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)
      _ = _ := by ring
  · intro M hM
    have h1 : IntegrableOn (fun u : ℝ => u ^ (-α - δ)) (Ioo 0 M) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by rw [hδ_def]; linarith))).mono_set
          Ioo_subset_Ioc_self
    have h2 : IntegrableOn (fun u : ℝ => u ^ (-α + δ)) (Ioo 0 M) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by rw [hδ_def]; linarith))).mono_set
          Ioo_subset_Ioc_self
    refine tendsto_setIntegral_mul_of_le measurableSet_Ioo (fun u hu => hu.1)
      (fun n => (measurable_measureReal_Ioi.comp (measurable_const.mul measurable_id)).const_mul _)
      (by fun_prop) (fun u hu => tendsto_mul_measureReal_Ioi hRV hna hc hu) hK ?_
    refine ((h1.add h2).const_mul |t|).mono' (by fun_prop) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun u hu => ?_
    have hp : 0 ≤ u ^ (-α - δ) + u ^ (-α + δ) :=
      add_nonneg (rpow_nonneg hu.1.le _) (rpow_nonneg hu.1.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hp)]
    exact mul_le_mul_of_nonneg_right (hgB u) hp
  · intro M hM
    exact (tendsto_mul_measureReal_Ioi hRV hna hc hM).const_mul 2
  · refine ((tendsto_intervalIntegral_cos_mul_rpow hα0 hα1 t).const_mul c).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    rw [intervalIntegral.integral_of_le hM.le, integral_Ioc_eq_integral_Ioo]
  · simpa using ((tendsto_rpow_neg_atTop hα0).const_mul c).const_mul 2

/-- **The sine part, `1 < α < 2`**: if `P(X > x) / P(|X| > x) → c`, then
`n ∫ (sin (t v) - t v)|_{v = max (x / aₙ, 0)} dμ → c E_α sign t |t|^α`. -/
theorem tendsto_mul_integral_sin_sub_max (hα1 : 1 < α) (hα2 : α < 2)
    (hRV : IsRegularlyVarying (absTail μ) (-α)) (ha : ∀ n, 0 < a n)
    (hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 1))
    (hc : Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 c)) (t : ℝ) :
    Tendsto (fun n : ℕ =>
        (n : ℝ) * ∫ x, (sin (t * max (x / a n) 0) - t * max (x / a n) 0) ∂μ) atTop
      (𝓝 (c * (stableSkewConst α * Real.sign t * |t| ^ α))) := by
  have hα0 : 0 < α := by linarith
  have hν := integrable_id_of_isRegularlyVarying hα1 hRV
  set δ := (α - 1) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨K, hK⟩ := eventually_abs_mul_measureReal_Ioi_le hα0 hRV hna hδ
  have hlay : ∀ w : ℝ, ∫ u in Ioo 0 w, (t * cos (t * u) - t) = sin (t * max w 0) - t * max w 0 :=
    fun w => by rw [setIntegral_Ioo_eq_sub (hasDerivAt_sin_mul_sub t) (by fun_prop) w]; simp
  have hgabs : ∀ u : ℝ, |t * cos (t * u) - t| = |t| * (1 - cos (t * u)) := fun u => by
    rw [show t * cos (t * u) - t = -t * (1 - cos (t * u)) by ring, abs_mul, abs_neg,
      abs_of_nonneg (one_sub_cos_nonneg _)]
  have hgB : ∀ u : ℝ, |t * cos (t * u) - t| ≤ 2 * |t| := fun u => by
    rw [hgabs, mul_comm 2]
    exact mul_le_mul_of_nonneg_left (one_sub_cos_le_two _) (abs_nonneg _)
  have e : ∀ n : ℕ, (n : ℝ) * ∫ x, (sin (t * max (x / a n) 0) - t * max (x / a n) 0) ∂μ =
      ∫ u in Ioi 0, (t * cos (t * u) - t) * ((n : ℝ) * μ.real (Ioi (a n * u))) := by
    intro n
    have e1 := integral_setIntegral_Ioo_eq_Ioi hν (g := fun u => t * cos (t * u) - t)
      (by fun_prop) hgB (ha n)
    simp only [hlay] at e1
    rw [e1, ← integral_const_mul]; congr 1; funext u; ring
  simp_rw [e]
  have hint : IntegrableOn (fun u => |t * cos (t * u) - t| * (u ^ (-α - δ) + u ^ (-α + δ)))
      (Ioi 0) := by
    have i1 := integrableOn_one_sub_cos_mul_rpow (α := α + δ - 1) (by rw [hδ_def]; linarith)
      (by rw [hδ_def]; linarith) t
    have i2 := integrableOn_one_sub_cos_mul_rpow (α := α - δ - 1) (by rw [hδ_def]; linarith)
      (by rw [hδ_def]; linarith) t
    rw [show -(α + δ - 1) - 1 = -α - δ by ring] at i1
    rw [show -(α - δ - 1) - 1 = -α + δ by ring] at i2
    refine IntegrableOn.congr_fun ((i1.add i2).const_mul |t|) (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]
    rw [hgabs]; ring
  have hlim := tendsto_setIntegral_mul_of_le measurableSet_Ioi (fun u hu => hu)
    (h := fun n u => (n : ℝ) * μ.real (Ioi (a n * u)))
    (fun n => (measurable_measureReal_Ioi.comp (measurable_const.mul measurable_id)).const_mul _)
    (g := fun u => t * cos (t * u) - t) (by fun_prop)
    (fun u hu => tendsto_mul_measureReal_Ioi hRV hna hc hu) hK hint
  have hval : ∫ u in Ioi 0, (t * cos (t * u) - t) * u ^ (-α) =
      stableSkewConst α * Real.sign t * |t| ^ α := by
    rw [← neg_mul_integral_one_sub_cos_mul_rpow hα1 t, ← integral_const_mul, ← integral_neg]
    congr 1; funext u; ring
  rw [hval] at hlim
  exact hlim

end Imag

section Assembly

variable {μ : Measure ℝ}

theorem eq_sub_of_odd {F : ℝ → ℝ} (hodd : ∀ v, F (-v) = -F v) (v : ℝ) :
    F v = F (max v 0) - F (max (-v) 0) := by
  have h0 : F 0 = 0 := by have := hodd 0; rw [neg_zero] at this; linarith
  rcases le_total 0 v with hv | hv
  · rw [max_eq_left hv, max_eq_right (neg_nonpos.2 hv), h0, sub_zero]
  · rw [max_eq_right hv, max_eq_left (neg_nonneg.2 hv), h0, hodd, zero_sub, neg_neg]

/-- Splitting an odd integrand into the contributions of the right and left tails. -/
theorem integral_odd_eq_sub [IsFiniteMeasure μ] {F : ℝ → ℝ} (hF : Continuous F)
    (hodd : ∀ v, F (-v) = -F v) (a : ℝ)
    (h1 : Integrable (fun x => F (max (x / a) 0)) μ)
    (h2 : Integrable (fun x => F (max (-x / a) 0)) μ) :
    ∫ x, F (x / a) ∂μ =
      ∫ x, F (max (x / a) 0) ∂μ - ∫ x, F (max (x / a) 0) ∂(μ.map (fun x => -x)) := by
  rw [integral_map measurable_neg.aemeasurable
    (by fun_prop : Continuous fun x => F (max (x / a) 0)).aestronglyMeasurable,
    ← integral_sub h1 h2]
  congr 1; funext x
  rw [eq_sub_of_odd hodd (x / a), neg_div]

/-- `φ(s) = ∫ cos (s x) dμ + i ∫ sin (s x) dμ`. -/
theorem charFun_eq_integral_cos_add_sin [IsFiniteMeasure μ] (s : ℝ) :
    charFun μ s = ((∫ x, cos (s * x) ∂μ : ℝ) : ℂ) + ((∫ x, sin (s * x) ∂μ : ℝ) : ℂ) * Complex.I := by
  rw [charFun_apply_real]
  have h : ∀ x : ℝ, Complex.exp (s * x * Complex.I) =
      ((cos (s * x) : ℝ) : ℂ) + ((sin (s * x) : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [← Complex.ofReal_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp_rw [h]
  have hc : Integrable (fun x => cos (s * x)) μ := Integrable.of_bound (by fun_prop) 1
    (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (abs_cos_le_one _))
  have hs : Integrable (fun x => sin (s * x)) μ := Integrable.of_bound (by fun_prop) 1
    (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (abs_sin_le_one _))
  rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal]

theorem integral_one_sub_cos_eq [IsProbabilityMeasure μ] (s : ℝ) :
    ∫ x, (1 - cos (s * x)) ∂μ = 1 - ∫ x, cos (s * x) ∂μ := by
  rw [integral_sub (integrable_const (1 : ℝ)) (Integrable.of_bound (by fun_prop) 1
    (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (abs_cos_le_one _)))]
  simp

theorem tendsto_ofReal_add_mul_I {A B : ℕ → ℝ} {x y : ℝ} (hA : Tendsto A atTop (𝓝 x))
    (hB : Tendsto B atTop (𝓝 y)) :
    Tendsto (fun n => ((A n : ℝ) : ℂ) + ((B n : ℝ) : ℂ) * Complex.I) atTop
      (𝓝 ((x : ℂ) + (y : ℂ) * Complex.I)) :=
  ((Complex.continuous_ofReal.tendsto _).comp hA).add
    (((Complex.continuous_ofReal.tendsto _).comp hB).mul_const _)

theorem abs_sin_mul_sub_le (t w : ℝ) : |sin (t * w) - t * w| ≤ 2 * |t| * |w| := by
  have h1 := abs_le.1 ((abs_sin_le_abs (x := t * w)).trans_eq (abs_mul t w))
  have h2 := abs_le.1 ((le_refl |t * w|).trans_eq (abs_mul t w))
  rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end Assembly

end GCLT

end ExtremeValueTheory
