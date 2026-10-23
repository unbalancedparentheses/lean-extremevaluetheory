import ExtremeValueTheory

/-!
# Non-vacuity: classical extreme value theory

Each test builds a concrete object satisfying every hypothesis of a headline theorem (README,
"Headline theorems": limits of maxima, domains of attraction, peaks over threshold, regular
variation, stable laws, heavy tails) and applies the theorem to it.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Test.NonVacuity.Classical

open CumulativeDistributionFunction ExtremeValueTheory Subexp

/-! ### Limits of maxima -/

/-- The standard Gumbel law is an extreme value law *because* it is the limit of normalized maxima
of iid standard exponential variables (`isInMDAGumbel_standardExponentialCDF`), not by its own
max-stability. -/
private theorem gumbel_isExtremeValueDistr_of_exponential_maxima :
    standardGumbelCDF.IsExtremeValueDistr := by
  obtain ⟨As, hAs⟩ := isInMDAGumbel_standardExponentialCDF
  exact ⟨isExtremeValueDistr_standardGumbelCDF.1, standardExponentialCDF, As, fun x _ => hAs x⟩

/-- Exercises `CumulativeDistributionFunction.IsExtremeValueDistr.classification`
(Fisher–Tippett–Gnedenko) on the Gumbel limit of exponential maxima. -/
theorem test_nonvacuous_classification :
    (∃ A : AffineIncrEquiv, A • standardGumbelCDF = standardGumbelCDF) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ), A • standardGumbelCDF = standardFrechetCDF hξ) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ), A • standardGumbelCDF = standardWeibullCDF hξ) :=
  gumbel_isExtremeValueDistr_of_exponential_maxima.classification

/-- Exercises `isMaxStable_iff_isExtremeValueDistr` (both directions) on the Gumbel limit of
exponential maxima. -/
theorem test_nonvacuous_isMaxStable_iff_isExtremeValueDistr :
    standardGumbelCDF.IsMaxStable ∧ standardGumbelCDF.IsExtremeValueDistr := by
  have h := (isMaxStable_iff_isExtremeValueDistr standardGumbelCDF).2
    gumbel_isExtremeValueDistr_of_exponential_maxima
  exact ⟨h, (isMaxStable_iff_isExtremeValueDistr standardGumbelCDF).1 h⟩

/-! ### Domains of attraction -/

/-- Exercises `isInMDAFrechet_iff` on the Pareto law `1 - x^{-2}`: the tail is regularly varying
with index `-2`. -/
theorem test_nonvacuous_isInMDAFrechet_iff :
    IsRegularlyVarying (fun x ↦ 1 - paretoCDF (two_pos : (0 : ℝ) < 2) x) (-2) :=
  (isInMDAFrechet_iff _ two_pos).1 (isInMDAFrechet_paretoCDF two_pos)

/-- Exercises `isInMDAWeibull_iff` on the uniform law on `[0, 1]` (`powerCDF` with `α = 1`):
finite endpoint and regularly varying tail at the endpoint. -/
theorem test_nonvacuous_isInMDAWeibull_iff :
    ∃ xF : ℝ, powerCDF one_pos xF = 1 ∧ (∀ x < xF, powerCDF one_pos x < 1) ∧
      IsRegularlyVarying (fun t ↦ 1 - powerCDF one_pos (xF - t⁻¹)) (-1) :=
  (isInMDAWeibull_iff _ one_pos).1 (isInMDAWeibull_powerCDF one_pos)

/-- Exercises `isInMDAGumbel_iff` on the standard exponential law: an auxiliary function exists. -/
theorem test_nonvacuous_isInMDAGumbel_iff :
    ((∀ x, standardExponentialCDF x < 1) ∧ ∃ f : ℝ → ℝ, (∀ᶠ t in atTop, 0 < f t) ∧
        ∀ x, Tendsto (fun t ↦ (1 - standardExponentialCDF (t + x * f t)) /
          (1 - standardExponentialCDF t)) atTop (𝓝 (Real.exp (-x)))) ∨
      ∃ xF : ℝ, (∀ x < xF, standardExponentialCDF x < 1) ∧ standardExponentialCDF xF = 1 ∧
        ∃ f : ℝ → ℝ, (∀ᶠ t in 𝓝[<] xF, 0 < f t) ∧
        ∀ x, Tendsto (fun t ↦ (1 - standardExponentialCDF (t + x * f t)) /
          (1 - standardExponentialCDF t)) (𝓝[<] xF) (𝓝 (Real.exp (-x))) :=
  (isInMDAGumbel_iff _).1 isInMDAGumbel_standardExponentialCDF

/-- Exercises `isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile` on the standard
exponential law (`γ = 0`) and on the Pareto law with `γ = 1/2`. -/
theorem test_nonvacuous_isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile :
    (∃ a : ℝ → ℝ, IsExtendedRegularlyVarying standardExponentialCDF.tailQuantile 0 a) ∧
      ∃ a : ℝ → ℝ, IsExtendedRegularlyVarying (paretoCDF (two_pos : (0 : ℝ) < 2)).tailQuantile
        (1 / 2) a :=
  ⟨(isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile _ 0).1
      isInMDAGEV_standardExponentialCDF,
    (isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile _ (1 / 2)).1
      (isInMDAGEV_paretoCDF two_pos)⟩

/-! ### Peaks over threshold -/

/-- Exercises `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival`
(Pickands–Balkema–de Haan) on the standard exponential law (`ξ = 0`) and the Pareto law
(`ξ = 1/2`). -/
theorem test_nonvacuous_isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival :
    (∃ β : ℝ → ℝ, (∀ᶠ u in standardExponentialCDF.upperEndpointFilter, 0 < β u) ∧
      TendstoUniformlyOn
        (fun u x ↦ excessSurvival (fun y ↦ 1 - standardExponentialCDF y) u (β u * x))
        (gpdSurvival' 0 1) standardExponentialCDF.upperEndpointFilter (Ici 0)) ∧
    (∃ β : ℝ → ℝ, (∀ᶠ u in (paretoCDF (two_pos : (0 : ℝ) < 2)).upperEndpointFilter, 0 < β u) ∧
      TendstoUniformlyOn
        (fun u x ↦ excessSurvival (fun y ↦ 1 - paretoCDF (two_pos : (0 : ℝ) < 2) y) u (β u * x))
        (gpdSurvival' (1 / 2) 1) (paretoCDF (two_pos : (0 : ℝ) < 2)).upperEndpointFilter
        (Ici 0)) :=
  ⟨(isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival _ 0).1
      isInMDAGEV_standardExponentialCDF,
    (isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival _ (1 / 2)).1
      (isInMDAGEV_paretoCDF two_pos)⟩

/-! ### Regular variation -/

/-- Exercises `IsRegularlyVarying.tendsto_integral_Ioi_div` (Karamata) on the Pareto tail
`F̄(x) = x^{-2}` (`x ≥ 1`): `∫ₓ^∞ F̄ / (x F̄(x)) → 1`. -/
theorem test_nonvacuous_tendsto_integral_Ioi_div :
    Tendsto (fun x => (∫ t in Ioi x, (1 - paretoCDF (two_pos : (0 : ℝ) < 2) t)) /
      (x * (1 - paretoCDF (two_pos : (0 : ℝ) < 2) x))) atTop (𝓝 (1 / (2 - 1))) :=
  IsRegularlyVarying.tendsto_integral_Ioi_div
    (fun _ _ h => sub_le_sub_left ((paretoCDF two_pos).mono' h) 1)
    test_nonvacuous_isInMDAFrechet_iff (by norm_num)

/-- Exercises `IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi` (the converse half of
Karamata's theorem) on the Pareto tail `x^{-2}`; the hypothesis `x F̄(x) / ∫ₓ^∞ F̄ → 1` is obtained
from the direct half. -/
theorem test_nonvacuous_of_tendsto_mul_div_integral_Ioi :
    IsRegularlyVarying (fun x ↦ 1 - paretoCDF (two_pos : (0 : ℝ) < 2) x) (-2) := by
  refine IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi (a := 1)
    (fun _ _ h => sub_le_sub_left ((paretoCDF two_pos).mono' h) 1) ?_ (by norm_num : (1 : ℝ) < 2) ?_
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).congr_fun
      (fun t ht => (one_sub_paretoCDF_of_one_le two_pos (le_of_lt ht)).symm) measurableSet_Ioi
  · have h := test_nonvacuous_tendsto_integral_Ioi_div.inv₀ (by norm_num)
    norm_num at h ⊢
    exact h

/-- Exercises `potter_bounds_of_measurable` on the Pareto tail `x^{-2}` with `δ = 1`, `A = 2`. -/
theorem test_nonvacuous_potter_bounds_of_measurable :
    ∃ x₀ : ℝ, 0 < x₀ ∧ (∀ x ≥ x₀, 0 < 1 - paretoCDF (two_pos : (0 : ℝ) < 2) x) ∧
      ∀ x ≥ x₀, ∀ y ≥ x₀,
      (2 : ℝ)⁻¹ * min ((y / x) ^ (-2 + 1 : ℝ)) ((y / x) ^ (-2 - 1 : ℝ)) ≤
          (1 - paretoCDF two_pos y) / (1 - paretoCDF two_pos x) ∧
        (1 - paretoCDF two_pos y) / (1 - paretoCDF two_pos x) ≤
          2 * max ((y / x) ^ (-2 + 1 : ℝ)) ((y / x) ^ (-2 - 1 : ℝ)) :=
  IsRegularlyVarying.potter_bounds_of_measurable test_nonvacuous_isInMDAFrechet_iff
    (measurable_const.sub (paretoCDF two_pos).mono.measurable) one_pos one_lt_two

/-- Exercises `isSlowlyVarying_iff_exists_representation` (Karamata's representation theorem) on
`log`. -/
theorem test_nonvacuous_isSlowlyVarying_iff_exists_representation :
    ∃ a : ℝ, 0 < a ∧ ∃ c ε : ℝ → ℝ, Measurable c ∧ Measurable ε ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ Tendsto c atTop (𝓝 c₀)) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ x ≥ a, IntervalIntegrable (fun t => ε t / t) volume a x) ∧
      ∀ x ≥ a, Real.log x = c x * exp (∫ t in a..x, ε t / t) :=
  (isSlowlyVarying_iff_exists_representation measurable_log).1 isSlowlyVarying_log

/-- Test-specific: a bounded multiplier for Breiman's lemma, `Y = min (max V₂ 0) 1 ∈ [0, 1]`. -/
private noncomputable def breimanY' (ω : ℝ × ℝ) : ℝ := min (max ω.2 0) 1

private theorem breimanY'_nonneg (ω : ℝ × ℝ) : 0 ≤ breimanY' ω :=
  le_min (le_max_right _ _) zero_le_one

private theorem breimanY'_le_one (ω : ℝ × ℝ) : breimanY' ω ≤ 1 := min_le_right _ _

/-- Exercises `tendsto_measure_mul_div_measure` (Breiman's lemma) with
`X = Minimality.breimanX 2` (tail `≍ (log x)/x²`, regularly varying with index `-2`) and an
independent bounded `Y ∈ [0, 1]`, `ε = 1`. -/
theorem test_nonvacuous_tendsto_measure_mul_div_measure :
    Tendsto (fun x => (Minimality.breimanP {ω | x < Minimality.breimanX 2 ω * breimanY' ω}).toReal /
      (Minimality.breimanP {ω | x < Minimality.breimanX 2 ω}).toReal) atTop
      (𝓝 (∫ ω, breimanY' ω ^ (2 : ℝ) ∂Minimality.breimanP)) := by
  have hYm : Measurable breimanY' := by unfold breimanY'; fun_prop
  have hind : IndepFun (Minimality.breimanX 2) breimanY' Minimality.breimanP :=
    indepFun_prod (X := fun v : ℝ => max v (exp 1) ^ (2 : ℝ)⁻¹)
      (Y := fun v : ℝ => min (max v 0) 1) (by fun_prop) (by fun_prop)
  refine tendsto_measure_mul_div_measure (Minimality.measurable_breimanX 2) hYm hind
    (ae_of_all _ breimanY'_nonneg) two_pos one_pos
    (Minimality.isRegularlyVarying_breimanX two_pos) ?_
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (breimanY'_nonneg ω) _)]
  exact rpow_le_one (breimanY'_nonneg ω) (breimanY'_le_one ω) (by norm_num)

/-! ### Stable laws -/

section Stable

open SymmPareto

/-- Exercises `tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt'` (generalized CLT,
textbook constants) on the symmetrized Pareto law with `α = 3/2`, `p = 1/2`,
`aₙ = (n + 1)^{2/3}`. -/
theorem test_nonvacuous_tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt' :
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ t, charFun (ν : Measure ℝ) t =
        Complex.exp (-((Gamma (1 - 3 / 2) * cos (π * (3 / 2) / 2) * |t| ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
          (1 - (((2 * (1 / 2) - 1) * Real.sign t * tan (π * (3 / 2) / 2) : ℝ) : ℂ) *
            Complex.I))) ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow (law (3 / 2)) n).map (fun x => (((n : ℝ) + 1) ^ (3 / 2 : ℝ)⁻¹)⁻¹ *
          (x - n * ∫ y, y ∂(law (3 / 2)))),
          (have := isProbabilityMeasure (α := 3 / 2) (by norm_num); inferInstance)⟩)
        atTop (𝓝 ν) := by
  have hα : (0 : ℝ) < 3 / 2 := by norm_num
  have := isProbabilityMeasure hα
  exact tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt' (by norm_num) (by norm_num)
    (isRegularlyVarying hα) (tendsto_measureReal_Ioi_div_absTail hα)
    (fun n => rpow_pos_of_pos (by positivity) _) (tendsto_mul_absTail hα)

/-- Exercises `tendsto_map_convPow_of_isRegularlyVarying_of_lt_one'` (generalized CLT, `α < 1`)
on the symmetrized Pareto law with `α = 1/2`, `p = 1/2`, `aₙ = (n + 1)²`. -/
theorem test_nonvacuous_tendsto_map_convPow_of_isRegularlyVarying_of_lt_one' :
    ∃ ν : ProbabilityMeasure ℝ,
      ∀ t, charFun (ν : Measure ℝ) t =
        Complex.exp (-((Gamma (1 - 1 / 2) * cos (π * (1 / 2) / 2) * |t| ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (1 - (((2 * (1 / 2) - 1) * Real.sign t * tan (π * (1 / 2) / 2) : ℝ) : ℂ) *
            Complex.I)) := by
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have := isProbabilityMeasure hα
  obtain ⟨ν, hν, -⟩ := tendsto_map_convPow_of_isRegularlyVarying_of_lt_one' hα (by norm_num)
    (isRegularlyVarying hα) (tendsto_measureReal_Ioi_div_absTail hα)
    (fun n => rpow_pos_of_pos (by positivity) _) (tendsto_mul_absTail hα)
  exact ⟨ν, hν⟩

/-- Exercises `tendsto_map_convPow_sub_of_isRegularlyVarying_one'` (generalized CLT, `α = 1`) on
the symmetrized Pareto law with `α = 1`, `p = 1/2`, `aₙ = n + 1`. -/
theorem test_nonvacuous_tendsto_map_convPow_sub_of_isRegularlyVarying_one' :
    ∃ ν : ProbabilityMeasure ℝ,
      HasStableOneCharFun (Real.pi / 2) (2 * (1 / 2) - 1) StableIntegral.stableLogConst (ν : Measure ℝ) := by
  have := isProbabilityMeasure (α := 1) one_pos
  obtain ⟨ν, hν, -⟩ := tendsto_map_convPow_sub_of_isRegularlyVarying_one'
    (by simpa using isRegularlyVarying (α := 1) one_pos)
    (tendsto_measureReal_Ioi_div_absTail one_pos)
    (fun n => rpow_pos_of_pos (by positivity) _) (tendsto_mul_absTail one_pos)
  exact ⟨ν, hν⟩

/-- Exercises `tendsto_map_convPow_of_isRegularlyVarying` (generalized CLT, symmetric case) on the
symmetrized Pareto law with `α = 3/2`. The library itself applies it the same way in
`exists_isSymmStable_stableConst`. -/
theorem test_nonvacuous_tendsto_map_convPow_of_isRegularlyVarying :
    ∃ ν : ProbabilityMeasure ℝ, IsSymmStable (3 / 2) (StableIntegral.stableConst (3 / 2)) (ν : Measure ℝ) := by
  have hα : (0 : ℝ) < 3 / 2 := by norm_num
  have := isProbabilityMeasure hα
  obtain ⟨ν, hν, -⟩ := tendsto_map_convPow_of_isRegularlyVarying map_neg hα (by norm_num)
    (isRegularlyVarying hα) (fun n => rpow_pos_of_pos (by positivity) _) (tendsto_mul_absTail hα)
  exact ⟨ν, hν⟩

/-- Exercises `domainOfAttraction_isStableIndex_iff` (Feller's criterion, sufficiency) on the
symmetrized Pareto law with `α = 3/2`. -/
theorem test_nonvacuous_domainOfAttraction_isStableIndex_iff :
    have := isProbabilityMeasure (α := 3 / 2) (by norm_num)
    ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∃ b : ℕ → ℝ, ∃ ν : ProbabilityMeasure ℝ,
      IsStableIndex (3 / 2) ν ∧ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow (law (3 / 2)) n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop
        (𝓝 ν) := by
  have hα : (0 : ℝ) < 3 / 2 := by norm_num
  have := isProbabilityMeasure hα
  exact (domainOfAttraction_isStableIndex_iff hα (by norm_num)).2
    ⟨isRegularlyVarying hα, 1 / 2, by norm_num, by norm_num, tendsto_measureReal_Ioi_div_absTail hα⟩

end Stable

/-- Exercises `IsStable.existsUnique_isStableIndex` on the standard normal law. -/
theorem test_nonvacuous_existsUnique_isStableIndex :
    ∃! α : ℝ, IsStableIndex α (gaussianReal 0 1) :=
  (isStable_gaussianReal 0 one_ne_zero).existsUnique_isStableIndex

/-- Exercises `domainOfAttraction_gaussianReal_iff` (necessity) on the standard normal law, whose
normalized sums are exactly standard normal (`isStrictlyStable_gaussianReal`): its truncated
second moment is slowly varying. -/
theorem test_nonvacuous_domainOfAttraction_gaussianReal_iff :
    (∀ x, gaussianReal 0 1 ≠ Measure.dirac x) ∧
      IsRegularlyVarying (truncSecondMoment (gaussianReal 0 1)) 0 := by
  have hs := isStrictlyStable_gaussianReal (v := 1) one_ne_zero
  let a : ℕ → ℝ := fun n => if h : 1 ≤ n then Classical.choose (hs.exists_mul n h) else 1
  have ha : ∀ n, 0 < a n := fun n => by
    simp only [a]; split_ifs with h
    · exact (Classical.choose_spec (hs.exists_mul n h)).1
    · exact one_pos
  refine domainOfAttraction_gaussianReal_iff.1 ⟨a, ha, fun _ => 0, 0, 1, one_ne_zero, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply Subtype.ext
  simp only [sub_zero]
  have hspec := Classical.choose_spec (hs.exists_mul n hn)
  have han : a n = Classical.choose (hs.exists_mul n hn) := by simp [a, hn]
  rw [← han] at hspec
  rw [hspec.2, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
  have : ((fun x => (a n)⁻¹ * x) ∘ fun x => a n * x) = id := by
    funext x; simp [← mul_assoc, inv_mul_cancel₀ (ha n).ne']
  rw [this, Measure.map_id]

/-! ### Heavy tails -/

/-- Exercises `IsSubexponential.tendsto_tail_compound_div` on the Pareto law `Pareto(1, 2)` with
the number of summands `N ≡ 2`: `P(X₁ + X₂ > x) / P(X > x) → 2`. -/
theorem test_nonvacuous_tendsto_tail_compound_div :
    Tendsto (fun x => tail (compound (paretoMeasure 1 2) (fun n => if n = 2 then 1 else 0)) x /
      tail (paretoMeasure 1 2) x) atTop
      (𝓝 (∑' n : ℕ, n * ((if n = 2 then 1 else 0 : ℝ≥0) : ℝ))) := by
  have := isProbabilityMeasure_paretoMeasure (one_pos : (0 : ℝ) < 1) (two_pos : (0 : ℝ) < 2)
  refine (isSubexponential_paretoMeasure one_pos two_pos).tendsto_tail_compound_div one_pos ?_
  refine summable_of_ne_finset_zero (s := {2}) fun n hn => ?_
  simp only [Finset.mem_singleton] at hn
  simp [hn]

/-- Exercises `tendsto_pkRuin_div_mul_tail` (Embrechts–Veraverbeke) on Pareto claims
`Pareto(1, 2)` with safety loading `ρ = 1`. -/
theorem test_nonvacuous_tendsto_pkRuin_div_mul_tail :
    Tendsto (fun u => pkRuin 1 (integratedTail (paretoMeasure 1 2)) u /
      (u * tail (paretoMeasure 1 2) u)) atTop
      (𝓝 (1 / (1 * (∫ t in Ioi 0, tail (paretoMeasure 1 2) t) * (2 - 1)))) := by
  have := isProbabilityMeasure_paretoMeasure (one_pos : (0 : ℝ) < 1) (two_pos : (0 : ℝ) < 2)
  exact tendsto_pkRuin_div_mul_tail (isRegularlyVarying_tail_paretoMeasure one_pos two_pos)
    (by norm_num) one_pos

end Test.NonVacuity.Classical
