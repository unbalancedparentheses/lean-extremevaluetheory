import ExtremeValueTheory.DomainOfAttraction.Examples
import ExtremeValueTheory.DomainOfAttraction.GEVDomain
import ExtremeValueTheory.DomainOfAttraction.Norming
import ExtremeValueTheory.DomainOfAttraction.VonMisesUnified
import ExtremeValueTheory.DomainOfAttraction.SampleMaxima

/-!
# Known answers and non-vacuity: `IsInMDAGEV` against `gevCDF`, and the standard laws

Checks that `IsInMDAGEV ξ` is the textbook domain of attraction of `gevCDF ξ`, on the textbook
examples.

References: [EKM] Embrechts, Klüppelberg, Mikosch, *Modelling Extremal Events* (1997), §3.3;
[dHF] de Haan, Ferreira, *Extreme Value Theory* (2006), §1.1.
-/

open Real Filter Topology Set MeasureTheory ProbabilityTheory
open CumulativeDistributionFunction ExtremeValueTheory

namespace Test.KnownAnswers.DomainExamples

/-! ### The link with `gevCDF` -/

/-- Pareto(`α`): `IsInMDAGEV (1 / α)` gives convergence to `gevCDF (1 / α)` itself, with `ξ = 1/α`
in the Jenkinson–von Mises sign ([EKM, Table 3.4.2]). -/
theorem test_exists_tendsto_gevCDF_pareto {α : ℝ} (hα : 0 < α) :
    ∃ As : ℕ → AffineIncrEquiv, ∀ x,
      Tendsto (fun n : ℕ ↦ ((As n • paretoCDF hα) x) ^ n) atTop (𝓝 (gevCDF (1 / α) x)) :=
  (isInMDAGEV_iff_exists_tendsto_gevCDF _).1 (isInMDAGEV_paretoCDF hα)

/-- `1 - (1 - x)^α` on `[0, 1]`: convergence to `gevCDF (-1 / α)`, the sign `ξ < 0` of the bounded
side ([EKM, Table 3.4.3]). -/
theorem test_exists_tendsto_gevCDF_power {α : ℝ} (hα : 0 < α) :
    ∃ As : ℕ → AffineIncrEquiv, ∀ x,
      Tendsto (fun n : ℕ ↦ ((As n • powerCDF hα) x) ^ n) atTop (𝓝 (gevCDF (-1 / α) x)) :=
  (isInMDAGEV_iff_exists_tendsto_gevCDF _).1 (isInMDAGEV_powerCDF hα)

/-- The converse direction: exponential maxima converge to `gevCDF 0`, so the law is in `MDA(H_0)`
([EKM, Table 3.4.4]). -/
theorem test_isInMDAGEV_of_exists_tendsto_gevCDF_exponential :
    standardExponentialCDF.IsInMDAGEV 0 :=
  (isInMDAGEV_iff_exists_tendsto_gevCDF 0).2
    ((isInMDAGEV_iff_exists_tendsto_gevCDF 0).1 isInMDAGEV_standardExponentialCDF)

/-- Exercises `exists_isInMDAGEV_of_tendsto` on the Gumbel limit of exponential maxima: a
nondegenerate limit at continuity points gives a domain of attraction. -/
theorem test_exists_isInMDAGEV_of_tendsto_exponential :
    ∃ ξ, standardExponentialCDF.IsInMDAGEV ξ := by
  obtain ⟨As, hAs⟩ := isInMDAGumbel_standardExponentialCDF
  exact exists_isInMDAGEV_of_tendsto isExtremeValueDistr_standardGumbelCDF.1 fun x _ => hAs x

/-- Exercises `IsInMDAGEV.unique`: the Pareto(`2`) law is in `MDA(H_{1/2})`, and in no other
`MDA(H_ξ)`; so the exponential law's `ξ = 0` and the uniform law's `ξ = -1` do not apply to it. -/
theorem test_unique_pareto {ξ : ℝ} (h : (paretoCDF (two_pos : (0 : ℝ) < 2)).IsInMDAGEV ξ) :
    ξ = 1 / 2 :=
  h.unique (isInMDAGEV_paretoCDF two_pos)

/-! ### The normal, Gamma and Cauchy laws -/

/-- The normal law at the textbook levels, at `x = 0`: the limit is `Λ(0) = e⁻¹`. -/
theorem test_tendsto_standardNormalCDF_pow_zero :
    Tendsto (fun n ↦ standardNormalCDF (normalScale n * 0 + normalLocation n) ^ n) atTop
      (𝓝 (exp (-1))) := by
  have h := tendsto_standardNormalCDF_pow 0
  rwa [standardGumbelCDF_apply_eq, neg_zero, exp_zero] at h

/-- The normal law is in `MDA(H_0)` and in no other domain: its tail is lighter than any power. -/
theorem test_normal_not_isInMDAGEV {ξ : ℝ} (hξ : ξ ≠ 0) : ¬ standardNormalCDF.IsInMDAGEV ξ :=
  fun h ↦ hξ (h.unique isInMDAGEV_standardNormalCDF)

/-- Normal laws with any mean and positive variance are in `MDA(H_0)`. -/
theorem test_isInMDAGEV_gaussianReal : (ofMeasure (gaussianReal 3 2)).IsInMDAGEV 0 :=
  isInMDAGEV_ofMeasure_gaussianReal 3 two_ne_zero

/-- The Gamma law at `a = r = 1` is the exponential law, and the constants reduce to the classical
`a_n = 1`, `b_n = log n`: `F (x + log n) ^ n → Λ(x)`. -/
theorem test_tendsto_gammaCDF_pow_one (x : ℝ) :
    Tendsto (fun n : ℕ ↦ gammaCDF 1 1 (x + log n) ^ n) atTop (𝓝 (standardGumbelCDF x)) := by
  have h := tendsto_gammaCDF_pow one_pos one_pos x
  simpa using h

/-- Erlang law of shape `3`, rate `2`, in `MDA(H_0)`. -/
theorem test_isInMDAGEV_erlang : (gammaCDF 3 2).IsInMDAGEV 0 :=
  isInMDAGEV_gammaCDF (by norm_num) (by norm_num)

/-- The Cauchy law at `x = 1`: `F (n / π) ^ n → Φ_1(1) = e⁻¹`. -/
theorem test_tendsto_standardCauchyCDF_pow_one :
    Tendsto (fun n : ℕ ↦ standardCauchyCDF ((n : ℝ) / π * 1) ^ n) atTop (𝓝 (exp (-1))) := by
  have h := tendsto_standardCauchyCDF_pow 1
  rw [standardFrechetCDF_apply_pos_eq _ one_pos] at h
  simpa using h

/-- The Cauchy law has `ξ = 1`, not the `ξ = 0` of the normal law. -/
theorem test_cauchy_not_isInMDAGEV_zero : ¬ standardCauchyCDF.IsInMDAGEV 0 := fun h ↦
  zero_ne_one (h.unique isInMDAGEV_standardCauchyCDF)

/-! ### Random-variable forms -/

/-- An iid standard normal sequence, packaged with its marginal c.d.f. Test-specific. -/
private theorem exists_iid_normal :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧
      (∀ i, IdentDistrib (X i) (X 0) P P) ∧
      ∀ x, standardNormalCDF x = P.real {ω | X 0 ω ≤ x} := by
  obtain ⟨Ω, _, P, X, hXm, hlaw, hind, hP⟩ := exists_iid ℕ (gaussianReal 0 1)
  refine ⟨Ω, _, P, X, hP, hXm, hind, fun i ↦ (hlaw i).identDistrib (hlaw 0), fun x ↦ ?_⟩
  rw [standardNormalCDF, ofMeasure_apply, ← (hlaw 0).map_eq, map_measureReal_apply (hXm 0)
    measurableSet_Iic]
  rfl

/-- **Non-vacuity of `isInMDAGEV_iff_exists_tendsto_sampleMax`**: the maxima of an iid normal sequence,
suitably normalized, converge in distribution to the Gumbel law `H_0`. -/
theorem test_normal_sampleMax :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ) (a b : ℕ → ℝ),
      IsProbabilityMeasure P ∧ (∀ n, 0 < a n) ∧ ∀ x,
        Tendsto (fun n ↦ P.real {ω | (blockMax X n 0 ω - b n) / a n ≤ x}) atTop
          (𝓝 (gevCDF 0 x)) := by
  obtain ⟨Ω, _, P, X, hP, -, hind, hid, hF⟩ := exists_iid_normal
  obtain ⟨a, b, ha, h⟩ :=
    (isInMDAGEV_iff_exists_tendsto_sampleMax hF hind hid 0).1 isInMDAGEV_standardNormalCDF
  exact ⟨Ω, _, P, X, a, b, hP, ha, h⟩

/-- **Non-vacuity of `exists_isInMDAGEV_and_smul_eq_of_tendsto_sampleMax`**: applied to the limit of
the normal maxima, it recovers that the limit is of GEV type. -/
theorem test_fisherTippettGnedenko_sampleMax :
    ∃ (A : AffineIncrEquiv) (ξ : ℝ), A • gevCDF 0 = gevCDF ξ := by
  obtain ⟨Ω, _, P, X, hP, -, hind, hid, hF⟩ := exists_iid_normal
  obtain ⟨a, b, ha, h⟩ :=
    (isInMDAGEV_iff_exists_tendsto_sampleMax hF hind hid 0).1 isInMDAGEV_standardNormalCDF
  exact (exists_isInMDAGEV_and_smul_eq_of_tendsto_sampleMax hF hind hid ha
    (isExtremeValueDistr_gevCDF 0).1 fun x _ ↦ h x).2

/-- **Non-vacuity of `isInMDAGEV_iff_exists_tendstoUniformlyOn_cond`**: for a normal variable, the
excess over a high threshold, rescaled and conditioned, tends to the standard exponential law: the
limit `gpdSurvivalAll 0 1 x` is `e^{-x}`. -/
theorem test_normal_cond_excess :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → ℝ) (β : ℝ → ℝ),
      IsProbabilityMeasure P ∧
      TendstoUniformlyOn (fun u x ↦ (P[|X ⁻¹' Ioi u]).real {ω | β u * x < X ω - u})
        (fun x ↦ exp (-x)) standardNormalCDF.upperEndpointFilter (Ici 0) := by
  obtain ⟨Ω, _, P, X, hP, hXm, -, -, hF⟩ := exists_iid_normal
  obtain ⟨β, -, h⟩ := (isInMDAGEV_iff_exists_tendstoUniformlyOn_cond (hXm 0) hF 0).1
    isInMDAGEV_standardNormalCDF
  have hg : gpdSurvivalAll 0 1 = fun x ↦ exp (-x) := by
    funext x
    simp [gpdSurvivalAll]
  rw [hg] at h
  exact ⟨Ω, _, P, X 0, β, hP, h⟩

/-! ### Canonical norming constants and the equivalent forms -/

/-- Exercises `exists_tendsto_pow_norming_tailQuantile` on Pareto(`2`), in `MDA(H_{1/2})`. -/
theorem test_canonical_pareto :
    ∃ a : ℝ → ℝ, ∀ x, Tendsto (fun n : ℕ ↦
      paretoCDF (two_pos : (0 : ℝ) < 2) (a n * x + (paretoCDF two_pos).tailQuantile n) ^ n) atTop
      (𝓝 (gevCDF (1 / 2) x)) := by
  obtain ⟨a, -, h⟩ := exists_tendsto_pow_norming_tailQuantile (isInMDAGEV_paretoCDF two_pos)
  exact ⟨a, h⟩

/-- Exercises `tendsto_pow_tailQuantile_mul_of_pos`, the scale-only constants for `ξ > 0`, on
Pareto(`1`): `F (U_n s) ^ n → Φ_1(s)`. -/
theorem test_tendsto_pow_tailQuantile_mul_pareto (s : ℝ) :
    Tendsto (fun n : ℕ ↦ paretoCDF one_pos ((paretoCDF one_pos).tailQuantile n * s) ^ n) atTop
      (𝓝 (standardFrechetCDF (one_div_pos.2 (show (0 : ℝ) < 1 / 1 by norm_num)) s)) :=
  tendsto_pow_tailQuantile_mul_of_pos (isInMDAGEV_paretoCDF one_pos) (by norm_num) s

/-- Exercises `exists_tendsto_pow_tailQuantile_of_neg`, the constants for `ξ < 0`, on the uniform
law, with `ξ = -1`. -/
theorem test_exists_tendsto_pow_tailQuantile_uniform :
    ∃ ℓ : ℝ, Tendsto (powerCDF one_pos).tailQuantile atTop (𝓝 ℓ) :=
  (exists_tendsto_pow_tailQuantile_of_neg (isInMDAGEV_powerCDF one_pos) (by norm_num)).imp
    fun _ h ↦ h.1

/-- Exercises `tendsto_pow_spacing_of_zero`, the spacing constants for `ξ = 0`, on the normal law. -/
theorem test_tendsto_pow_spacing_normal (x : ℝ) :
    Tendsto (fun n : ℕ ↦ standardNormalCDF (((standardNormalCDF.tailQuantile (2 * n) -
      standardNormalCDF.tailQuantile n) / log 2) * x + standardNormalCDF.tailQuantile n) ^ n) atTop
      (𝓝 (standardGumbelCDF x)) :=
  tendsto_pow_spacing_of_zero isInMDAGEV_standardNormalCDF one_lt_two x

/-- Exercises `isInMDAGEV_iff_exists_tendsto_mul_one_sub`: the normal law, in tail form. -/
theorem test_exists_tendsto_mul_one_sub_normal :
    ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∀ x, Tendsto (fun n : ℕ ↦
      (n : ℝ) * (1 - standardNormalCDF (a n * x + b n))) atTop (𝓝 (exp (-x))) := by
  obtain ⟨a, b, ha, h⟩ :=
    (isInMDAGEV_iff_exists_tendsto_mul_one_sub 0).1 isInMDAGEV_standardNormalCDF
  refine ⟨a, b, ha, fun x ↦ ?_⟩
  simpa using h x (by simp [exp_pos])

/-- Exercises `isInMDAGEV_iff_exists_tendsto_div_tail` on Pareto(`1`), with `ξ = 1`: the limit is
`(1 + x)⁻¹` for `x > -1`, including negative `x`. -/
theorem test_exists_tendsto_div_tail_pareto :
    ∃ f : ℝ → ℝ, (∀ᶠ t in (paretoCDF (one_pos : (0 : ℝ) < 1)).upperEndpointFilter, 0 < f t) ∧
      Tendsto (fun t ↦ (1 - paretoCDF one_pos (t + f t * (-1 / 2))) / (1 - paretoCDF one_pos t))
        (paretoCDF one_pos).upperEndpointFilter (𝓝 2) := by
  have hF : (paretoCDF (one_pos : (0 : ℝ) < 1)).IsInMDAGEV 1 := by
    simpa using isInMDAGEV_paretoCDF (one_pos : (0 : ℝ) < 1)
  obtain ⟨f, hf, h⟩ := (isInMDAGEV_iff_exists_tendsto_div_tail 1).1 hF
  have hval : gpdSurvivalAll 1 1 (-1 / 2) = 2 := by
    norm_num [gpdSurvivalAll]
  refine ⟨f, hf, ?_⟩
  have := h (-1 / 2) (by rw [hval]; norm_num)
  rwa [hval] at this

/-! ### The unified von Mises condition -/

/-- Exercises `isInMDAGEV_of_vonMises` on Pareto(`1`), `F x = 1 - x⁻¹`: with `F' = x⁻²`, `F'' = -2 x⁻³`
the ratio `(1 - F) F'' / (F')²` is `-2 = -γ - 1`, so `γ = 1 = 1 / α`, the textbook shape. -/
theorem test_vonMises_pareto : (paretoCDF (one_pos : (0 : ℝ) < 1)).IsInMDAGEV 1 := by
  refine (paretoCDF one_pos).isInMDAGEV_of_vonMises (z := 1) (γ := 1) zero_le_one
    (F₁ := fun x ↦ (x ^ 2)⁻¹) (F₂ := fun x ↦ -2 * (x ^ 3)⁻¹) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    (fun x hx ↦ ?_) ?_
  · have hx0 : x ≠ 0 := by linarith
    have h : HasDerivAt (fun y : ℝ ↦ 1 - y⁻¹) (x ^ 2)⁻¹ x := by
      simpa using (hasDerivAt_inv hx0).const_sub 1
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hx] with y hy
    rw [paretoCDF_apply_of_one_le one_pos hy.le, rpow_neg_one]
  · have hx0 : x ≠ 0 := by linarith
    have h := (hasDerivAt_pow 2 x).fun_inv (pow_ne_zero 2 hx0)
    convert h using 1
    norm_num
    field_simp
  · have : (0 : ℝ) < x := by linarith
    positivity
  · refine (tendsto_const_nhds (x := (-1 - 1 : ℝ))).congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hx0 : x ≠ 0 := by linarith
    rw [paretoCDF_apply_of_one_le one_pos hx.le, sub_sub_cancel, rpow_neg_one]
    field_simp
    ring

/-- Exercises `isInMDAGEV_of_vonMises_nhdsLT` on `F x = 1 - (1 - x)²` on `[0, 1]`: with `F' = 2 (1 - x)`,
`F'' = -2`, the ratio is `-1/2 = -γ - 1`, so `γ = -1/2 = -1 / α`, the textbook shape. -/
theorem test_vonMises_power : (powerCDF (two_pos : (0 : ℝ) < 2)).IsInMDAGEV (-1 / 2) := by
  have hF : ∀ y ∈ Ioo (0 : ℝ) 1, powerCDF two_pos y = 1 - (1 - y) ^ 2 := fun y hy ↦ by
    rw [powerCDF_apply_of_mem_Icc two_pos (Ioo_subset_Icc_self hy), rpow_two]
  refine (powerCDF two_pos).isInMDAGEV_of_vonMises_nhdsLT (z := 0) (xF := 1) (γ := -1 / 2) one_pos
    (by norm_num) (F₁ := fun x ↦ 2 * (1 - x)) (F₂ := fun _ ↦ -2) (fun x hx ↦ ?_) (fun x _ ↦ ?_)
    (fun x hx ↦ ?_) ?_ ?_
  · have h : HasDerivAt (fun y : ℝ ↦ 1 - (1 - y) ^ 2) (2 * (1 - x)) x := by
      have := (((hasDerivAt_id x).const_sub 1).pow 2).const_sub 1
      convert this using 1 <;> simp
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using hF y hy
  · have := ((hasDerivAt_id x).const_sub 1).const_mul 2
    simpa using this
  · have := hx.2
    show 0 < 2 * (1 - x)
    linarith
  · have hc : Tendsto (fun y : ℝ ↦ 1 - (1 - y) ^ 2) (𝓝[<] 1) (𝓝 (1 - (1 - 1) ^ 2)) :=
      (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
    norm_num at hc
    refine hc.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with y hy
    exact (hF y hy).symm
  · refine (tendsto_const_nhds (x := (-(-1 / 2) - 1 : ℝ))).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with y hy
    have h1 : 1 - y ≠ 0 := by linarith [hy.2]
    rw [hF y hy, sub_sub_cancel]
    field_simp
    ring

end Test.KnownAnswers.DomainExamples
