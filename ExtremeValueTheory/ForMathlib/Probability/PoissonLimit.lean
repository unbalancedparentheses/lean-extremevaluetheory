/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ForMathlib.Probability.PoissonRandomMeasure
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Poisson limits of counts of triangular arrays of independent points

-/

open MeasureTheory Filter Finset Topology Complex
open scoped ENNReal NNReal Real

namespace ProbabilityTheory

/-! ### Inversion formula for random vectors with values in `ℕ ^ k` -/

section Inversion

/-- `∫_0^{2π} exp (i t z) dt = 2π 𝟙{z = 0}` for an integer `z`. -/
lemma integral_Ioc_cexp_mul_intCast_mul_I (z : ℤ) :
    ∫ t in Set.Ioc 0 (2 * π), cexp (t * z * I) = if z = 0 then (2 * π : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hz
  · simp [hz]
  · have hc : (z * I : ℂ) ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hz) I_ne_zero
    have := integral_exp_mul_complex (a := 0) (b := 2 * π) hc
    simp_rw [show ∀ t : ℝ, (t : ℂ) * z * I = (z * I) * t from fun t ↦ by ring]
    rw [this]
    have h1 : cexp (↑z * I * ↑(2 * π)) = 1 := by
      rw [← exp_int_mul_two_pi_mul_I z]
      congr 1
      push_cast
      ring
    push_cast at h1
    simp [h1]

/-- The uniform (unnormalized) measure on the torus `(0, 2π] ^ k`. -/
noncomputable def torusMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k ↦ volume.restrict (Set.Ioc (0 : ℝ) (2 * π))

instance (k : ℕ) : IsFiniteMeasure (torusMeasure k) := by
  have : ∀ _ : Fin k, IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    fun _ ↦ isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  unfold torusMeasure
  infer_instance

/-- `∫_{(0, 2π]^k} exp (i ⟨t, z⟩) dt = (2π)^k 𝟙{z = 0}` for an integer vector `z`. -/
lemma integral_torusMeasure_cexp {k : ℕ} (z : Fin k → ℤ) :
    ∫ t, cexp ((∑ j, t j * z j : ℝ) * I) ∂(torusMeasure k) =
      if z = 0 then (2 * π : ℂ) ^ k else 0 := by
  have h (t : Fin k → ℝ) : cexp ((∑ j, t j * z j : ℝ) * I) = ∏ j, cexp (t j * z j * I) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  simp_rw [h]
  rw [torusMeasure, integral_fintype_prod_eq_prod (f := fun _ (s : ℝ) ↦ cexp (s * z _ * I))]
  simp_rw [integral_Ioc_cexp_mul_intCast_mul_I]
  split_ifs with hz
  · simp [hz]
  · obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra! h'
      exact hz (funext h')
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Inversion formula for random vectors with values in `ℕ ^ k`.** For a random vector
`Y : Ω → ℕ ^ k` with characteristic function `φ`,
`(2π) ^ k P(Y = m) = ∫_{(0, 2π] ^ k} φ(t) exp (-i ⟨t, m⟩) dt`. -/
lemma integral_torusMeasure_charFun_mul (Q : Measure Ω) [IsFiniteMeasure Q] {k : ℕ}
    {Y : Ω → Fin k → ℕ} (hY : Measurable Y) (m : Fin k → ℕ) :
    ∫ t, (∫ ω, cexp ((∑ j, t j * Y ω j : ℝ) * I) ∂Q) * cexp (-(∑ j, t j * m j : ℝ) * I)
        ∂(torusMeasure k) = (2 * π : ℂ) ^ k * Q.real {ω | Y ω = m} := by
  have hprod (t : Fin k → ℝ) (ω : Ω) : cexp ((∑ j, t j * Y ω j : ℝ) * I) *
      cexp (-(∑ j, t j * m j : ℝ) * I) =
      cexp ((∑ j, t j * (((Y ω j : ℤ) - m j : ℤ) : ℝ) : ℝ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    ring
  simp_rw [← integral_mul_const, hprod]
  have hmeas : Measurable fun p : (Fin k → ℝ) × Ω ↦
      cexp ((∑ j, p.1 j * (((p.2 |> Y) j : ℤ) - m j : ℤ) : ℝ) * I) := by
    refine Complex.measurable_exp.comp (Measurable.mul_const ?_ _)
    refine Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun j _ ↦ ?_)
    refine (measurable_pi_apply j |>.comp measurable_fst).mul ?_
    have : Measurable fun ω ↦ ((((Y ω j : ℤ) - m j : ℤ)) : ℝ) :=
      (measurable_of_countable fun y : Fin k → ℕ ↦ ((((y j : ℤ) - m j : ℤ)) : ℝ)).comp hY
    exact this.comp measurable_snd
  rw [integral_integral_swap]
  · simp_rw [integral_torusMeasure_cexp]
    have hind (ω : Ω) : (if (fun j ↦ ((Y ω j : ℤ) - m j : ℤ)) = 0 then (2 * π : ℂ) ^ k else 0) =
        {ω | Y ω = m}.indicator (fun _ ↦ (2 * π : ℂ) ^ k) ω := by
      have : (fun j ↦ ((Y ω j : ℤ) - m j : ℤ)) = 0 ↔ Y ω = m := by
        simp only [funext_iff, Pi.zero_apply, sub_eq_zero, Nat.cast_inj]
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, this]
    simp_rw [hind]
    rw [integral_indicator_const (s := {ω | Y ω = m}) _ (hY (measurableSet_singleton m))]
    simp [mul_comm]
  · refine Integrable.of_bound hmeas.aestronglyMeasurable 1
      (Eventually.of_forall fun p ↦ ?_)
    exact (Complex.norm_exp_ofReal_mul_I _).le

/-- The characteristic function of a random vector with values in `ℕ ^ k` is strongly
measurable. -/
lemma stronglyMeasurable_integral_cexp_natCast (Q : Measure Ω) [SFinite Q] {k : ℕ}
    {Y : Ω → Fin k → ℕ} (hY : Measurable Y) :
    StronglyMeasurable fun t : Fin k → ℝ ↦ ∫ ω, cexp ((∑ j, t j * Y ω j : ℝ) * I) ∂Q := by
  refine StronglyMeasurable.integral_prod_right (f := fun (t : Fin k → ℝ) (ω : Ω) ↦
    cexp ((∑ j, t j * Y ω j : ℝ) * I)) ?_
  refine Measurable.stronglyMeasurable ?_
  refine Complex.measurable_exp.comp (Measurable.mul_const ?_ _)
  refine Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun j _ ↦ ?_)
  refine (measurable_pi_apply j |>.comp measurable_fst).mul ?_
  exact ((measurable_of_countable fun y : Fin k → ℕ ↦ ((y j : ℕ) : ℝ)).comp hY).comp
    measurable_snd

/-- **Convergence of the point probabilities of random vectors with values in `ℕ ^ k`** from the
pointwise convergence of their characteristic functions. -/
theorem tendsto_measureReal_eq_of_tendsto_integral_cexp {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Q : ι → Measure Ω}
    [∀ i, IsProbabilityMeasure (Q i)] {Q' : Measure Ω'} [IsProbabilityMeasure Q'] {k : ℕ}
    {Y : ι → Ω → Fin k → ℕ} {Y' : Ω' → Fin k → ℕ} (hY : ∀ i, Measurable (Y i))
    (hY' : Measurable Y')
    (h : ∀ t : Fin k → ℝ, Tendsto (fun i ↦ ∫ ω, cexp ((∑ j, t j * Y i ω j : ℝ) * I) ∂(Q i)) l
      (𝓝 (∫ ω, cexp ((∑ j, t j * Y' ω j : ℝ) * I) ∂Q'))) (m : Fin k → ℕ) :
    Tendsto (fun i ↦ (Q i).real {ω | Y i ω = m}) l (𝓝 (Q'.real {ω | Y' ω = m})) := by
  have hc : (2 * π : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero])
  have key : Tendsto (fun i ↦ (2 * π : ℂ) ^ k * (Q i).real {ω | Y i ω = m}) l
      (𝓝 ((2 * π : ℂ) ^ k * Q'.real {ω | Y' ω = m})) := by
    simp_rw [← integral_torusMeasure_charFun_mul _ (hY _), ← integral_torusMeasure_charFun_mul _ hY']
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1)
      (Eventually.of_forall fun i ↦ ?_) (Eventually.of_forall fun i ↦ ?_) (integrable_const 1)
      (ae_of_all _ fun t ↦ (h t).mul_const _)
    · refine ((stronglyMeasurable_integral_cexp_natCast _ (hY i)).mul ?_).aestronglyMeasurable
      refine Measurable.stronglyMeasurable ?_
      refine Complex.measurable_exp.comp (Measurable.mul_const ?_ _)
      exact (Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun j _ ↦
        (measurable_pi_apply j).mul_const _)).neg
    · refine ae_of_all _ fun t ↦ ?_
      rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one]
      refine (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω ↦
        (Complex.norm_exp_ofReal_mul_I _).le)).trans ?_
      simp
  have := (Complex.continuous_re.tendsto _).comp (key.const_mul ((2 * π : ℂ) ^ k)⁻¹)
  simpa [Function.comp_def, ← mul_assoc, inv_mul_cancel₀ hc] using this

end Inversion

/-! ### Products of the form `∏ (1 + w i)` -/

/-- If `∑_{i < n} w n i → s`, `∑_{i < n} ‖w n i‖` is bounded and `max_{i < n} ‖w n i‖ → 0`, then
`∏_{i < n} (1 + w n i) → exp s`. -/
lemma tendsto_prod_range_one_add {w : ℕ → ℕ → ℂ} {s : ℂ} {M : ℝ}
    (hsum : Tendsto (fun n ↦ ∑ i ∈ range n, w n i) atTop (𝓝 s))
    (hbdd : ∀ᶠ n in atTop, ∑ i ∈ range n, ‖w n i‖ ≤ M)
    (hmax : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i < n, ‖w n i‖ ≤ ε) :
    Tendsto (fun n ↦ ∏ i ∈ range n, (1 + w n i)) atTop (𝓝 (cexp s)) := by
  have hdiff : Tendsto (fun n ↦ ∑ i ∈ range n, (log (1 + w n i) - w n i)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set ε := min (1 / 2) (δ / (2 * (|M| + 1))) with hε
    have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
    filter_upwards [hbdd, hmax ε hε0] with n hn hw
    rw [dist_zero_right]
    calc ‖∑ i ∈ range n, (log (1 + w n i) - w n i)‖
        ≤ ∑ i ∈ range n, ‖log (1 + w n i) - w n i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range n, ε * ‖w n i‖ := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hwi := hw i (Finset.mem_range.1 hi)
          have hw2 : ‖w n i‖ ≤ 1 / 2 := hwi.trans (min_le_left _ _)
          refine (Complex.norm_log_one_add_sub_self_le (by linarith)).trans ?_
          have h1 : (1 - ‖w n i‖)⁻¹ ≤ 2 := by
            rw [inv_le_comm₀ (by linarith) two_pos]; linarith
          calc ‖w n i‖ ^ 2 * (1 - ‖w n i‖)⁻¹ / 2 ≤ ‖w n i‖ ^ 2 * 2 / 2 := by gcongr
            _ = ‖w n i‖ * ‖w n i‖ := by ring
            _ ≤ ε * ‖w n i‖ := by gcongr
      _ = ε * ∑ i ∈ range n, ‖w n i‖ := by rw [Finset.mul_sum]
      _ ≤ ε * (|M| + 1) := by gcongr; linarith [le_abs_self M]
      _ ≤ δ / (2 * (|M| + 1)) * (|M| + 1) := by gcongr; exact min_le_right _ _
      _ < δ := by
          rw [div_mul_eq_mul_div, mul_comm 2, ← div_div, mul_div_assoc,
            div_self (by positivity : |M| + 1 ≠ 0)]
          linarith
  have hlog : Tendsto (fun n ↦ ∑ i ∈ range n, log (1 + w n i)) atTop (𝓝 s) := by
    have := hdiff.add hsum
    simp only [zero_add, ← Finset.sum_add_distrib, sub_add_cancel] at this
    exact this
  refine ((Complex.continuous_exp.tendsto s).comp hlog).congr' ?_
  filter_upwards [hmax (1 / 2) (by norm_num)] with n hn
  rw [Function.comp_apply, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i hi ↦ Complex.exp_log ?_
  intro h0
  have : ‖w n i‖ = 1 := by
    rw [show w n i = -1 by linear_combination h0, norm_neg, norm_one]
  linarith [hn i (Finset.mem_range.1 hi)]

/-! ### Poisson limits of counts -/

section Counts

/-- A bound used for `1 + ∑ j, p j (exp (i t j) - 1)`. -/
lemma norm_sum_mul_cexp_sub_one_le {k : ℕ} (p : Fin k → ℝ) (hp : ∀ j, 0 ≤ p j) (t : Fin k → ℝ) :
    ‖∑ j, (p j : ℂ) * (cexp (t j * I) - 1)‖ ≤ 2 * ∑ j, p j := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp j), mul_comm 2]
  refine mul_le_mul_of_nonneg_left ?_ (hp j)
  refine (norm_sub_le (cexp (t j * I)) 1).trans ?_
  rw [Complex.norm_exp_ofReal_mul_I, norm_one]
  norm_num

/-- The characteristic function of the Poisson distribution, written as an integral over `ℕ`. -/
lemma integral_cexp_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    ∫ x : ℕ, cexp (t * x * I) ∂(poissonMeasure r) = cexp (r * (cexp (t * I) - 1)) := by
  rw [← charFun_map_cast_poissonMeasure, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop)]
  simp

/-- The joint characteristic function of independent Poisson random variables. -/
lemma integral_cexp_pi_poissonMeasure {k : ℕ} (r : Fin k → ℝ≥0) (t : Fin k → ℝ) :
    ∫ y : Fin k → ℕ, cexp ((∑ j, t j * y j : ℝ) * I) ∂(Measure.pi fun j ↦ poissonMeasure (r j)) =
      cexp (∑ j, ((r j : ℝ) : ℂ) * (cexp (t j * I) - 1)) := by
  have h (y : Fin k → ℕ) : cexp ((∑ j, t j * y j : ℝ) * I) = ∏ j, cexp (t j * y j * I) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (f := fun j (x : ℕ) ↦ cexp (t j * x * I)), Complex.exp_sum]
  simp_rw [integral_cexp_poissonMeasure]

/-- The point probabilities of independent Poisson random variables. -/
lemma measureReal_pi_poissonMeasure_singleton {k : ℕ} (r : Fin k → ℝ≥0) (m : Fin k → ℕ) :
    (Measure.pi fun j ↦ poissonMeasure (r j)).real {m} =
      ∏ j, Real.exp (-r j) * r j ^ m j / (m j).factorial := by
  rw [← Set.univ_pi_singleton, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun j _ ↦ poissonMeasure_real_singleton _ _

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E]

open scoped Classical

/-- The number of points among `Z 0, …, Z (n - 1)` in a set is measurable. -/
lemma measurable_card_filter_range {Z : ℕ → Ω → E} (hZ : ∀ i, Measurable (Z i)) {B : Set E}
    (hB : MeasurableSet B) (n : ℕ) :
    Measurable fun ω ↦ #{i ∈ range n | Z i ω ∈ B} := by
  simp_rw [Finset.card_filter]
  exact Finset.measurable_sum _ fun i _ ↦
    Measurable.ite (hZ i hB) measurable_const measurable_const

/-- The joint characteristic function of the counts of independent points in disjoint sets:
`E exp (i ∑ j, t j #{i < n | Z i ∈ B j}) = ∏_{i < n} (1 + ∑ j, P(Z i ∈ B j) (exp (i t j) - 1))`. -/
lemma integral_cexp_card_filter_range {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → E}
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P) {k : ℕ} {B : Fin k → Set E}
    (hB : ∀ j, MeasurableSet (B j)) (hd : Pairwise (Function.onFun Disjoint B)) (t : Fin k → ℝ)
    (n : ℕ) :
    ∫ ω, cexp ((∑ j, t j * #{i ∈ range n | Z i ω ∈ B j} : ℝ) * I) ∂P =
      ∏ i ∈ range n, (1 + ∑ j, (P.real (Z i ⁻¹' B j) : ℂ) * (cexp (t j * I) - 1)) := by
  set g : E → ℂ := fun z ↦ cexp ((∑ j, t j * (B j).indicator (1 : E → ℝ) z : ℝ) * I) with hg
  have hgm : Measurable g := by
    refine Complex.measurable_exp.comp (Measurable.mul_const ?_ _)
    exact Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun j _ ↦
      (measurable_one.indicator (hB j)).const_mul _)
  have key (ω : Ω) : cexp ((∑ j, t j * #{i ∈ range n | Z i ω ∈ B j} : ℝ) * I) =
      ∏ i : Fin n, g (Z i ω) := by
    rw [hg, ← Complex.exp_sum, ← Finset.sum_mul, Fin.sum_univ_eq_sum_range
      (fun i ↦ ((∑ j, t j * (B j).indicator (1 : E → ℝ) (Z i ω) : ℝ) : ℂ))]
    congr 1
    push_cast
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : Z i ω ∈ B j <;> simp [hi]
  simp_rw [key]
  rw [(hind.precomp Fin.val_injective).integral_fun_prod_comp (f := fun _ ↦ g)
    (fun i ↦ (hZ i).aemeasurable) (fun i ↦ hgm.aestronglyMeasurable),
    ← Fin.prod_univ_eq_prod_range (fun i ↦ (1 + ∑ j, (P.real (Z i ⁻¹' B j) : ℂ) *
      (cexp (t j * I) - 1)))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [hg]
  simp_rw [cexp_sum_indicator_eq hd]
  rw [integral_add (integrable_const _), integral_finsetSum]
  · simp only [integral_const, probReal_univ, one_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show (fun ω ↦ (B j).indicator (fun _ ↦ cexp (t j * I) - 1) (Z i ω)) =
      (Z i ⁻¹' B j).indicator (fun _ ↦ cexp (t j * I) - 1) from funext fun ω ↦ rfl,
      integral_indicator_const _ (hZ i (hB j))]
    simp [Complex.real_smul]
  · intro j _
    exact ((integrable_const _).indicator (hB j)).comp_measurable (hZ i)
  · exact integrable_finsetSum _ fun j _ ↦
      ((integrable_const _).indicator (hB j)).comp_measurable (hZ i)

/-- **Poisson limit theorem for counts of triangular arrays of independent points.** For each
`n`, let `Z n 0, Z n 1, …` be independent random elements under `P n`, and let `B 0, …, B (k-1)`
be disjoint measurable sets. If `∑_{i < n} P(Z n i ∈ B j) → r j` for every `j` and
`max_{i < n} P(Z n i ∈ B j) → 0`, then the counts `#{i < n | Z n i ∈ B j}` converge jointly in law
to independent Poisson random variables with means `r j`. -/
theorem tendsto_measureReal_card_filter_range_eq {P : ℕ → Measure Ω}
    [∀ n, IsProbabilityMeasure (P n)] {Z : ℕ → ℕ → Ω → E} (hZ : ∀ n i, Measurable (Z n i))
    (hind : ∀ n, iIndepFun (Z n) (P n)) {k : ℕ} {B : Fin k → Set E}
    (hB : ∀ j, MeasurableSet (B j)) (hd : Pairwise (Function.onFun Disjoint B))
    {r : Fin k → ℝ≥0}
    (hsum : ∀ j, Tendsto (fun n ↦ ∑ i ∈ range n, (P n).real (Z n i ⁻¹' B j)) atTop (𝓝 (r j)))
    (hmax : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i < n, ∀ j, (P n).real (Z n i ⁻¹' B j) ≤ ε)
    (m : Fin k → ℕ) :
    Tendsto (fun n ↦ (P n).real {ω | ∀ j, #{i ∈ range n | Z n i ω ∈ B j} = m j}) atTop
      (𝓝 (∏ j, Real.exp (-r j) * r j ^ m j / (m j).factorial)) := by
  have hY (n : ℕ) : Measurable fun ω (j : Fin k) ↦ #{i ∈ range n | Z n i ω ∈ B j} :=
    Measurable.of_eval fun j ↦ measurable_card_filter_range (hZ n) (hB j) n
  have h := tendsto_measureReal_eq_of_tendsto_integral_cexp (l := atTop) (Q := P) (Q' :=
    Measure.pi fun j ↦ poissonMeasure (r j)) hY measurable_id (fun t ↦ ?_) m
  · rw [← measureReal_pi_poissonMeasure_singleton]
    convert h using 3 with n
    all_goals ext; simp [funext_iff]
  -- convergence of the characteristic functions
  simp only [id]
  simp_rw [integral_cexp_card_filter_range (hZ _) (hind _) hB hd t,
    integral_cexp_pi_poissonMeasure]
  set p : ℕ → ℕ → Fin k → ℝ := fun n i j ↦ (P n).real (Z n i ⁻¹' B j) with hp
  have hp0 (n i j) : 0 ≤ p n i j := measureReal_nonneg
  refine tendsto_prod_range_one_add (M := 2 * ∑ j, ((r j : ℝ) + 1)) ?_ ?_ ?_
  · simp_rw [Finset.sum_comm (s := range _), ← Finset.sum_mul]
    refine tendsto_finsetSum _ fun j _ ↦ Tendsto.mul_const _ ?_
    have := (Complex.continuous_ofReal.tendsto _).comp (hsum j)
    simpa [Function.comp_def] using this
  · have hev : ∀ᶠ n in atTop, ∀ j, ∑ i ∈ range n, p n i j ≤ r j + 1 := by
      rw [eventually_all]
      exact fun j ↦ (hsum j).eventually (eventually_le_nhds (by linarith))
    filter_upwards [hev] with n hn
    calc ∑ i ∈ range n, ‖∑ j, (p n i j : ℂ) * (cexp (t j * I) - 1)‖
        ≤ ∑ i ∈ range n, 2 * ∑ j, p n i j :=
          Finset.sum_le_sum fun i _ ↦ norm_sum_mul_cexp_sub_one_le _ (hp0 n i) t
      _ = 2 * ∑ j, ∑ i ∈ range n, p n i j := by rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ 2 * ∑ j, ((r j : ℝ) + 1) := by gcongr with j; exact hn j
  · intro ε hε
    filter_upwards [hmax (ε / (2 * (k + 1))) (by positivity)] with n hn i hi
    calc ‖∑ j, (p n i j : ℂ) * (cexp (t j * I) - 1)‖ ≤ 2 * ∑ j, p n i j :=
          norm_sum_mul_cexp_sub_one_le _ (hp0 n i) t
      _ ≤ 2 * ∑ _j : Fin k, ε / (2 * (k + 1)) := by gcongr with j; exact hn i hi j
      _ = ε * (k / (k + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ ε := by
          refine mul_le_of_le_one_right hε.le ?_
          rw [div_le_one (by positivity)]
          linarith

end Counts

end ProbabilityTheory
