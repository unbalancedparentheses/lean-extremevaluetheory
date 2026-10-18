/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Multivariate.DomainOfAttractionStandardized

/-!
# Multivariate peaks over thresholds: the multivariate generalized Pareto distribution

Rootzén and Tajvidi [RT06] define the **multivariate generalized Pareto distribution** as the
limit of the conditional law of the normalized excess vector `(X - u) / a(u)` given that **some**
coordinate exceeds its threshold, `X ≰ u`. For `X ∼ μ` in the maximum domain of attraction of `ν`
with normalizations `a n > 0`, `b n` (thresholds `u = b n`), with `F(x) = μ (Iic x)` and
`G(x) = ν (Iic x)`,

  `P((X - b n) / a n ≤ x | X ≰ b n) → H(x) = (log G(x ∧ 0) - log G(x)) / log G(0)`

([RT06, Theorem 2.1]). Indeed `P(X ≤ a n x + b n, X ≰ b n) = F(a n x + b n) - F(a n (x ∧ 0) + b n)`,
and the three tails `n (1 - F(·))` converge to `-log G(·)`.

On the standardized (unit Fréchet) scale, with the tail quantile functions `U_i` of the marginals of
`μ` and the exponent function `V = -log G_0` of the standardized limit,

  `P(X ≤ U(n y) | X ≰ U(n 1)) → H_0(y) = (V(y ∧ 1) - V(y)) / V(1)`,  `y ∈ (0, ∞)^ι`,

and `H_0` is **threshold stable**: for every `t ≥ 1` the conditional law of `Y / t` given
`Y ≰ t 1`, for `Y ∼ H_0`, is again `H_0` ([RT06, Theorem 2.2]; [Rootzén, Segers and Wadsworth,
*Multivariate peaks over thresholds models*, Extremes 21 (2018)]).

## Main definitions and results

* `conditionalExcessCDF μ c d x = P(X ≤ c x + d | X ≰ d)`: the distribution function of the
  normalized excess vector `(X - d) / c` given `X ≰ d`.
* `mgpdCDF ν x = (log G(x ∧ 0) - log G(x)) / log G(0)`: the multivariate GPD of [RT06].
* `IsMDAWith.tendsto_conditionalExcessCDF`: [RT06, Theorem 2.1].
* `standardMGPD ν y = (V(y ∧ 1) - V(y)) / V(1)`: the standardized multivariate GPD.
* `IsMDAWith.tendsto_conditionalExcess_tailQuantile`: the standardized version.
* `IsSimpleMaxStable.standardMGPD_threshold_stable`: threshold stability.

## References

* H. Rootzén and N. Tajvidi, *Multivariate generalized Pareto distributions*, Bernoulli 12 (2006),
  917–930 [RT06].
-/

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace ExtremeValueTheory

variable {ι : Type*}

/-- The distribution function of the normalized excess vector `(X - d) / c` given that some
coordinate exceeds its threshold: `P(X ≤ c x + d | X ≰ d)`. -/
noncomputable def conditionalExcessCDF (μ : Measure (ι → ℝ)) (c d x : ι → ℝ) : ℝ :=
  μ.real (Iic (c * x + d) \ Iic d) / μ.real (Iic d)ᶜ

/-- The **multivariate generalized Pareto distribution** associated with a multivariate extreme
value distribution `G` ([RT06, (2.2)]): `H(x) = (log G(x ∧ 0) - log G(x)) / log G(0)`. -/
noncomputable def mgpdCDF (ν : Measure (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  (Real.log (ν.real (Iic (x ⊓ 0))) - Real.log (ν.real (Iic x))) / Real.log (ν.real (Iic 0))

/-- The **standardized multivariate generalized Pareto distribution** of a simple max-stable law
with exponent function `V`: `H_0(y) = (V(y ∧ 1) - V(y)) / V(1)`. -/
noncomputable def standardMGPD (ν : Measure (ι → ℝ)) (y : ι → ℝ) : ℝ :=
  (maxStableExponent ν (y ⊓ 1) - maxStableExponent ν y) / maxStableExponent ν 1

/-- If `n (1 - A n) → α`, `n (1 - B n) → β` and `n (1 - C n) → γ ≠ 0`, then
`(A n - B n) / (1 - C n) → (β - α) / γ`. -/
lemma tendsto_sub_div_one_sub {A B C : ℕ → ℝ} {α β γ : ℝ}
    (hA : Tendsto (fun n : ℕ ↦ n * (1 - A n)) atTop (𝓝 α))
    (hB : Tendsto (fun n : ℕ ↦ n * (1 - B n)) atTop (𝓝 β))
    (hC : Tendsto (fun n : ℕ ↦ n * (1 - C n)) atTop (𝓝 γ)) (hγ : γ ≠ 0) :
    Tendsto (fun n ↦ (A n - B n) / (1 - C n)) atTop (𝓝 ((β - α) / γ)) := by
  refine ((hB.sub hA).div hC hγ).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change (↑n * (1 - B n) - ↑n * (1 - A n)) / (↑n * (1 - C n)) = _
  rw [← mul_sub, show 1 - B n - (1 - A n) = A n - B n by ring, mul_div_mul_left _ _ hn0]

variable [Fintype ι] {μ ν : Measure (ι → ℝ)} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] {a b : ℕ → ι → ℝ}

/-- `P(X ≤ c x + d, X ≰ d) = F(c x + d) - F(c (x ∧ 0) + d)` for `c > 0`. -/
lemma measureReal_Iic_sdiff_Iic {c d x : ι → ℝ} (hc : ∀ i, 0 < c i) :
    μ.real (Iic (c * x + d) \ Iic d) = μ.real (Iic (c * x + d)) - μ.real (Iic (c * (x ⊓ 0) + d)) := by
  have hsub : Iic (c * (x ⊓ 0) + d) ⊆ Iic (c * x + d) := Iic_subset_Iic.2 fun i ↦ by
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inf_apply, Pi.zero_apply]
    exact add_le_add_left (mul_le_mul_of_nonneg_left (min_le_left _ _) (hc i).le) _
  have heq : Iic (c * x + d) \ Iic d = Iic (c * x + d) \ Iic (c * (x ⊓ 0) + d) := by
    ext z
    simp only [Set.mem_sdiff, mem_Iic, and_congr_right_iff]
    intro hz
    refine not_congr ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.inf_apply, Pi.zero_apply]
      rcases le_total (x i) 0 with hx | hx
      · rw [min_eq_left hx]; exact hz i
      · rw [min_eq_right hx, mul_zero, zero_add]; exact h i
    · have := h i
      simp only [Pi.add_apply, Pi.mul_apply, Pi.inf_apply, Pi.zero_apply] at this
      exact this.trans (by
        nlinarith [min_le_right (x i) 0, (hc i).le, mul_le_mul_of_nonneg_left
          (min_le_right (x i) 0) (hc i).le])
  rw [heq, measureReal_sdiff hsub measurableSet_Iic]

/-- **The multivariate GPD as the limit of conditional excess laws** ([RT06, Theorem 2.1]): if
`μ` is in the domain of attraction of `ν` (with continuous marginals), `G(0) < 1` and
`G(x ∧ 0) > 0`, then `P((X - b n) / a n ≤ x | X ≰ b n) → H(x)`. -/
theorem IsMDAWith.tendsto_conditionalExcessCDF (h : IsMDAWith μ ν a b)
    (hc : ∀ i, Continuous (marginal ν i)) {x : ι → ℝ} (hx : 0 < ν.real (Iic (x ⊓ 0)))
    (h0 : ν.real (Iic 0) < 1) :
    Tendsto (fun n ↦ conditionalExcessCDF μ (a n) (b n) x) atTop (𝓝 (mgpdCDF ν x)) := by
  have hcont : ∀ y, ContinuousAt (fun y ↦ ν.real (Iic y)) y := fun y ↦
    continuousAt_measureReal_Iic fun i ↦ (hc i).continuousAt
  have hxpos : 0 < ν.real (Iic x) :=
    hx.trans_le (measureReal_mono (Iic_subset_Iic.2 inf_le_left))
  have h0pos : 0 < ν.real (Iic 0) :=
    hx.trans_le (measureReal_mono (Iic_subset_Iic.2 inf_le_right))
  have hA := h.tendsto_mul_one_sub (hcont x) hxpos
  have hB := h.tendsto_mul_one_sub (hcont (x ⊓ 0)) hx
  have hC := h.tendsto_mul_one_sub (hcont 0) h0pos
  have hγ : -Real.log (ν.real (Iic 0)) ≠ 0 := neg_ne_zero.2 (Real.log_neg h0pos h0).ne
  have := tendsto_sub_div_one_sub hA hB hC hγ
  simp only [mul_zero, zero_add] at this
  convert this using 1
  · funext n
    rw [conditionalExcessCDF, measureReal_Iic_sdiff_Iic (h.pos n),
      probReal_compl_eq_one_sub measurableSet_Iic]
  · rw [mgpdCDF, ← neg_div_neg_eq]
    congr 1
    ring

/-- **The standardized multivariate GPD as a limit** ([RT06, Theorem 2.1], unit Fréchet scale):
with the tail quantile functions `U_i` of the marginals of `μ`,
`P(X ≤ U(n y) | X ≰ U(n 1)) → H_0(y) = (V(y ∧ 1) - V(y)) / V(1)` for `y ∈ (0, ∞)^ι`, where `V` is
the exponent function of the unit Fréchet standardization of the limit. -/
theorem IsMDAWith.tendsto_conditionalExcess_tailQuantile [Nonempty ι] (h : IsMDAWith μ ν a b)
    (hc : ∀ i, Continuous (marginal ν i)) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    Tendsto (fun n : ℕ ↦
      μ.real (Iic (fun i ↦ (marginal μ i).tailQuantile (n * y i)) \
        Iic (fun i ↦ (marginal μ i).tailQuantile (n * 1))) /
      μ.real (Iic (fun i ↦ (marginal μ i).tailQuantile (n * 1)))ᶜ) atTop
      (𝓝 (standardMGPD (frechetStandardization ν) y)) := by
  set U : (ι → ℝ) → ℕ → ι → ℝ := fun w n i ↦ (marginal μ i).tailQuantile (n * w i)
  have hy1 : ∀ i, 0 < (y ⊓ 1) i := fun i ↦ lt_min (hy i) one_pos
  have hA := h.tendsto_mul_one_sub_tailQuantile hc hy
  have hB := h.tendsto_mul_one_sub_tailQuantile hc hy1
  have hC := h.tendsto_mul_one_sub_tailQuantile hc (y := 1) fun _ ↦ one_pos
  have hms := h.isSimpleMaxStable_frechetStandardization hc
  have hV1 : maxStableExponent (frechetStandardization ν) 1 ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := hms.inv_le_maxStableExponent (y := 1) (fun _ ↦ one_pos) i
    simp only [Pi.one_apply, inv_one] at this
    linarith
  have := tendsto_sub_div_one_sub hA hB hC hV1
  refine this.congr' ?_
  have hev : ∀ᶠ n : ℕ in atTop, 1 < (n : ℝ) ∧ ∀ i, 1 < (n : ℝ) * (y ⊓ 1) i := by
    refine (tendsto_natCast_atTop_atTop.eventually_gt_atTop 1).and (eventually_all.2 fun i ↦ ?_)
    exact (tendsto_natCast_atTop_atTop.atTop_mul_const (hy1 i)).eventually_gt_atTop 1
  filter_upwards [hev] with n ⟨hn1, hny⟩
  -- `U(n y) ∧ U(n 1) = U(n (y ∧ 1))` coordinatewise
  have hle1 : ∀ i, U (y ⊓ 1) n i ≤ U 1 n i := fun i ↦
    (marginal μ i).tailQuantile_mono (hny i) (mul_le_mul_of_nonneg_left (min_le_right _ _)
      n.cast_nonneg)
  have hle2 : ∀ i, U (y ⊓ 1) n i ≤ U y n i := fun i ↦
    (marginal μ i).tailQuantile_mono (hny i) (mul_le_mul_of_nonneg_left (min_le_left _ _)
      n.cast_nonneg)
  have heq : Iic (U y n) \ Iic (U 1 n) = Iic (U y n) \ Iic (U (y ⊓ 1) n) := by
    ext z
    simp only [Set.mem_sdiff, mem_Iic, and_congr_right_iff]
    intro hz
    refine not_congr ⟨fun h i ↦ ?_, fun h i ↦ (h i).trans (hle1 i)⟩
    rcases le_total (y i) 1 with hyi | hyi
    · have : U (y ⊓ 1) n i = U y n i := by
        simp only [U, Pi.inf_apply, Pi.one_apply, min_eq_left hyi]
      rw [this]; exact hz i
    · have : U (y ⊓ 1) n i = U 1 n i := by
        simp only [U, Pi.inf_apply, Pi.one_apply, min_eq_right hyi]
      rw [this]; exact h i
  change _ = μ.real (Iic (U y n) \ Iic (U 1 n)) / μ.real (Iic (U 1 n))ᶜ
  rw [heq, measureReal_sdiff (Iic_subset_Iic.2 hle2) measurableSet_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic]

omit [IsProbabilityMeasure ν] in
/-- **Threshold stability of the standardized multivariate GPD** ([RT06, Theorem 2.2]): for a
simple max-stable law with exponent function `V`, `H_0(y) = (V(y ∧ 1) - V(y)) / V(1)` satisfies,
for every `t ≥ 1` and `y ∈ (0, ∞)^ι`,
`(H_0(t y) - H_0(t y ∧ t 1)) / (1 - H_0(t 1)) = H_0(y)`: the conditional law of `Y / t` given
`Y ≰ t 1` is again `H_0`. Moreover `1 - H_0(t 1) = 1 / t`. -/
theorem IsSimpleMaxStable.standardMGPD_threshold_stable [Nonempty ι]
    (hν : IsSimpleMaxStable ν) {t : ℝ} (ht : 1 ≤ t) {y : ι → ℝ} (hy : ∀ i, 0 < y i) :
    1 - standardMGPD ν (t • 1) = t⁻¹ ∧
    (standardMGPD ν (t • y) - standardMGPD ν (t • y ⊓ t • 1)) / (1 - standardMGPD ν (t • 1)) =
      standardMGPD ν y := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have h1 : ∀ i, 0 < (1 : ι → ℝ) i := fun _ ↦ one_pos
  have hy1 : ∀ i, 0 < (y ⊓ 1) i := fun i ↦ lt_min (hy i) one_pos
  have hV1 : 0 < maxStableExponent ν 1 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := hν.inv_le_maxStableExponent h1 i
    simp only [Pi.one_apply, inv_one] at this
    linarith
  have e1 : t • (1 : ι → ℝ) ⊓ 1 = 1 := funext fun i ↦ by
    simp [ht]
  have e2 : (t • y ⊓ t • 1) ⊓ 1 = t • y ⊓ 1 := funext fun i ↦ by
    simp only [Pi.inf_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
    rcases le_total (t * y i) t with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, min_eq_right ht, min_eq_right (ht.trans h)]
  have e3 : t • y ⊓ t • (1 : ι → ℝ) = t • (y ⊓ 1) := funext fun i ↦ by
    simp only [Pi.inf_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
    exact (mul_min_of_nonneg _ _ ht0.le).symm
  have hT : 1 - standardMGPD ν (t • 1) = t⁻¹ := by
    have := hV1.ne'
    rw [standardMGPD, e1, hν.maxStableExponent_smul ht0 h1]
    field_simp
    ring
  refine ⟨hT, ?_⟩
  have := hV1.ne'
  rw [hT, standardMGPD, standardMGPD, standardMGPD, e2, e3, hν.maxStableExponent_smul ht0 hy,
    hν.maxStableExponent_smul ht0 hy1]
  field_simp
  ring

end ExtremeValueTheory
