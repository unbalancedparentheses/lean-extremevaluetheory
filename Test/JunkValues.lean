import ExtremeValueTheory

/-!
# Junk-value tests

Statements that hold, in some admissible instance, only because of one of Lean's totalization
conventions (`x / 0 = 0`, `0⁻¹ = 0`, `ENNReal.toReal ∞ = 0`, the integral of a non-integrable
function is `0`, the sum of a non-summable series is `0`). Each test instantiates a public
statement in the junk case. See `Test/JUNK_VALUES.md` for the audit these come from and
`scripts/JunkScan.lean` for the scanner.
-/

open MeasureTheory Set Filter Topology ExtremeValueTheory
open scoped ENNReal

namespace JunkValuesTest

/-! ### Fixed: `HasSpectralMeasure.measure_univ_toReal` needs a finite `H`

`HasSpectralMeasure ν H` reads `ν (Iic y) = exp (-(∫⁻ max_i w i / y i ∂H).toReal)`. For an
infinite `H` the integral is `∞`, `toReal ∞ = 0`, and the condition becomes `ν (Iic y) = 1`: the
infinite measure `∞ • δ₁` is a "spectral measure" of the point mass `δ₀`. Before the fix,
`measure_univ_toReal` (total mass = extremal coefficient, textbook value in `[1, d]`) applied to
this pair and read `0 = 0`. It now assumes `[IsFiniteMeasure H]`. -/

/-- An infinite measure concentrated on the sup-norm sphere. -/
noncomputable def Hinf : Measure (Fin 2 → ℝ≥0∞) := (∞ : ℝ≥0∞) • Measure.dirac (fun _ ↦ 1)

/-- The point mass at the origin; it is not max-stable. -/
noncomputable def ν0 : Measure (Fin 2 → ℝ) := Measure.dirac 0

/-- Junk: the infinite `Hinf` satisfies `HasSpectralMeasure ν0`, since `exp (-(∞).toReal) = 1`. -/
theorem test_hasSpectralMeasure_infinite : HasSpectralMeasure ν0 Hinf := by
  intro y hy
  have h0 : (0 : Fin 2 → ℝ) ∈ Iic y := fun i ↦ (hy i).le
  have hlin : ∫⁻ w, ⨆ i, w i / ENNReal.ofReal (y i) ∂Hinf = ∞ := by
    rw [Hinf, lintegral_smul_measure, lintegral_dirac]
    have : (0 : ℝ≥0∞) < ⨆ i : Fin 2, (1 : ℝ≥0∞) / ENNReal.ofReal (y i) :=
      lt_of_lt_of_le (ENNReal.div_pos one_ne_zero ENNReal.ofReal_ne_top)
        (le_iSup (fun i : Fin 2 ↦ (1 : ℝ≥0∞) / ENNReal.ofReal (y i)) 0)
    exact ENNReal.top_mul this.ne'
  rw [hlin, ν0, Measure.dirac_apply_of_mem h0]
  simp

/-- `Hinf` is concentrated on the sphere `max_i w i = 1`, the other hypothesis of
`measure_univ_toReal`. -/
theorem test_Hinf_sphere : ∀ᵐ w ∂Hinf, ⨆ i, w i = 1 := by
  refine Measure.ae_smul_measure ?_ _
  rw [ae_dirac_eq]
  simp

/-- Both sides of the (old) conclusion are junk `0`: `(∞).toReal = 0` on the left, and
`extremalCoefficient δ₀ = -log 1 = 0` on the right (textbook range `[1, 2]`). -/
theorem test_spectral_both_sides_junk :
    (Hinf univ).toReal = 0 ∧ extremalCoefficient ν0 = 0 := by
  refine ⟨by simp [Hinf], ?_⟩
  simp [extremalCoefficient, maxStableExponent, ν0, measureReal_def,
    Measure.dirac_apply_of_mem (show (0 : Fin 2 → ℝ) ∈ Iic (fun _ ↦ 1) from fun _ ↦ zero_le_one)]

/-- The fix: `Hinf` is not finite, so the strengthened `measure_univ_toReal` no longer applies. -/
theorem test_Hinf_not_finite : ¬ IsFiniteMeasure Hinf := by
  intro h
  exact measure_ne_top Hinf univ (by simp [Hinf])

/-! ### Documented: the Hill estimator at `k = 0`

`hill x k = k⁻¹ * ∑_{i<k} (log X_(i) - log X_(k))`; at `k = 0` it is `0⁻¹ * 0 = 0`. The
minimality counterexample `Minimality.exists_hill_k_bounded_counterexample` quantifies over all
bounded `k`, so its `kₙ = 0` instances fail consistency only because the estimator is junk `0`;
its content for `k ≥ 1` is genuine. -/

/-- Junk: `hill x 0 = 0` (textbook: undefined). -/
theorem test_hill_zero {n : ℕ} (x : Fin n → ℝ) : hill x 0 = 0 := by simp [hill]

/-! ### Documented: Karamata for `α < 1`

`Minimality.not_tendsto_integral_Ioi_div_of_lt_one` says the Karamata ratio does not tend to
`1 / (α - 1)` when `α < 1`. In that regime `F` is not integrable on any `Ioi x`, so `∫` is junk `0`
and the ratio is identically `0`; the limit fails because `0 ≠ 1 / (α - 1)`, not because the
integral diverges. The divergence is recorded honestly by `max_rpow_karamata_counterexample`. -/

/-- Junk: for `F(t) = max(t, 1)^(-α)`, `0 ≤ α < 1`, the Karamata ratio is identically `0`. -/
theorem test_karamata_lt_one_ratio_zero {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 1) (x : ℝ) :
    (∫ t in Ioi x, max t 1 ^ (-α)) / (x * max x 1 ^ (-α)) = 0 := by
  have h := (Minimality.max_rpow_karamata_counterexample hα0 hα).2.2.1 x
  rw [integral_undef h, zero_div]

/-! ### Documented: `tail_compound` with a non-summable weight sequence

`tail_compound : tail (compound μ p) x = ∑' n, p n * tail (μ^{*n}) x` has no summability
hypothesis on `p`. For `p ≡ 1` the compound "law" has infinite mass on `(-1, ∞)`, and the identity
reads `0 = 0` (`toReal ∞ = 0` on the left, the sum of a non-summable series on the right). The
identity is still consistent, and its only user `tendsto_tail_compound_div` assumes summability. -/

theorem test_convPow_dirac_zero (n : ℕ) :
    Subexp.convPow (Measure.dirac (0 : ℝ)) n = Measure.dirac 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Subexp.convPow_succ, ih]; simp

/-- Junk: the tail of the infinite-mass compound measure at `-1` is `0` (textbook: `∞`). -/
theorem test_tail_compound_nonsummable :
    tail (compound (Measure.dirac (0 : ℝ)) (fun _ ↦ 1)) (-1) = 0 := by
  rw [tail_compound]
  simp only [test_convPow_dirac_zero, NNReal.coe_one, one_mul]
  have : tail (Measure.dirac (0 : ℝ)) (-1) = 1 := by
    simp [tail, measureReal_def,
      Measure.dirac_apply_of_mem (show (0 : ℝ) ∈ Set.Ioi (-1) by norm_num)]
  rw [this, tsum_const]
  simp

end JunkValuesTest
