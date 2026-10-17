/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.InfiniteMovingAverage

/-!
# The spectral tail process of an infinite moving average

Let `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` with `ψ_j ≥ 0` (not all zero), `∑ ψ_j^δ < ∞`, and iid nonnegative
noise with `P(Z_0 > x)` regularly varying with index `-α`, `0 < δ < α < 1`. Its spectral tail
process is ([DR85], [KS20, §15.3], [Meinguet–Segers 2010])

  `Θ_t = ψ_{J+t} / ψ_J`,  `P(J = j) = ψ_j^α / ∑_i ψ_i^α`,  `J ∈ ℕ`,

and its candidate extremal index is `ϑ = sup_j ψ_j^α / ∑_j ψ_j^α`.

## Main results

* `tendstoLawCond_of_approx`: a *converging together* principle for conditional laws: if
  `(B^m_x, V^m_x)` converge to `ν_m` for every `m`, `ν_m → ν`, and `(B^m_x, V^m_x)` approximate
  `(B_x, V_x)` in the sense that the symmetric difference of the conditioning events and the set
  where `V_x, V^m_x` are `ε`-apart are `o(P(B_x))` as `m → ∞`, uniformly for large `x`, then
  `(B_x, V_x)` converges to `ν`.
* `InfiniteMovingAverage.hasSpectralTailProcess`: the spectral tail process of `X` is
  `Θ_t = ψ_{J+t} / ψ_J`.
* `InfiniteMovingAverage.candidateExtremalIndex_spectral`: `ϑ = sup_j ψ_j^α / ∑_j ψ_j^α`.

## Proof

Work with the tail process `Y_t = R Θ_t` (`R` Pareto, independent of `J`). The finite moving
averages `X^{(m)}` have tail process `R Θ^{(m)}_t` (`MovingAverage.hasSpectralTailProcess` and
`HasSpectralTailProcess.hasTailProcess`), whose window laws converge as `m → ∞` to those of
`R Θ_t` (Tannery's theorem). The windows `(X_t / x)_{t ∈ S}` and `(X^{(m)}_t / x)_{t ∈ S}` are
`ε`-close off `⋃_{t ∈ S} {|X_t - X^{(m)}_t| > ε x}`, whose probability is
`≤ |S| K T_m P(Z_0 > εx)` (`exists_measureReal_abs_sub_gt_le`), and
`{X_0 > x} Δ {X^{(m)}_0 > x}` is contained in that event for `t = 0` together with
`{(1 - ε)x < X^{(m)}_0 ≤ (1 + ε)x}`. Converging together gives the tail process of `X`, and
`HasTailProcess.hasSpectralTailProcess` its spectral tail process.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

/-! ### Converging together for conditional laws -/

section ConvergingTogether

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]

omit [IsProbabilityMeasure P] in
theorem abs_integral_le_of_abs_le {F G : Ω → ℝ} (hF : Integrable F P) (hG : Integrable G P)
    (h : ∀ ω, |F ω| ≤ G ω) : |∫ ω, F ω ∂P| ≤ ∫ ω, G ω ∂P := by
  refine abs_le.2 ⟨?_, integral_mono hF hG fun ω => (abs_le.1 (h ω)).2⟩
  rw [← integral_neg]
  exact integral_mono hG.neg hF fun ω => (abs_le.1 (h ω)).1

omit [OpensMeasurableSpace E] in
/-- **Comparison of two conditional expectations.** If `|g| ≤ M`, `g` is `K`-Lipschitz, and
`dist (V ω) (V' ω) ≤ ε` off `D`, then
`|E[g(V) | B] - E[g(V') | B']| ≤ K ε + 2M (P(B \ B') + P(B' \ B) + P(B ∩ D)) / P(B)`. -/
theorem abs_integral_cond_sub_le {B B' D : Set Ω} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hD : MeasurableSet D) {V V' : Ω → E} (hV : Measurable V) (hV' : Measurable V')
    {g : E → ℝ} (hgm : Measurable g) {M K ε : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y, |g y| ≤ M)
    (hK0 : 0 ≤ K) (hK : ∀ y y', |g y - g y'| ≤ K * dist y y') (hε : 0 ≤ ε)
    (hDc : ∀ ω, ω ∉ D → dist (V ω) (V' ω) ≤ ε) (hPB : 0 < P.real B) (hPB' : 0 < P.real B') :
    |∫ ω, g (V ω) ∂P[|B] - ∫ ω, g (V' ω) ∂P[|B']| ≤
      K * ε + 2 * M * (P.real (B \ B') + P.real (B' \ B) + P.real (B ∩ D)) / P.real B := by
  rw [integral_cond_eq, integral_cond_eq, smul_eq_mul, smul_eq_mul, ← integral_indicator hB,
    ← integral_indicator hB']
  set a := P.real B
  set b := P.real B'
  set Δ := P.real (B \ B') + P.real (B' \ B) with hΔ
  have hgV : Measurable fun ω => g (V ω) := hgm.comp hV
  have hgV' : Measurable fun ω => g (V' ω) := hgm.comp hV'
  have hI1 : Integrable (B.indicator fun ω => g (V ω)) P :=
    (integrable_of_abs_le hgV fun ω => hM (V ω)).indicator hB
  have hI2 : Integrable (B'.indicator fun ω => g (V' ω)) P :=
    (integrable_of_abs_le hgV' fun ω => hM (V' ω)).indicator hB'
  set A := ∫ ω, B.indicator (fun ω => g (V ω)) ω ∂P
  set A' := ∫ ω, B'.indicator (fun ω => g (V' ω)) ω ∂P
  -- the difference of the integrals
  have hAA : |A - A'| ≤ K * ε * a + 2 * M * P.real (B ∩ D) + M * Δ := by
    rw [← integral_sub hI1 hI2]
    set G1 : Ω → ℝ := B.indicator fun _ => K * ε with hG1
    set G2 : Ω → ℝ := (B ∩ D).indicator fun _ => 2 * M with hG2
    set G3 : Ω → ℝ := (B \ B').indicator fun _ => M with hG3
    set G4 : Ω → ℝ := (B' \ B).indicator fun _ => M with hG4
    have i1 : Integrable G1 P := (integrable_const _).indicator hB
    have i2 : Integrable G2 P := (integrable_const _).indicator (hB.inter hD)
    have i3 : Integrable G3 P := (integrable_const _).indicator (hB.diff hB')
    have i4 : Integrable G4 P := (integrable_const _).indicator (hB'.diff hB)
    have i12 : Integrable (fun ω => G1 ω + G2 ω) P := i1.add i2
    have i123 : Integrable (fun ω => G1 ω + G2 ω + G3 ω) P := i12.add i3
    have i1234 : Integrable (fun ω => G1 ω + G2 ω + G3 ω + G4 ω) P := i123.add i4
    refine (abs_integral_le_of_abs_le (hI1.sub hI2) i1234 fun ω => ?_).trans_eq ?_
    · have hKε : 0 ≤ K * ε := mul_nonneg hK0 hε
      by_cases h1 : ω ∈ B <;> by_cases h2 : ω ∈ B' <;> by_cases h3 : ω ∈ D <;>
        simp [hG1, hG2, hG3, hG4, Set.indicator, h1, h2, h3]
      · linarith [abs_sub (g (V ω)) (g (V' ω)), hM (V ω), hM (V' ω)]
      · exact (hK _ _).trans (mul_le_mul_of_nonneg_left (hDc ω h3) hK0)
      · linarith [hM (V ω)]
      · linarith [hM (V ω)]
      · simpa [abs_neg] using hM (V' ω)
      · simpa [abs_neg] using hM (V' ω)
    · have e1 : ∫ ω, (G1 ω + G2 ω + G3 ω + G4 ω) ∂P =
          ∫ ω, (G1 ω + G2 ω + G3 ω) ∂P + ∫ ω, G4 ω ∂P := integral_add i123 i4
      have e2 : ∫ ω, (G1 ω + G2 ω + G3 ω) ∂P = ∫ ω, (G1 ω + G2 ω) ∂P + ∫ ω, G3 ω ∂P :=
        integral_add i12 i3
      have e3 : ∫ ω, (G1 ω + G2 ω) ∂P = ∫ ω, G1 ω ∂P + ∫ ω, G2 ω ∂P := integral_add i1 i2
      rw [e1, e2, e3, hG1, hG2, hG3, hG4, integral_indicator_const _ hB,
        integral_indicator_const _ (hB.inter hD), integral_indicator_const _ (hB.diff hB'),
        integral_indicator_const _ (hB'.diff hB)]
      simp only [smul_eq_mul, hΔ]
      ring
  have hA' : |A'| ≤ M * b := by
    refine (abs_integral_le_of_abs_le hI2 ((integrable_const M).indicator hB')
      fun ω => ?_).trans_eq ?_
    · by_cases h : ω ∈ B' <;> simp [Set.indicator, h, hM]
    · rw [integral_indicator_const _ hB', smul_eq_mul, mul_comm]
  have hab : |b - a| ≤ Δ := by
    have h1 : a ≤ b + P.real (B \ B') :=
      (measureReal_mono (show B ⊆ B' ∪ (B \ B') from fun ω h => by
        by_cases h' : ω ∈ B'
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩) (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    have h2 : b ≤ a + P.real (B' \ B) :=
      (measureReal_mono (show B' ⊆ B ∪ (B' \ B) from fun ω h => by
        by_cases h' : ω ∈ B
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩) (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    have := measureReal_nonneg (μ := P) (s := B \ B')
    have := measureReal_nonneg (μ := P) (s := B' \ B)
    rw [abs_le]; constructor <;> linarith
  have hkey : a⁻¹ * A - b⁻¹ * A' = (A - A') / a + A' * (b - a) / (a * b) := by
    field_simp; ring
  have h1 : |(A - A') / a| ≤ (K * ε * a + 2 * M * P.real (B ∩ D) + M * Δ) / a := by
    rw [abs_div, abs_of_pos hPB]
    exact div_le_div_of_nonneg_right hAA hPB.le
  have h2 : |A' * (b - a) / (a * b)| ≤ M * Δ / a := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hPB hPB')]
    calc |A'| * |b - a| / (a * b) ≤ M * b * Δ / (a * b) := by
          apply div_le_div_of_nonneg_right _ (mul_pos hPB hPB').le
          exact mul_le_mul hA' hab (abs_nonneg _) (by positivity)
      _ = M * Δ / a := by field_simp
  rw [hkey]
  refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
  field_simp
  ring

/-- **Converging together for conditional laws.** Let `(B_x, V_x)` be conditioning events and
`E`-valued random elements, approximated by `(B^m_x, V^m_x)` whose conditional laws converge to
`ν_m`, with `ν_m → ν`. If for all `ε, η > 0`, for large `m` and then large `x`, there is an event
`D` off which `V_x` and `V^m_x` are `ε`-close and with
`P(B_x \ B^m_x) + P(B^m_x \ B_x) + P(B_x ∩ D) ≤ η P(B_x)`, then the conditional laws of `V_x`
given `B_x` converge to `ν`. -/
theorem tendstoLawCond_of_approx [Nonempty E] {B : ℝ → Set Ω} {V : ℝ → Ω → E}
    {Bm : ℕ → ℝ → Set Ω} {Vm : ℕ → ℝ → Ω → E} {ν : Measure E} [IsProbabilityMeasure ν]
    {νm : ℕ → Measure E}
    (hB : ∀ x, MeasurableSet (B x)) (hBm : ∀ m x, MeasurableSet (Bm m x))
    (hV : ∀ x, Measurable (V x)) (hVm : ∀ m x, Measurable (Vm m x))
    (hpos : ∀ᶠ x in atTop, 0 < P.real (B x))
    (hm : ∀ m, TendstoLawCond P (Bm m) (Vm m) atTop (νm m))
    (hν : ∀ g : E →ᵇ ℝ, Tendsto (fun m => ∫ y, g y ∂νm m) atTop (𝓝 (∫ y, g y ∂ν)))
    (happrox : ∀ ε > 0, ∀ η > 0, ∀ᶠ m in atTop, ∀ᶠ x in atTop, ∃ D : Set Ω, MeasurableSet D ∧
      (∀ ω ∉ D, dist (V x ω) (Vm m x ω) ≤ ε) ∧
      P.real (B x \ Bm m x) + P.real (Bm m x \ B x) + P.real (B x ∩ D) ≤ η * P.real (B x)) :
    TendstoLawCond P B V atTop ν := by
  intro f
  have hprob : ∀ᶠ x in atTop, IsProbabilityMeasure ((P[|B x]).map (V x)) := by
    filter_upwards [hpos] with x hx
    have h0 : P (B x) ≠ 0 := fun h => by simp [measureReal_def, h] at hx
    have := cond_isProbabilityMeasure (μ := P) h0
    exact inferInstance
  refine (MeasureTheory.tendsto_integral_of_forall_lipschitz hprob ?_ f).congr fun x => ?_
  swap
  · rw [integral_map (hV x).aemeasurable f.continuous.aestronglyMeasurable]
  rintro g ⟨C, hC⟩ ⟨K, hK⟩
  have hgc : Continuous g := hK.continuous
  have hgm : Measurable g := hgc.measurable
  refine (?_ : Tendsto (fun x => ∫ ω, g (V x ω) ∂P[|B x]) atTop _).congr fun x =>
    (integral_map (hV x).aemeasurable hgc.aestronglyMeasurable).symm
  obtain ⟨y₀⟩ := ‹Nonempty E›
  set M := |g y₀| + C with hM_def
  have hM : ∀ y, |g y| ≤ M := fun y => by
    have := hC y y₀
    rw [Real.dist_eq] at this
    linarith [abs_sub_abs_le_abs_sub (g y) (g y₀)]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM y₀)
  have hK' : ∀ y y', |g y - g y'| ≤ K * dist y y' := fun y y' => by
    rw [← Real.dist_eq]; exact hK.dist_le_mul y y'
  set gB : E →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨g, hgc⟩ C hC
  have hgB : ∀ y, gB y = g y := fun y => rfl
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hK0 : (0 : ℝ) ≤ K := K.2
  set ε := δ / (4 * (K + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hKε : K * ε < δ / 4 := by
    rw [hε_def, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set η := min (1 / 2) (δ / (4 * (2 * M + 1))) with hη_def
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hMη : 2 * M * η < δ / 4 := by
    calc 2 * M * η ≤ 2 * M * (δ / (4 * (2 * M + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ < δ / 4 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  obtain ⟨m, hm1, hm2⟩ := ((happrox ε hε η hη).and ((hν gB).eventually
    (Metric.ball_mem_nhds _ (show 0 < δ / 4 by positivity)))).exists
  filter_upwards [hm1, (hm m gB).eventually (Metric.ball_mem_nhds _
    (show 0 < δ / 4 by positivity)), hpos] with x ⟨D, hDm, hDc, hsum⟩ h2 hx
  simp only [Real.dist_eq, hgB] at hm2 h2 ⊢
  have hd0 := measureReal_nonneg (μ := P) (s := Bm m x \ B x)
  have hd1 := measureReal_nonneg (μ := P) (s := B x ∩ D)
  have hBm0 : 0 < P.real (Bm m x) := by
    have : P.real (B x) ≤ P.real (Bm m x) + P.real (B x \ Bm m x) :=
      (measureReal_mono (show B x ⊆ Bm m x ∪ (B x \ Bm m x) from fun ω h => by
        by_cases h' : ω ∈ Bm m x
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩) (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    nlinarith
  have h1 := abs_integral_cond_sub_le (hB x) (hBm m x) hDm (hV x) (hVm m x) hgm hM0 hM hK0 hK'
    hε.le hDc hx hBm0
  have h3 : 2 * M * (P.real (B x \ Bm m x) + P.real (Bm m x \ B x) + P.real (B x ∩ D)) /
      P.real (B x) ≤ 2 * M * η := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hx).2 hsum) (by positivity)
  calc |∫ ω, g (V x ω) ∂P[|B x] - ∫ y, g y ∂ν|
      ≤ |∫ ω, g (V x ω) ∂P[|B x] - ∫ ω, g (Vm m x ω) ∂P[|Bm m x]| +
        |∫ ω, g (Vm m x ω) ∂P[|Bm m x] - ∫ y, g y ∂νm m| + |∫ y, g y ∂νm m - ∫ y, g y ∂ν| := by
        have := abs_sub_le (∫ ω, g (V x ω) ∂P[|B x]) (∫ ω, g (Vm m x ω) ∂P[|Bm m x])
          (∫ y, g y ∂ν)
        have := abs_sub_le (∫ ω, g (Vm m x ω) ∂P[|Bm m x]) (∫ y, g y ∂νm m) (∫ y, g y ∂ν)
        linarith
    _ < δ := by linarith

end ConvergingTogether

end ExtremeValueTheory
