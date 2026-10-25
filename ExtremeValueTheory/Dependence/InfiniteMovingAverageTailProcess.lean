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
    (hm : ∀ᶠ m in atTop, TendstoLawCond P (Bm m) (Vm m) atTop (νm m))
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
  obtain ⟨m, ⟨hm1, hm2⟩, hm3⟩ := (((happrox ε hε η hη).and ((hν gB).eventually
    (Metric.ball_mem_nhds _ (show 0 < δ / 4 by positivity)))).and hm).exists
  filter_upwards [hm1, (hm3 gB).eventually (Metric.ball_mem_nhds _
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

namespace InfiniteMovingAverage

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Z : ℤ → Ω → ℝ} {ψ : ℕ → ℝ}
  {α δ : ℝ}

/-! ### Measurability -/

theorem measurable_process (hZ : ∀ i, Measurable (Z i)) (t : ℤ) :
    Measurable (process ψ Z t) :=
  Measurable.tsum fun _ => (hZ _).const_mul _

theorem process_nonneg (hψ0 : ∀ j, 0 ≤ ψ j) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (t : ℤ) (ω : Ω) :
    0 ≤ process ψ Z t ω :=
  tsum_nonneg fun j => mul_nonneg (hψ0 j) (hZ0 _ ω)

/-! ### Truncation -/

/-- The truncated coefficients `ψ_j 1{j ≤ m}`. -/
noncomputable def trunc (m : ℕ) (ψ : ℕ → ℝ) (j : ℕ) : ℝ := if j ≤ m then ψ j else 0

theorem trunc_of_le {m j : ℕ} (h : j ≤ m) : trunc m ψ j = ψ j := by simp [trunc, h]

theorem trunc_of_lt {m j : ℕ} (h : m < j) : trunc m ψ j = 0 := by
  simp [trunc, show ¬ j ≤ m by omega]

theorem trunc_nonneg (hψ0 : ∀ j, 0 ≤ ψ j) (m j : ℕ) : 0 ≤ trunc m ψ j := by
  unfold trunc; split_ifs
  · exact hψ0 j
  · exact le_rfl

theorem process_trunc (m : ℕ) :
    MovingAverage.process m (trunc m ψ) Z = MovingAverage.process m ψ Z := by
  funext t ω
  exact Finset.sum_congr rfl fun i hi => by
    rw [trunc_of_le (by simp only [Finset.mem_range] at hi; omega)]

theorem weightSum_trunc (m : ℕ) :
    MovingAverage.weightSum m (trunc m ψ) α = MovingAverage.weightSum m ψ α :=
  Finset.sum_congr rfl fun i hi => by
    rw [trunc_of_le (by simp only [Finset.mem_range] at hi; omega)]

theorem coef_trunc {m : ℕ} {k : ℤ} (hk : k ≤ m) :
    MovingAverage.coef (trunc m ψ) k = MovingAverage.coef ψ k := by
  unfold MovingAverage.coef
  split_ifs with h
  · exact trunc_of_le (by omega)
  · rfl

/-! ### The candidate spectral tail process -/

/-- The law of the index `J ∈ ℕ` of the big jump: `P(J = j) = ψ_j^α / ∑_i ψ_i^α`. -/
noncomputable def indexLaw (ψ : ℕ → ℝ) (α : ℝ) : Measure ℕ :=
  Measure.sum fun j => ENNReal.ofReal (ψ j ^ α / ∑' i, ψ i ^ α) • Measure.dirac j

/-- The spectral tail process `Θ_t = ψ_{J+t} / ψ_J`, on the index space `ℕ` of `J`. -/
noncomputable def spectral (ψ : ℕ → ℝ) (t : ℤ) (j : ℕ) : ℝ :=
  MovingAverage.coef ψ (j + t) / ψ j

theorem indexLaw_apply (s : Set ℕ) :
    indexLaw ψ α s = ∑' j, ENNReal.ofReal (ψ j ^ α / ∑' i, ψ i ^ α) * s.indicator 1 j := by
  rw [indexLaw, Measure.sum_apply _ (MeasurableSet.of_discrete)]
  simp

theorem indexLaw_singleton (j : ℕ) :
    indexLaw ψ α {j} = ENNReal.ofReal (ψ j ^ α / ∑' i, ψ i ^ α) := by
  rw [indexLaw_apply, tsum_eq_single j fun i hi => by simp [hi]]
  simp

theorem indexLaw_isProbabilityMeasure (hψ0 : ∀ j, 0 ≤ ψ j) (hS : Summable fun j => ψ j ^ α)
    (hW : 0 < ∑' j, ψ j ^ α) : IsProbabilityMeasure (indexLaw ψ α) := by
  constructor
  rw [indexLaw_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => div_nonneg (Real.rpow_nonneg (hψ0 j) _) hW.le)
    (hS.div_const _), tsum_div_const, div_self hW.ne', ENNReal.ofReal_one]

/-- Under `indexLaw`, `ψ_J > 0` almost surely. -/
theorem ae_indexLaw_pos (hα : 0 < α) (hψ0 : ∀ j, 0 ≤ ψ j) :
    ∀ᵐ j ∂indexLaw ψ α, 0 < ψ j := by
  rw [ae_iff, indexLaw_apply, ENNReal.tsum_eq_zero]
  intro j
  by_cases h : 0 < ψ j
  · simp [h]
  · have : ψ j = 0 := le_antisymm (not_lt.1 h) (hψ0 j)
    simp [this, Real.zero_rpow hα.ne']

theorem integral_indexLaw (hψ0 : ∀ j, 0 ≤ ψ j) (hS : Summable fun j => ψ j ^ α)
    (hW : 0 < ∑' j, ψ j ^ α) {f : ℕ → ℝ} {C : ℝ} (hf : ∀ j, |f j| ≤ C) :
    ∫ j, f j ∂indexLaw ψ α = ∑' j, ψ j ^ α / (∑' i, ψ i ^ α) * f j := by
  have := indexLaw_isProbabilityMeasure hψ0 hS hW
  rw [integral_countable (integrable_of_abs_le measurable_from_top hf)]
  refine tsum_congr fun j => ?_
  rw [measureReal_def, indexLaw_singleton, ENNReal.toReal_ofReal
    (div_nonneg (Real.rpow_nonneg (hψ0 j) _) hW.le), smul_eq_mul]

/-! ### Convergence of the window laws of the tail processes -/

theorem abs_integral_pareto_le (hα : 0 < α) {S : Finset ℤ} (g : (S → ℝ) →ᵇ ℝ) (θ : S → ℝ) :
    |∫ r, g (fun t => r * θ t) ∂paretoMeasure 1 α| ≤ ‖g‖ := by
  have := isProbabilityMeasure_paretoMeasure one_pos hα
  have h := norm_integral_le_of_norm_le_const (μ := paretoMeasure 1 α)
    (f := fun r => g (fun t => r * θ t)) (Eventually.of_forall fun r => g.norm_coe_le_norm _)
  simpa using h

theorem tendsto_weightSum (hS : Summable fun j => ψ j ^ α) :
    Tendsto (fun m => MovingAverage.weightSum m ψ α) atTop (𝓝 (∑' j, ψ j ^ α)) :=
  hS.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem weightSum_le_tsum (hψ0 : ∀ j, 0 ≤ ψ j) (hS : Summable fun j => ψ j ^ α) (m : ℕ) :
    MovingAverage.weightSum m ψ α ≤ ∑' j, ψ j ^ α :=
  hS.sum_le_tsum _ fun j _ => Real.rpow_nonneg (hψ0 j) _

theorem weightSum_mono (hψ0 : ∀ j, 0 ≤ ψ j) {k m : ℕ} (h : k ≤ m) :
    MovingAverage.weightSum k ψ α ≤ MovingAverage.weightSum m ψ α :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    fun j _ _ => Real.rpow_nonneg (hψ0 j) _

/-- **The window laws of the tail processes of the truncations converge**: the law of
`(R Θ^{(m)}_t)_{t ∈ S}` converges to that of `(R Θ_t)_{t ∈ S}` as `m → ∞`. -/
theorem tendsto_integral_window (hα : 0 < α) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hS : Summable fun j => ψ j ^ α) {k : ℕ} (hk : 0 < ψ k) (S : Finset ℤ)
    (g : (S → ℝ) →ᵇ ℝ) :
    Tendsto (fun m => ∫ y, g y ∂(((paretoMeasure 1 α).prod
        (MovingAverage.indexLaw m (trunc m ψ) α)).map
          fun p (t : S) => p.1 * MovingAverage.spectral m (trunc m ψ) t p.2)) atTop
      (𝓝 (∫ y, g y ∂(((paretoMeasure 1 α).prod (indexLaw ψ α)).map
          fun p (t : S) => p.1 * spectral ψ t p.2))) := by
  have hP := isProbabilityMeasure_paretoMeasure one_pos hα
  set W := ∑' j, ψ j ^ α with hW_def
  have hkα : 0 < ψ k ^ α := Real.rpow_pos_of_pos hk _
  have hW : 0 < W := hkα.trans_le (hS.le_tsum k fun j _ => Real.rpow_nonneg (hψ0 j) _)
  have hQ := indexLaw_isProbabilityMeasure hψ0 hS hW
  set H : (S → ℝ) → ℝ := fun θ => ∫ r, g (fun t => r * θ t) ∂paretoMeasure 1 α with hH_def
  have hH : ∀ θ, |H θ| ≤ ‖g‖ := abs_integral_pareto_le hα g
  have hgb : ∀ y, |g y| ≤ ‖g‖ := fun y => by
    simpa [Real.norm_eq_abs] using g.norm_coe_le_norm y
  -- the limit
  have hlim : ∫ y, g y ∂(((paretoMeasure 1 α).prod (indexLaw ψ α)).map
      fun p (t : S) => p.1 * spectral ψ t p.2) =
      ∑' j, ψ j ^ α / W * H (fun t => spectral ψ t j) := by
    have hmeas : Measurable fun p : ℝ × ℕ => fun t : S => p.1 * spectral ψ t p.2 :=
      measurable_pi_iff.2 fun t => measurable_fst.mul
        ((measurable_from_top (f := fun j : ℕ => spectral ψ t j)).comp measurable_snd)
    rw [integral_map hmeas.aemeasurable g.continuous.aestronglyMeasurable,
      integral_prod_symm (fun p : ℝ × ℕ => g (fun t => p.1 * spectral ψ t p.2))
        (integrable_of_abs_le (g.continuous.measurable.comp hmeas) fun p => hgb _)]
    show ∫ j, H (fun t => spectral ψ t j) ∂indexLaw ψ α = _
    exact integral_indexLaw hψ0 hS hW (fun j => hH _)
  rw [hlim]
  -- a bound for the window
  obtain ⟨N, hN⟩ := S.exists_le
  -- the finite terms
  set F : ℕ → ℕ → ℝ := fun m j => if j ≤ m then
    ψ j ^ α / MovingAverage.weightSum m ψ α *
      H (fun t => MovingAverage.coef (trunc m ψ) (j + t) / ψ j) else 0 with hF_def
  have hfin : ∀ m ≥ k, ∫ y, g y ∂(((paretoMeasure 1 α).prod
      (MovingAverage.indexLaw m (trunc m ψ) α)).map
        fun p (t : S) => p.1 * MovingAverage.spectral m (trunc m ψ) t p.2) = ∑' j, F m j := by
    intro m hm
    have hWm : 0 < MovingAverage.weightSum m (trunc m ψ) α := by
      rw [weightSum_trunc]
      exact hkα.trans_le (Finset.single_le_sum (f := fun j => ψ j ^ α)
        (fun j _ => Real.rpow_nonneg (hψ0 j) _) (Finset.mem_range.2 (by omega)))
    have := MovingAverage.indexLaw_isProbabilityMeasure (trunc_nonneg hψ0 m) hWm
    have hmeas : Measurable fun p : ℝ × Fin (m + 1) =>
        fun t : S => p.1 * MovingAverage.spectral m (trunc m ψ) t p.2 :=
      measurable_pi_iff.2 fun t => measurable_fst.mul ((measurable_from_top
        (f := fun j : Fin (m + 1) => MovingAverage.spectral m (trunc m ψ) t j)).comp measurable_snd)
    rw [integral_map hmeas.aemeasurable g.continuous.aestronglyMeasurable,
      integral_prod_symm (fun p : ℝ × Fin (m + 1) =>
        g (fun t => p.1 * MovingAverage.spectral m (trunc m ψ) t p.2))
        (integrable_of_abs_le (g.continuous.measurable.comp hmeas) fun p => hgb _)]
    show ∫ j, H (fun t => MovingAverage.spectral m (trunc m ψ) t j)
      ∂(MovingAverage.indexLaw m (trunc m ψ) α) = _
    rw [MovingAverage.indexLaw, integral_finsetSum_measure fun j _ =>
          (integrable_of_abs_le measurable_from_top (fun j => hH _)).smul_measure
            ENNReal.ofReal_ne_top]
    simp only [integral_smul_measure, integral_dirac, smul_eq_mul, MovingAverage.spectral]
    rw [Fin.sum_univ_eq_sum_range (fun j => (ENNReal.ofReal (trunc m ψ j ^ α /
        MovingAverage.weightSum m (trunc m ψ) α)).toReal *
        H (fun t => MovingAverage.coef (trunc m ψ) (j + t) / trunc m ψ j)) (m + 1),
      tsum_eq_sum (s := Finset.range (m + 1)) fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj
        simp [hF_def, show ¬ j ≤ m by omega]]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := by simp only [Finset.mem_range] at hj; omega
    simp only [hF_def, hjm, ↓reduceIte]
    rw [trunc_of_le hjm, weightSum_trunc, ENNReal.toReal_ofReal (div_nonneg
      (Real.rpow_nonneg (hψ0 j) _) (hWm.le.trans_eq (weightSum_trunc m)))]
  refine Tendsto.congr' (EventuallyEq.symm (eventually_atTop.2 ⟨k, hfin⟩)) ?_
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => ψ j ^ α /
    MovingAverage.weightSum k ψ α * ‖g‖) ((hS.div_const _).mul_right _) (fun j => ?_) ?_
  · -- pointwise convergence
    have hWk : 0 < MovingAverage.weightSum k ψ α := hkα.trans_le (Finset.single_le_sum
      (f := fun j => ψ j ^ α) (fun j _ => Real.rpow_nonneg (hψ0 j) _)
      (Finset.mem_range.2 (by omega)))
    have h1 : Tendsto (fun m => ψ j ^ α / MovingAverage.weightSum m ψ α *
        H (fun t => spectral ψ t j)) atTop (𝓝 (ψ j ^ α / W * H (fun t => spectral ψ t j))) :=
      (tendsto_const_nhds.div (tendsto_weightSum hS) hW.ne').mul_const _
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (j + N.toNat)] with m hm
    simp only [hF_def, show j ≤ m by omega, ↓reduceIte]
    congr 2
    funext t
    rw [spectral, coef_trunc (by have := hN t t.2; have := Int.self_le_toNat N; omega)]
  · -- domination
    filter_upwards [eventually_ge_atTop k] with m hm j
    have hWk : 0 < MovingAverage.weightSum k ψ α := hkα.trans_le (Finset.single_le_sum
      (f := fun j => ψ j ^ α) (fun j _ => Real.rpow_nonneg (hψ0 j) _)
      (Finset.mem_range.2 (by omega)))
    have hb0 : 0 ≤ ψ j ^ α / MovingAverage.weightSum k ψ α * ‖g‖ :=
      mul_nonneg (div_nonneg (Real.rpow_nonneg (hψ0 j) _) hWk.le) (norm_nonneg _)
    simp only [hF_def]
    split_ifs with hjm
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (Real.rpow_nonneg (hψ0 j) _)
        (hWk.le.trans (weightSum_mono hψ0 hm)))]
      exact mul_le_mul (div_le_div_of_nonneg_left (Real.rpow_nonneg (hψ0 j) _) hWk
        (weightSum_mono hψ0 hm)) (hH _) (abs_nonneg _) (div_nonneg (Real.rpow_nonneg (hψ0 j) _)
        hWk.le)
    · simpa using hb0

/-! ### Approximation by the truncations -/

section Approx

variable [IsProbabilityMeasure P]

/-- **Approximation of the windows**: for `ε, η > 0`, for large `m` and then large `x`, the
windows `(X_t / x)_{t ∈ S}` and `(X^{(m)}_t / x)_{t ∈ S}` are `ε`-close off an event `D` with
`P(B_x Δ B^m_x) + P(B_x ∩ D) ≤ η P(B_x)`, `B_x = {X_0 > x}`, `B^m_x = {X^{(m)}_0 > x}`. -/
theorem eventually_approx_of_summable_rpow (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) (S : Finset ℤ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ m in atTop, ∀ᶠ x in atTop, ∃ D : Set Ω, MeasurableSet D ∧
      (∀ ω ∉ D, dist (fun t : S => process ψ Z t ω / x)
        (fun t : S => MovingAverage.process m ψ Z t ω / x) ≤ ε) ∧
      P.real ({ω | x < |process ψ Z 0 ω|} \ {ω | x < |MovingAverage.process m ψ Z 0 ω|}) +
        P.real ({ω | x < |MovingAverage.process m ψ Z 0 ω|} \ {ω | x < |process ψ Z 0 ω|}) +
        P.real ({ω | x < |process ψ Z 0 ω|} ∩ D) ≤
        η * P.real {ω | x < |process ψ Z 0 ω|} := by
  have hα : 0 < α := hδ.trans hδα
  have hS := summable_rpow hψ0 hδ hδα.le hψ
  obtain ⟨k, hk⟩ := hpos
  set W := ∑' j, ψ j ^ α with hW_def
  have hW : 0 < W := (Real.rpow_pos_of_pos hk _).trans_le
    (hS.le_tsum k fun j _ => Real.rpow_nonneg (hψ0 j) _)
  set L : ℝ → ℝ := fun x => P.real {ω | x < Z 0 ω} with hL_def
  obtain ⟨K, x₀, m₀, hK, hx₀, hR⟩ :=
    exists_measureReal_abs_sub_gt_le_of_summable_rpow hZ hident hZ0 hδ hδα hδ1 hL hψ0 hψ
  set S' := insert (0 : ℤ) S with hS'
  set n : ℝ := (S'.card : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  -- the choice of `ε'`
  set c : ℝ → ℝ := fun e => (1 - e) ^ (-α) - (1 + e) ^ (-α) with hc_def
  have hc : ContinuousAt c 0 :=
    ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by norm_num))).sub
      ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num)))
  have hc0 : c 0 = 0 := by simp [hc_def]
  obtain ⟨ε', hcε, hε'0, hε'1⟩ : ∃ e, c e < η / 4 ∧ e ∈ Set.Ioo 0 (min ε 1) :=
    (((hc.eventually (gt_mem_nhds (show c 0 < η / 4 by rw [hc0]; positivity))).filter_mono
      nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (lt_min hε one_pos))).exists
  have hε'ε : ε' ≤ ε := hε'1.le.trans (min_le_left _ _)
  have hε'1' : ε' < 1 := hε'1.trans_le (min_le_right _ _)
  -- the choice of `m`
  set T : ℕ → ℝ := fun m => ∑' j, ψ (j + (m + 1)) ^ δ with hT_def
  have hT : Tendsto T atTop (𝓝 0) :=
    (tendsto_sum_nat_add fun j => ψ j ^ δ).comp (tendsto_add_atTop_nat 1)
  have hTsmall : ∀ᶠ m in atTop, 3 * n * K * T m * ε' ^ (-α) < η * W / 8 := by
    have : Tendsto (fun m => 3 * n * K * T m * ε' ^ (-α)) atTop
        (𝓝 (3 * n * K * 0 * ε' ^ (-α))) := ((hT.const_mul _).mul_const _)
    rw [mul_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hTsmall, eventually_ge_atTop m₀] with m hm hmm₀
  set Wm := MovingAverage.weightSum m ψ α with hWm_def
  have hWm0 : 0 ≤ Wm := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hψ0 j) _
  have hWmW : Wm ≤ W := weightSum_le_tsum hψ0 hS m
  have hFm := MovingAverage.tendsto_measureReal_process_div (m := m) (ψ := ψ) hZ hind hident hZ0
    hα hL hψ0
  have hdiff := (LinearProcess.tendsto_comp_mul_div hL hFm (show (0 : ℝ) < 1 - ε' by linarith)).sub
    (LinearProcess.tendsto_comp_mul_div hL hFm (show (0 : ℝ) < 1 + ε' by linarith))
  rw [← mul_sub] at hdiff
  have hWmc : Wm * c ε' < η * W / 4 := by
    rcases le_or_gt (c ε') 0 with h | h
    · have : Wm * c ε' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hWm0 h
      have : 0 < η * W / 4 := by positivity
      linarith
    · calc Wm * c ε' ≤ W * c ε' := mul_le_mul_of_nonneg_right hWmW h.le
        _ < W * (η / 4) := mul_lt_mul_of_pos_left hcε hW
        _ = η * W / 4 := by ring
  have hX := tendsto_measureReal_process_div_of_summable_rpow hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ
  have hDlim : Tendsto (fun x => 3 * n * K * T m * (L (ε' * x) / L x)) atTop
      (𝓝 (3 * n * K * T m * ε' ^ (-α))) := tendsto_const_nhds.mul (hL.2 ε' hε'0)
  filter_upwards [hdiff.eventually (gt_mem_nhds (show Wm * c ε' < Wm * c ε' + η * W / 8 by
      have : 0 < η * W / 8 := by positivity
      linarith)),
    hDlim.eventually (gt_mem_nhds hm), hX.eventually (lt_mem_nhds (show W / 2 < W by linarith)),
    hL.1, (tendsto_id.const_mul_atTop hε'0).eventually (eventually_ge_atTop x₀),
    eventually_gt_atTop 0] with x h1 h2 h3 hLx hx0' hx
  set X := process ψ Z with hX_def
  set Xm := MovingAverage.process m ψ Z with hXm_def
  have hXm0 : ∀ ω, 0 ≤ Xm 0 ω := MovingAverage.process_nonneg hψ0 hZ0 0
  have hX0 : ∀ ω, 0 ≤ X 0 ω := process_nonneg hψ0 hZ0 0
  set D := ⋃ t ∈ S', {ω | ε' * x < |X t ω - Xm t ω|} with hD_def
  have hDm : MeasurableSet D := Finset.measurableSet_biUnion S' fun t _ =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp
      ((measurable_process hZ t).sub (MovingAverage.measurable_process hZ t)))
  have hnotD : ∀ ω ∉ D, ∀ t ∈ S', |X t ω - Xm t ω| ≤ ε' * x := by
    intro ω hω t ht
    by_contra h
    exact hω (mem_biUnion ht (not_le.1 h))
  refine ⟨D, hDm, fun ω hω => ?_, ?_⟩
  · refine (dist_pi_le_iff hε.le).2 fun t => ?_
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hx, div_le_iff₀ hx]
    exact (hnotD ω hω t (Finset.mem_insert_of_mem t.2)).trans
      (mul_le_mul_of_nonneg_right hε'ε hx.le)
  -- the bound
  have habsX : ∀ y, {ω | y < |X 0 ω|} = {ω | y < X 0 ω} := fun y => by
    ext ω; simp [abs_of_nonneg (hX0 ω)]
  have habsXm : ∀ y, {ω | y < |Xm 0 ω|} = {ω | y < Xm 0 ω} := fun y => by
    ext ω; simp [abs_of_nonneg (hXm0 ω)]
  rw [habsX, habsXm]
  have hmeasXm : ∀ y, MeasurableSet {ω | y < Xm 0 ω} := fun y =>
    measurableSet_lt measurable_const (MovingAverage.measurable_process hZ 0)
  have hPD : P.real D ≤ n * (K * T m * L (ε' * x)) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun t _ => hR m hmm₀ t _ hx0').trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact le_rfl
  have h0S' : (0 : ℤ) ∈ S' := Finset.mem_insert_self 0 S
  have hsub1 : {ω | x < X 0 ω} \ {ω | x < Xm 0 ω} ⊆
      D ∪ ({ω | (1 - ε') * x < Xm 0 ω} \ {ω | x < Xm 0 ω}) := by
    rintro ω ⟨h1, h2⟩
    by_cases hω : ω ∈ D
    · exact Or.inl hω
    · refine Or.inr ⟨?_, h2⟩
      have := (abs_le.1 (hnotD ω hω 0 h0S')).2
      simp only [mem_ofPred_eq] at h1 ⊢
      linarith
  have hsub2 : {ω | x < Xm 0 ω} \ {ω | x < X 0 ω} ⊆
      D ∪ ({ω | x < Xm 0 ω} \ {ω | (1 + ε') * x < Xm 0 ω}) := by
    rintro ω ⟨h1, h2⟩
    by_cases hω : ω ∈ D
    · exact Or.inl hω
    · refine Or.inr ⟨h1, ?_⟩
      have := (abs_le.1 (hnotD ω hω 0 h0S')).1
      simp only [mem_ofPred_eq, not_lt] at h2 ⊢
      linarith
  have hd1 : P.real ({ω | (1 - ε') * x < Xm 0 ω} \ {ω | x < Xm 0 ω}) =
      P.real {ω | (1 - ε') * x < Xm 0 ω} - P.real {ω | x < Xm 0 ω} :=
    measureReal_sdiff (fun ω (h : x < Xm 0 ω) => (show (1 - ε') * x < Xm 0 ω by nlinarith))
      (hmeasXm x)
  have hd2 : P.real ({ω | x < Xm 0 ω} \ {ω | (1 + ε') * x < Xm 0 ω}) =
      P.real {ω | x < Xm 0 ω} - P.real {ω | (1 + ε') * x < Xm 0 ω} :=
    measureReal_sdiff (fun ω (h : (1 + ε') * x < Xm 0 ω) => (show x < Xm 0 ω by nlinarith))
      (hmeasXm _)
  have hb1 := (measureReal_mono (μ := P) hsub1 (measure_ne_top _ _)).trans
    (measureReal_union_le _ _)
  have hb2 := (measureReal_mono (μ := P) hsub2 (measure_ne_top _ _)).trans
    (measureReal_union_le _ _)
  have hb3 : P.real ({ω | x < X 0 ω} ∩ D) ≤ P.real D :=
    measureReal_mono Set.inter_subset_right (measure_ne_top _ _)
  rw [hd1] at hb1
  rw [hd2] at hb2
  -- the limits, in multiplied form
  rw [← sub_div, div_lt_iff₀ hLx] at h1
  rw [← mul_div_assoc, div_lt_iff₀ hLx] at h2
  rw [lt_div_iff₀ hLx] at h3
  have h4 := mul_lt_mul_of_pos_left h3 hη
  have h5 : n * (K * T m * L (ε' * x)) = 3 * n * K * T m * L (ε' * x) / 3 := by ring
  have hL0 : 0 < L x := hLx
  nlinarith

/-! ### The tail process and the spectral tail process -/

/-- **The tail process of an infinite moving average, all `α > 0`** ([DR85], [KS20, §15.3]):
under the hypotheses of `hasExtremalIndex_of_summable_rpow`, `X_t = ∑_j ψ_j Z_{t-j}` has tail process
`Y_t = R Θ_t`, with `R` Pareto(`α`) independent of `J`, `Θ_t = ψ_{J+t} / ψ_J`,
`P(J = j) = ψ_j^α / ∑_i ψ_i^α`. -/
theorem hasTailProcess_of_summable_rpow (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasTailProcess P (process ψ Z) α ((paretoMeasure 1 α).prod (indexLaw ψ α))
      (fun t p => p.1 * spectral ψ t p.2) := by
  have hα : 0 < α := hδ.trans hδα
  have hS := summable_rpow hψ0 hδ hδα.le hψ
  obtain ⟨k, hk⟩ := hpos
  have hkα : 0 < ψ k ^ α := Real.rpow_pos_of_pos hk _
  have hW : 0 < ∑' j, ψ j ^ α := hkα.trans_le (hS.le_tsum k fun j _ => Real.rpow_nonneg (hψ0 j) _)
  have hP := isProbabilityMeasure_paretoMeasure one_pos hα
  have hQ := indexLaw_isProbabilityMeasure hψ0 hS hW
  have hθ0 : ∀ j, 0 < ψ j → spectral ψ 0 j = 1 := fun j hj => by
    simp [spectral, hj.ne']
  constructor
  · have hae : ∀ᵐ p ∂((paretoMeasure 1 α).prod (indexLaw ψ α)), |p.1 * spectral ψ 0 p.2| = p.1 := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure,
        Measure.quasiMeasurePreserving_snd.ae (ae_indexLaw_pos hα hψ0)] with p h1 h2
      rw [hθ0 _ h2, mul_one, abs_of_pos (one_pos.trans h1)]
    rw [Measure.map_congr hae]
    simp
  intro S
  -- the finite tail processes
  have hfinTP : ∀ m ≥ k, HasTailProcess P (MovingAverage.process m ψ Z) α
      ((paretoMeasure 1 α).prod (MovingAverage.indexLaw m (trunc m ψ) α))
      (fun t p => p.1 * MovingAverage.spectral m (trunc m ψ) t p.2) := by
    intro m hm
    have hWm : 0 < MovingAverage.weightSum m (trunc m ψ) α := by
      rw [weightSum_trunc]
      exact hkα.trans_le (Finset.single_le_sum (f := fun j => ψ j ^ α)
        (fun j _ => Real.rpow_nonneg (hψ0 j) _) (Finset.mem_range.2 (by omega)))
    have := MovingAverage.indexLaw_isProbabilityMeasure (trunc_nonneg hψ0 m) hWm
    have h := (MovingAverage.hasSpectralTailProcess hZ hind hident hZ0 hα hL
      (trunc_nonneg hψ0 m) (fun j hj => trunc_of_lt hj) hWm).hasTailProcess hα
      (MovingAverage.measurable_process hZ) (fun t => measurable_from_top)
    rwa [process_trunc] at h
  -- positivity of `P(X_0 > x)`
  have hX := tendsto_measureReal_process_div_of_summable_rpow hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ
  have hBpos : ∀ᶠ x in atTop, 0 < P.real {ω | x < |process ψ Z 0 ω|} := by
    filter_upwards [hX.eventually (lt_mem_nhds hW), hL.1] with x hx hLx
    have : {ω | x < |process ψ Z 0 ω|} = {ω | x < process ψ Z 0 ω} := by
      ext ω; simp [abs_of_nonneg (process_nonneg hψ0 hZ0 0 ω)]
    rw [this]
    exact (div_pos_iff_of_pos_right hLx).1 hx
  refine tendstoLawCond_of_approx (Bm := fun m x => {ω | x < |MovingAverage.process m ψ Z 0 ω|})
    (Vm := fun m x ω (t : S) => MovingAverage.process m ψ Z t ω / x)
    (fun x => measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (measurable_process hZ 0)))
    (fun m x => measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (MovingAverage.measurable_process hZ 0)))
    (fun x => measurable_pi_iff.2 fun t => (measurable_process hZ t).div_const x)
    (fun m x => measurable_pi_iff.2 fun t => (MovingAverage.measurable_process hZ t).div_const x)
    hBpos ?_ (tendsto_integral_window hα hψ0 hS hk S) fun ε hε η hη =>
      eventually_approx_of_summable_rpow hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ ⟨k, hk⟩ S hε hη
  filter_upwards [eventually_ge_atTop k] with m hm
  exact (hfinTP m hm).2 S

/-- **The spectral tail process of an infinite moving average, all `α > 0`** ([DR85],
[KS20, §15.3], [Meinguet–Segers 2010]). Let `(Z_i)_{i ∈ ℤ}` be iid nonnegative with
`P(Z_0 > x)` regularly varying with index `-α`, `α > 0`, let `0 < δ < α` with `δ < 1`, and let
`ψ_j ≥ 0`, not all zero, with `∑ ψ_j^δ < ∞`. Then `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` has spectral
tail process `Θ_t = ψ_{J+t} / ψ_J`, `P(J = j) = ψ_j^α / ∑_i ψ_i^α`, `J ∈ ℕ`. -/
theorem hasSpectralTailProcess_of_summable_rpow (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasSpectralTailProcess P (process ψ Z) α (indexLaw ψ α) (spectral ψ) := by
  have hα : 0 < α := hδ.trans hδα
  have hS := summable_rpow hψ0 hδ hδα.le hψ
  obtain ⟨k, hk⟩ := hpos
  have hW : 0 < ∑' j, ψ j ^ α := (Real.rpow_pos_of_pos hk _).trans_le
    (hS.le_tsum k fun j _ => Real.rpow_nonneg (hψ0 j) _)
  have hP := isProbabilityMeasure_paretoMeasure one_pos hα
  have hQ := indexLaw_isProbabilityMeasure hψ0 hS hW
  have h := (hasTailProcess_of_summable_rpow hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ
    ⟨k, hk⟩).hasSpectralTailProcess hα (measurable_process hZ) (fun t => measurable_fst.mul
      ((measurable_from_top (f := fun j : ℕ => spectral ψ t j)).comp measurable_snd))
  refine ⟨h.1, fun S => ?_⟩
  have hae : ∀ᵐ p ∂((paretoMeasure 1 α).prod (indexLaw ψ α)),
      (fun (t : S) => p.1 * spectral ψ t p.2 / |p.1 * spectral ψ 0 p.2|) =
        fun (t : S) => spectral ψ t p.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_one_lt_paretoMeasure,
      Measure.quasiMeasurePreserving_snd.ae (ae_indexLaw_pos hα hψ0)] with p h1 h2
    have h0 : spectral ψ 0 p.2 = 1 := by simp [spectral, h2.ne']
    funext t
    rw [h0, mul_one, abs_of_pos (one_pos.trans h1)]
    field_simp
  have e : ((paretoMeasure 1 α).prod (indexLaw ψ α)).map
      (fun p (t : S) => p.1 * spectral ψ t p.2 / |p.1 * spectral ψ 0 p.2|) =
      (indexLaw ψ α).map fun j (t : S) => spectral ψ t j := by
    rw [Measure.map_congr hae, show (fun p : ℝ × ℕ => fun t : S => spectral ψ t p.2) =
      (fun j (t : S) => spectral ψ t j) ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_from_top measurable_snd, Measure.map_snd_prod, measure_univ,
      one_smul]
  convert h.2 S using 1
  exact e.symm

/-! #### The case `α < 1` -/

/-- **Approximation of the windows** (`0 < δ < α < 1`): the case `α < 1` of
`eventually_approx_of_summable_rpow`. -/
theorem eventually_approx (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) (S : Finset ℤ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ m in atTop, ∀ᶠ x in atTop, ∃ D : Set Ω, MeasurableSet D ∧
      (∀ ω ∉ D, dist (fun t : S => process ψ Z t ω / x)
        (fun t : S => MovingAverage.process m ψ Z t ω / x) ≤ ε) ∧
      P.real ({ω | x < |process ψ Z 0 ω|} \ {ω | x < |MovingAverage.process m ψ Z 0 ω|}) +
        P.real ({ω | x < |MovingAverage.process m ψ Z 0 ω|} \ {ω | x < |process ψ Z 0 ω|}) +
        P.real ({ω | x < |process ψ Z 0 ω|} ∩ D) ≤
        η * P.real {ω | x < |process ψ Z 0 ω|} :=
  eventually_approx_of_summable_rpow hZ hind hident hZ0 hδ hδα (hδα.trans hα1) hL hψ0 hψ hpos S hε hη

/-- **The tail process of an infinite moving average** ([DR85], [KS20, §15.3]): under the
hypotheses of `hasExtremalIndex`, `X_t = ∑_j ψ_j Z_{t-j}` has tail process `Y_t = R Θ_t`, with
`R` Pareto(`α`) independent of `J`, `Θ_t = ψ_{J+t} / ψ_J`, `P(J = j) = ψ_j^α / ∑_i ψ_i^α`. The
case `α < 1` of `hasTailProcess_of_summable_rpow`. -/
theorem hasTailProcess (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasTailProcess P (process ψ Z) α ((paretoMeasure 1 α).prod (indexLaw ψ α))
      (fun t p => p.1 * spectral ψ t p.2) :=
  hasTailProcess_of_summable_rpow hZ hind hident hZ0 hδ hδα (hδα.trans hα1) hL hψ0 hψ hpos

/-- **The spectral tail process of an infinite moving average** ([DR85], [KS20, §15.3],
[Meinguet–Segers 2010]). Let `(Z_i)_{i ∈ ℤ}` be iid nonnegative with `P(Z_0 > x)` regularly
varying with index `-α`, `0 < δ < α < 1`, and let `ψ_j ≥ 0`, not all zero, with
`∑ ψ_j^δ < ∞`. Then `X_t = ∑_{j ≥ 0} ψ_j Z_{t-j}` has spectral tail process
`Θ_t = ψ_{J+t} / ψ_J`, `P(J = j) = ψ_j^α / ∑_i ψ_i^α`, `J ∈ ℕ`. The case `α < 1` of
`hasSpectralTailProcess_of_summable_rpow`. -/
theorem hasSpectralTailProcess (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasSpectralTailProcess P (process ψ Z) α (indexLaw ψ α) (spectral ψ) :=
  hasSpectralTailProcess_of_summable_rpow hZ hind hident hZ0 hδ hδα (hδα.trans hα1) hL hψ0 hψ hpos

end Approx

/-! ### The candidate extremal index -/

section Candidate

/-- The running supremum `R_n = sup_{i ≥ 0} ψ_{n+i}`. -/
noncomputable def runSup (ψ : ℕ → ℝ) (n : ℕ) : ℝ := ⨆ i, ψ (n + i)

variable (hψ0 : ∀ j, 0 ≤ ψ j) (hδ : 0 < δ) (hψ : Summable fun j => ψ j ^ δ)
include hψ0 hδ hψ

/-- The running supremum is attained. -/
theorem exists_runSup_eq (n : ℕ) : ∃ k, runSup ψ n = ψ (n + k) ∧ ∀ i, ψ (n + i) ≤ ψ (n + k) := by
  have hmax : ∃ k, ∀ i, ψ (n + i) ≤ ψ (n + k) := by
    by_cases h : ∃ i, 0 < ψ (n + i)
    · obtain ⟨k, -, hk⟩ := exists_forall_le (ψ := fun i => ψ (n + i)) (fun i => hψ0 _) hδ
        ((summable_nat_add_iff n).2 hψ |>.congr fun i => by rw [add_comm]) h
      exact ⟨k, hk⟩
    · push Not at h
      exact ⟨0, fun i => (h i).trans (hψ0 _)⟩
  obtain ⟨k, hk⟩ := hmax
  refine ⟨k, le_antisymm (ciSup_le hk) (le_ciSup (f := fun i => ψ (n + i))
    ⟨ψ (n + k), by rintro _ ⟨i, rfl⟩; exact hk i⟩ k), hk⟩

theorem le_runSup (n i : ℕ) : ψ (n + i) ≤ runSup ψ n := by
  obtain ⟨k, hk, hmax⟩ := exists_runSup_eq hψ0 hδ hψ n
  rw [hk]; exact hmax i

theorem runSup_nonneg (n : ℕ) : 0 ≤ runSup ψ n :=
  (hψ0 (n + 0)).trans (le_runSup hψ0 hδ hψ n 0)

theorem runSup_succ_le (n : ℕ) : runSup ψ (n + 1) ≤ runSup ψ n := by
  obtain ⟨k, hk, -⟩ := exists_runSup_eq hψ0 hδ hψ (n + 1)
  rw [hk, show n + 1 + k = n + (k + 1) by ring]
  exact le_runSup hψ0 hδ hψ n _

theorem runSup_eq_of_eq_zero {n : ℕ} (hn : ψ n = 0) : runSup ψ n = runSup ψ (n + 1) := by
  refine le_antisymm ?_ (runSup_succ_le hψ0 hδ hψ n)
  obtain ⟨k, hk, -⟩ := exists_runSup_eq hψ0 hδ hψ n
  rw [hk]
  rcases k with _ | k
  · rw [add_zero, hn]; exact runSup_nonneg hψ0 hδ hψ _
  · rw [show n + (k + 1) = n + 1 + k by ring]; exact le_runSup hψ0 hδ hψ _ _

theorem tendsto_runSup : Tendsto (runSup ψ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hψ.tendsto_atTop_zero).eventually
    (gt_mem_nhds (Real.rpow_pos_of_pos hε δ)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hk, -⟩ := exists_runSup_eq hψ0 hδ hψ n
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (runSup_nonneg hψ0 hδ hψ n), hk]
  have := hN (n + k) (by omega)
  rwa [Real.rpow_lt_rpow_iff (hψ0 _) hε.le hδ] at this

theorem iSup_ofReal_div (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ⨆ i : ℕ, ENNReal.ofReal (ψ (n + i) / c) = ENNReal.ofReal (runSup ψ n / c) := by
  refine le_antisymm (iSup_le fun i => ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (le_runSup hψ0 hδ hψ n i) hc.le)) ?_
  obtain ⟨k, hk, -⟩ := exists_runSup_eq hψ0 hδ hψ n
  rw [hk]
  exact le_iSup (fun i => ENNReal.ofReal (ψ (n + i) / c)) k

/-- **Candidate extremal index of an infinite moving average** ([DR85], [KS20, §15.3]): the
spectral tail process `Θ_t = ψ_{J+t} / ψ_J` has candidate extremal index
`ϑ = sup_j ψ_j^α / ∑_j ψ_j^α`. -/
theorem candidateExtremalIndex_spectral (hδα : δ ≤ α) (hpos : ∃ j, 0 < ψ j) :
    candidateExtremalIndex (indexLaw ψ α) (spectral ψ) α =
      ENNReal.ofReal ((⨆ j, ψ j) ^ α / ∑' j, ψ j ^ α) := by
  have hα : 0 < α := hδ.trans_le hδα
  have hS := summable_rpow hψ0 hδ hδα hψ
  obtain ⟨k, hk⟩ := hpos
  set W := ∑' j, ψ j ^ α with hW_def
  have hW : 0 < W := (Real.rpow_pos_of_pos hk _).trans_le
    (hS.le_tsum k fun j _ => Real.rpow_nonneg (hψ0 j) _)
  set R := runSup ψ with hR_def
  have hR0 : ∀ n, 0 ≤ R n := runSup_nonneg hψ0 hδ hψ
  have hRs : ∀ n, R (n + 1) ≤ R n := runSup_succ_le hψ0 hδ hψ
  have hterm : ∀ j : ℕ, ENNReal.ofReal (ψ j ^ α / W) *
      ((⨆ k : ℕ, ENNReal.ofReal |spectral ψ k j|) ^ α -
        (⨆ k : ℕ, ENNReal.ofReal |spectral ψ (k + 1) j|) ^ α) =
      ENNReal.ofReal ((R j ^ α - R (j + 1) ^ α) / W) := by
    intro j
    rcases (hψ0 j).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow hα.ne', zero_div, ENNReal.ofReal_zero, zero_mul,
        hR_def, runSup_eq_of_eq_zero hψ0 hδ hψ h0.symm, sub_self, zero_div, ENNReal.ofReal_zero]
    have h1 : ∀ k : ℕ, |spectral ψ k j| = ψ (j + k) / ψ j := fun k => by
      rw [spectral, show (j : ℤ) + (k : ℤ) = ((j + k : ℕ) : ℤ) by push_cast; ring,
        MovingAverage.coef_natCast, abs_of_nonneg (div_nonneg (hψ0 _) hpos.le)]
    have h2 : ∀ k : ℕ, |spectral ψ ((k : ℤ) + 1) j| = ψ (j + 1 + k) / ψ j := fun k => by
      rw [spectral, show (j : ℤ) + ((k : ℤ) + 1) = ((j + 1 + k : ℕ) : ℤ) by push_cast; ring,
        MovingAverage.coef_natCast, abs_of_nonneg (div_nonneg (hψ0 _) hpos.le)]
    simp only [h1, h2]
    rw [iSup_ofReal_div hψ0 hδ hψ _ hpos, iSup_ofReal_div hψ0 hδ hψ _ hpos,
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hR0 _) hpos.le) hα.le,
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hR0 _) hpos.le) hα.le,
      ← ENNReal.ofReal_sub _ (Real.rpow_nonneg (div_nonneg (hR0 _) hpos.le) _),
      ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg (hψ0 _) _) hW.le)]
    congr 1
    rw [Real.div_rpow (hR0 _) hpos.le, Real.div_rpow (hR0 _) hpos.le]
    have : 0 < ψ j ^ α := Real.rpow_pos_of_pos hpos _
    field_simp
  have hnn : ∀ j, 0 ≤ R j ^ α - R (j + 1) ^ α := fun j =>
    sub_nonneg.2 (Real.rpow_le_rpow (hR0 _) (hRs _) hα.le)
  -- telescoping
  have hsum : HasSum (fun j => R j ^ α - R (j + 1) ^ α) (R 0 ^ α) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    have hlim : Tendsto (fun n => R 0 ^ α - R n ^ α) atTop (𝓝 (R 0 ^ α - 0 ^ α)) :=
      tendsto_const_nhds.sub ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp
        (tendsto_runSup hψ0 hδ hψ))
    rw [Real.zero_rpow hα.ne', sub_zero] at hlim
    refine hlim.congr fun n => ?_
    rw [Finset.sum_range_sub']
  rw [candidateExtremalIndex, indexLaw, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac]
  refine (tsum_congr hterm).trans ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => div_nonneg (hnn j) hW.le)
      (hsum.summable.div_const _), tsum_div_const, hsum.tsum_eq]
  congr 3
  simp [hR_def, runSup]

end Candidate

/-- **`θ = ϑ` for infinite moving averages, all `α > 0`** ([DR85], [KS20, Chapter 15]): under
the hypotheses of `hasExtremalIndex_of_summable_rpow`, `X` has spectral tail process
`Θ_t = ψ_{J+t} / ψ_J`, and its extremal index is the candidate extremal index `ϑ` of `Θ`, namely
`sup_j ψ_j^α / ∑_j ψ_j^α`. -/
theorem hasSpectralTailProcess_and_hasExtremalIndex_of_summable_rpow [IsProbabilityMeasure P]
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hδ1 : δ < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasSpectralTailProcess P (process ψ Z) α (indexLaw ψ α) (spectral ψ) ∧
      HasExtremalIndex (fun n : ℕ => process ψ Z n) P
        (candidateExtremalIndex (indexLaw ψ α) (spectral ψ) α).toReal := by
  refine ⟨hasSpectralTailProcess_of_summable_rpow hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ hpos, ?_⟩
  rw [candidateExtremalIndex_spectral hψ0 hδ hψ hδα.le hpos, ENNReal.toReal_ofReal]
  · exact hasExtremalIndex_of_summable_rpow hZ hind hident hZ0 hδ hδα hδ1 hL hψ0 hψ hpos
  · obtain ⟨k, hk⟩ := hpos
    exact div_nonneg (Real.rpow_nonneg ((hψ0 k).trans (le_ciSup (f := ψ)
      ⟨ψ (Classical.choose (exists_forall_le hψ0 hδ hψ ⟨k, hk⟩)), by
        rintro _ ⟨j, rfl⟩
        exact (Classical.choose_spec (exists_forall_le hψ0 hδ hψ ⟨k, hk⟩)).2 j⟩ k)) _)
      (tsum_nonneg fun j => Real.rpow_nonneg (hψ0 j) _)

/-- **`θ = ϑ` for infinite moving averages** ([DR85], [KS20, Chapter 15]): under the hypotheses
of `hasExtremalIndex`, `X` has spectral tail process `Θ_t = ψ_{J+t} / ψ_J`, and its extremal index
is the candidate extremal index `ϑ` of `Θ`, namely `sup_j ψ_j^α / ∑_j ψ_j^α`. The case `α < 1`
of `hasSpectralTailProcess_and_hasExtremalIndex_of_summable_rpow`. -/
theorem hasSpectralTailProcess_and_hasExtremalIndex [IsProbabilityMeasure P]
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω) (hδ : 0 < δ)
    (hδα : δ < α) (hα1 : α < 1)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-α)) (hψ0 : ∀ j, 0 ≤ ψ j)
    (hψ : Summable fun j => ψ j ^ δ) (hpos : ∃ j, 0 < ψ j) :
    HasSpectralTailProcess P (process ψ Z) α (indexLaw ψ α) (spectral ψ) ∧
      HasExtremalIndex (fun n : ℕ => process ψ Z n) P
        (candidateExtremalIndex (indexLaw ψ α) (spectral ψ) α).toReal :=
  hasSpectralTailProcess_and_hasExtremalIndex_of_summable_rpow hZ hind hident hZ0 hδ hδα
    (hδα.trans hα1) hL hψ0 hψ hpos

end InfiniteMovingAverage

end ExtremeValueTheory

/-! ### Deprecated names -/

namespace ExtremeValueTheory.InfiniteMovingAverage

@[deprecated (since := "2026-10-23")] alias eventually_approx_of_lt_one := eventually_approx_of_summable_rpow
@[deprecated (since := "2026-10-23")] alias hasTailProcess_of_lt_one := hasTailProcess_of_summable_rpow
@[deprecated (since := "2026-10-23")] alias hasSpectralTailProcess_of_lt_one := hasSpectralTailProcess_of_summable_rpow
@[deprecated (since := "2026-10-23")] alias hasSpectralTailProcess_and_hasExtremalIndex_of_lt_one := hasSpectralTailProcess_and_hasExtremalIndex_of_summable_rpow

end ExtremeValueTheory.InfiniteMovingAverage
