import ExtremeValueTheory

/-! # Known answers: dependence

Extremal indices, spectral tail processes, mixing coefficients and stochastic recurrences of
`ExtremeValueTheory/Dependence` evaluated on examples with a textbook answer.

References: [EKM] Embrechts, Klüppelberg, Mikosch, *Modelling Extremal Events* (1997);
[LLR] Leadbetter, Lindgren, Rootzén, *Extremes and Related Properties of Random Sequences and
Processes* (1983); [KS20] Kulik, Soulier, *Heavy-Tailed Time Series* (2020); [BDM16] Buraczewski,
Damek, Mikosch, *Stochastic Models with Power-Law Tails* (2016); [Bra05] Bradley, *Basic properties
of strong mixing conditions*, Probab. Surveys 2 (2005).
-/

open ExtremeValueTheory MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal

namespace Test.KnownAnswers.Dependence

/-! ### The candidate extremal index `ϑ = E[sup_{k≥0} |Θ_k|^α - sup_{k≥1} |Θ_k|^α]` -/

/-- **iid**: the spectral tail process is `Θ_t = 1{t = 0}` and `ϑ = 1` ([KS20, Example 5.2.4]).
Computed from the definition of `candidateExtremalIndex`, not from a library lemma. -/
theorem test_candidateExtremalIndex_iid :
    candidateExtremalIndex (Measure.dirac ()) unitSpectral 2 = 1 := by
  have h0 : (⨆ k : ℕ, ENNReal.ofReal |unitSpectral k ()|) = 1 := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0 (by simp [unitSpectral]))
    unfold unitSpectral; split_ifs <;> simp
  have h1 : (⨆ k : ℕ, ENNReal.ofReal |unitSpectral (k + 1) ()|) = 0 :=
    ENNReal.iSup_eq_zero.2 fun k => by simp [unitSpectral]; omega
  rw [candidateExtremalIndex, lintegral_dirac, h0, h1]
  simp

/-- The tail process of an iid sequence vanishes off time `0`. -/
example (t : ℤ) (ht : t ≠ 0) : unitSpectral t () = 0 := by simp [unitSpectral, ht]

/-- **Moving maximum** `X_t = max(Z_t, Z_{t+1})`: `Θ` is `(Θ_{-1}, Θ_0, Θ_1) = (1, 1, 0)` or
`(0, 1, 1)` with probability `1/2` each, and `θ = ϑ = 1/2` ([EKM, Example 8.1.10], [KS20, Example
5.2.10]). -/
theorem test_movingMaxSpectral :
    (movingMaxSpectral (-1) true, movingMaxSpectral 0 true, movingMaxSpectral 1 true) = (1, 1, 0) ∧
    (movingMaxSpectral (-1) false, movingMaxSpectral 0 false, movingMaxSpectral 1 false) =
      (0, 1, 1) := by
  simp [movingMaxSpectral, movingMaxPeak]

example : candidateExtremalIndex fairCoin movingMaxSpectral 3 = 2⁻¹ :=
  candidateExtremalIndex_movingMax (by norm_num)

/-- **Finite moving average** `X_t = ∑_{j ≤ m} ψ_j Z_{t-j}` with nonnegative coefficients:
`θ = max_j ψ_j^α / ∑_j ψ_j^α` ([EKM, §8.1, Example 8.1.13 / (8.13)], [KS20, §15.3]).
With `ψ = (1, 1)` (`m = 1`) and `α = 1`: `θ = 1/2`. -/
theorem test_movingAverage_equal_weights :
    candidateExtremalIndex (MovingAverage.indexLaw 1 (fun j => if j ≤ 1 then 1 else 0) 1)
      (MovingAverage.spectral 1 (fun j => if j ≤ 1 then 1 else 0)) 1 = ENNReal.ofReal (1 / 2) := by
  have hS : MovingAverage.weightSum 1 (fun j : ℕ => if j ≤ 1 then (1 : ℝ) else 0) 1 = 2 := by
    simp only [MovingAverage.weightSum, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
  rw [MovingAverage.candidateExtremalIndex_spectral one_pos (fun j => by split_ifs <;> norm_num)
    (fun j hj => by simp [Nat.not_le.2 hj]) (by rw [hS]; norm_num), hS]
  congr 1
  simp [Finset.sup'_insert, Finset.range_add_one]

/-- With `ψ = (1, 1/2)` and `α = 2`: `θ = 1 / (1 + 1/4) = 4/5`. -/
theorem test_movingAverage_unequal_weights :
    candidateExtremalIndex
        (MovingAverage.indexLaw 1 (fun j => if j = 0 then 1 else if j = 1 then 1 / 2 else 0) 2)
        (MovingAverage.spectral 1 (fun j => if j = 0 then 1 else if j = 1 then 1 / 2 else 0)) 2 =
      ENNReal.ofReal (4 / 5) := by
  set ψ : ℕ → ℝ := fun j => if j = 0 then 1 else if j = 1 then 1 / 2 else 0 with hψ
  have hS : MovingAverage.weightSum 1 ψ 2 = 5 / 4 := by
    simp [MovingAverage.weightSum, Finset.sum_range_succ, hψ]; norm_num
  have hψ0 : ∀ j, 0 ≤ ψ j := fun j => by simp only [hψ]; split_ifs <;> norm_num
  have hψm : ∀ j, 1 < j → ψ j = 0 := fun j hj => by
    simp only [hψ, show j ≠ 0 by omega, show j ≠ 1 by omega, ↓reduceIte]
  rw [MovingAverage.candidateExtremalIndex_spectral two_pos hψ0 hψm (by rw [hS]; norm_num), hS]
  congr 1
  simp [Finset.sup'_insert, Finset.range_add_one, hψ]
  norm_num

/-- `Θ_0 = 1` for the moving-average spectral process (`ψ_J ≠ 0`), and `Θ_t = 0` before the
start of the window. -/
example : MovingAverage.spectral 1 (fun _ => 3) 0 0 = 1 ∧
    MovingAverage.spectral 1 (fun _ => 3) (-1) 0 = 0 := by
  constructor <;> norm_num [MovingAverage.spectral, MovingAverage.coef]

/-- **Mixture** of a constant sequence (probability `p`) and an iid sequence: `ϑ = 1 - p`
([KS20, Example 5.4.4]); with `p = 1/4`, `ϑ = 3/4`. -/
example : candidateExtremalIndex (mixtureCoin (1 / 4)) mixtureSpectral 1 = ENNReal.ofReal (3 / 4) := by
  rw [candidateExtremalIndex_mixture one_pos]; norm_num

/-! ### Extremal index: statement-level checks of the formulas -/

/-- **iid sequences have extremal index `1`** ([LLR, §3.7], [EKM, §8.1]). -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hX : ∀ t, Measurable (X t)) (hind : iIndepFun X P)
    (hid : ∀ t, IdentDistrib (X t) (X 0) P P) : HasExtremalIndex X P 1 :=
  hasExtremalIndex_one_of_iIndepFun hX hind hid

/-- **AR(1)** `X_t = φ X_{t-1} + Z_t` with `φ ∈ (0, 1)` and `Z` regularly varying with index `α`:
`θ = 1 - φ^α` ([EKM, Example 8.1.12, (8.11)], Chernick 1981); for `φ = 1/2`, `α = 1`: `θ = 1/2`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℤ → Ω → ℝ} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hZ0 : ∀ i ω, 0 ≤ Z i ω)
    (hL : IsRegularlyVarying (fun x => P.real {ω | x < Z 0 ω}) (-1)) :
    HasExtremalIndex (fun n : ℕ => AR1.process (1 / 2) Z n) P (1 / 2) := by
  have := AR1.hasExtremalIndex_of_pos (φ := 1 / 2) hZ hind hident hZ0 one_pos hL (by norm_num)
    (by norm_num)
  norm_num at this ⊢
  exact this

/-- The AR(1) series `X_t = ∑_j φ^j Z_{t-j}`: with constant noise `Z ≡ c`, `X_t = c / (1 - φ)`;
for `φ = 1/2`, `c = 1`: `X_t = 2`. Checks the indexing of the causal representation. -/
theorem test_AR1_process_const (t : ℤ) :
    AR1.process (1 / 2) (fun _ (_ : Unit) => (1 : ℝ)) t () = 2 := by
  simp only [AR1.process, InfiniteMovingAverage.process, mul_one]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- The ARMAX transition is `x ↦ max(φ x, z)` ([EKM, Example 8.1.14], Davis–Resnick 1989). -/
example : ARMAX.step (1 / 2) 4 1 = 2 ∧ ARMAX.step (1 / 2) 4 3 = 3 := by
  norm_num [ARMAX.step]

/-! ### Mixing coefficients -/

/-- The strong mixing coefficient is `α(𝓐, 𝓑) = sup |P(A ∩ B) - P(A) P(B)|`, which for the fair
coin with `A = B = {heads}` is at least `1/2 - 1/4 = 1/4` ([Bra05, (1.1)]; `α ≤ 1/4` always).
A definition through conditional probabilities `|P(A | B) - P(A)|` would give `1/2` instead. -/
theorem test_strongMixingCoeff_fairCoin :
    ENNReal.ofReal (1 / 4) ≤ strongMixingCoeff (inferInstance : MeasurableSpace Bool)
      (inferInstance : MeasurableSpace Bool) fairCoin := by
  have h := ofReal_le_strongMixingCoeff (μ := fairCoin)
    (m₁ := (inferInstance : MeasurableSpace Bool)) (m₂ := (inferInstance : MeasurableSpace Bool))
    (A := {true}) (B := {true}) (measurableSet_singleton _) (measurableSet_singleton _)
  have hP : fairCoin.real {true} = 1 / 2 := by
    simp [fairCoin, Measure.real, ENNReal.toReal_inv]
  rw [Set.inter_self, hP] at h
  convert h using 2
  norm_num

/-- Independent σ-algebras have strong mixing coefficient `0`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {m₁ m₂ : MeasurableSpace Ω}
    (h : Indep m₁ m₂ μ) : strongMixingCoeff m₁ m₂ μ = 0 :=
  strongMixingCoeff_eq_zero_of_indep h

/-- An `m`-dependent sequence has `α(h) = β(h) = 0` for every lag `h > m` ([Bra05, §1]). -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : IsMDependent X 2 μ) : alphaMixing X μ 3 = 0 ∧ betaMixing X μ 3 = 0 :=
  ⟨hX.alphaMixing_eq_zero (by norm_num), hX.betaMixing_eq_zero (by norm_num)⟩

/-! ### Stochastic recurrence equations and GARCH(1,1) -/

/-- The perpetuity `∑_k A_0 ⋯ A_{k-1} B_k` with constant coefficients `(a, b)`, `0 ≤ a < 1`, is
`b / (1 - a)`, the fixed point of `x = a x + b` ([BDM16, §2.1], Vervaat 1979). -/
theorem test_perpetuity_const {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    SRE.perpetuity (fun _ => (a, b)) = b / (1 - a) := by
  simp only [SRE.perpetuity, SRE.term, Finset.prod_const, Finset.card_range]
  rw [tsum_mul_right, tsum_geometric_of_lt_one ha0 ha1, div_eq_inv_mul]

/-- **GARCH(1,1)**: `σ²_{t+1} = α₀ + (α₁ Z_t² + β₁) σ²_t` is the SRE with `A = α₁ Z² + β₁`,
`B = α₀` ([BDM16, §4.3], Bollerslev 1986). -/
example (α₀ α₁ β₁ z x : ℝ) :
    SRE.GARCH.coeff α₁ β₁ z = α₁ * z ^ 2 + β₁ ∧
      SRE.affine x (SRE.GARCH.innov α₀ α₁ β₁ z) = α₀ + (α₁ * z ^ 2 + β₁) * x :=
  ⟨rfl, SRE.GARCH.affine_innov α₀ α₁ β₁ x z⟩

/-- With degenerate innovations `Z ≡ ±1` the GARCH(1,1) stationary squared volatility is the
textbook unconditional variance `α₀ / (1 - α₁ - β₁)` (Bollerslev 1986). -/
theorem test_garch_unconditional_variance {α₀ α₁ β₁ : ℝ} (h1 : 0 ≤ α₁) (h2 : 0 ≤ β₁)
    (h : α₁ + β₁ < 1) :
    SRE.perpetuity (fun _ => SRE.GARCH.innov α₀ α₁ β₁ 1) = α₀ / (1 - α₁ - β₁) := by
  simp only [SRE.GARCH.innov, SRE.GARCH.coeff, one_pow, mul_one]
  rw [test_perpetuity_const (by positivity) h, sub_sub]

end Test.KnownAnswers.Dependence
