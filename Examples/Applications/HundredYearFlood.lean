import ExtremeValueTheory

/-!
# The 100-year flood

**The problem.** A river's daily peak discharge is modelled above a threshold of `u = 1000` m³/s.
The excesses over the threshold are taken to follow a generalized Pareto law with shape `ξ = 1/4` and
scale `σ = 100` m³/s, and the threshold is exceeded on a proportion `ζ = 256/36500` of days, about
2.56 days a year. These numbers are illustrative, not fitted to any river. How high is the
100-year level, that is, the level exceeded on average once in `N = 36500` days? And how much can a
confidence interval from a fitted model be trusted?

**What a practitioner learns.** The level is `x_N = u + (σ/ξ)((Nζ)^ξ - 1) = 2200` m³/s, and
`ζ · P(excess > x_N - u) = 1/N` confirms that it means what it should. If the excesses really are this
GPD, the usual interval, maximum likelihood estimate plus or minus `z` standard errors with the
plug-in delta-method variance, has coverage tending to 95% as the number of excesses `n` grows.

**What the theorem does not say.**

* It assumes that the excesses are an **exact iid GPD sample**. Real excesses are at best approximately
  GPD above a finite threshold, and the error of that approximation is not accounted for.
* The **exceedance probability `ζ` is known**. In practice it is estimated, which adds uncertainty that
  this interval omits. The number of excesses `n` is not random here.
* It is **asymptotic**. It says nothing about coverage at any finite `n`, such as the few hundred
  excesses of a real record, and gives no rate.
* It says **nothing about threshold choice**: `u = 1000` is an input.
* Independence rules out the clustering of flood days, so nothing here covers declustering.
* The likelihood is maximized over a compact set `K` containing the truth in its interior, and the
  estimator is an exact maximizer. Whether a given optimizer finds it is a separate question.
* It says nothing about climate trends or any other non-stationarity.
-/

open Filter Topology Set MeasureTheory ProbabilityTheory
open ExtremeValueTheory

namespace Examples.Applications.HundredYearFlood

/-- The compact parameter set for `(ξ, σ)` over which the likelihood is maximized. -/
def K : Set (ℝ × ℝ) := Icc (-1 / 4 : ℝ) (3 / 4) ×ˢ Icc (50 : ℝ) 200

/-- `K` is compact. -/
theorem isCompact_K : IsCompact K := isCompact_Icc.prod isCompact_Icc

/-- `K` lies in the admissible region `ξ > -1`, `σ > 0`. -/
theorem K_sub : ∀ p ∈ K, -1 < p.1 ∧ 0 < p.2 := by
  rintro ⟨a, b⟩ ⟨⟨ha, -⟩, ⟨hb, -⟩⟩
  exact ⟨by simp only at ha ⊢; linarith, by simp only at hb ⊢; linarith⟩

/-- The true parameter `(1/4, 100)` is interior to `K`. -/
theorem mem_interior_K : ((1 / 4 : ℝ), (100 : ℝ)) ∈ interior K := by
  rw [K, interior_prod_eq, interior_Icc, interior_Icc]
  exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- The exceedance probability per day. -/
noncomputable abbrev ζ : ℝ := 256 / 36500

/-- The 100-year level of the stated model is 2200 m³/s. -/
theorem returnLevel_eq : gpdReturnLevel 1000 (1 / 4) 100 ζ 36500 = 2200 := by
  rw [gpdReturnLevel_of_ne (by norm_num)]
  have h : (36500 * ζ : ℝ) ^ (1 / 4 : ℝ) = 4 := by
    rw [show (36500 * ζ : ℝ) = (4 : ℝ) ^ (4 : ℕ) by norm_num [ζ], ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h]
  norm_num

/-- That level is exceeded with probability `1/N` per day: the exceedance probability of the threshold
times the GPD survival function at `x_N - u`. -/
theorem exceedance_eq : ζ * gpdSurvivalAll (1 / 4) 100 (2200 - 1000) = 1 / 36500 := by
  have h1 : (1 : ℝ) + 1 / 4 * (2200 - 1000) / 100 = 4 := by norm_num
  have h2 : -(1 / (1 / 4 : ℝ)) = -((4 : ℕ) : ℝ) := by norm_num
  rw [gpdSurvivalAll, ite_eq_right (by norm_num : (1 / 4 : ℝ) ≠ 0), h1,
    max_eq_left (by norm_num), h2, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  norm_num [ζ]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

/-- **The checked statement.** The 100-year level of the model is 2200 m³/s and is exceeded with
probability `1/N` per day. There is a two-sided standard normal quantile `z` with
`N(0, 1)([-z, z]) = 95%`. For every iid sample `X` of excesses with law `GPD(1/4, 100)` there is a measurable
maximizer `g n` of the likelihood over `K`, and the probability that the interval
`x̂ ± z ŝ / √n` built from it contains 2200 tends to 95%.

Read the module docstring before using this: the sample is exactly GPD, `ζ` is known, and the
statement is about the limit `n → ∞` only. -/
theorem hundredYearFlood (hX : ∀ i, HasLaw (X i) (gpdMeasure (1 / 4) 100) P)
    (hind : iIndepFun X P) :
    gpdReturnLevel 1000 (1 / 4) 100 ζ 36500 = 2200 ∧
    ζ * gpdSurvivalAll (1 / 4) 100 (2200 - 1000) = 1 / 36500 ∧
    ∃ z : ℝ, 0 < z ∧ (gaussianReal 0 1).real (Icc (-z) z) = 95 / 100 ∧
      ∃ g : (n : ℕ) → (Fin n → ℝ) → ℝ × ℝ, (∀ n, Measurable (g n)) ∧
        (∀ n x, g n x ∈ K ∧ IsMaxOn (fun p : ℝ × ℝ ↦ gpdLogLikE p.1 p.2 x) K (g n x)) ∧
        Tendsto (fun n : ℕ ↦ P.real {ω | (2200 : ℝ) ∈ Icc
          (gpdReturnLevel 1000 (g n fun i : Fin n ↦ X i ω).1 (g n fun i : Fin n ↦ X i ω).2 ζ 36500 -
            z * √(gpdReturnLevelVar (g n fun i : Fin n ↦ X i ω).1
              (g n fun i : Fin n ↦ X i ω).2 ζ 36500) / √(n : ℝ))
          (gpdReturnLevel 1000 (g n fun i : Fin n ↦ X i ω).1 (g n fun i : Fin n ↦ X i ω).2 ζ 36500 +
            z * √(gpdReturnLevelVar (g n fun i : Fin n ↦ X i ω).1
              (g n fun i : Fin n ↦ X i ω).2 ζ 36500) / √(n : ℝ))})
          atTop (𝓝 (95 / 100)) := by
  refine ⟨returnLevel_eq, exceedance_eq, ?_⟩
  obtain ⟨z, hz, hcov⟩ := exists_gaussianReal_Icc_eq (α := 5 / 100) (by norm_num) (by norm_num)
  have hcov' : (gaussianReal 0 1).real (Icc (-z) z) = 95 / 100 := by rw [hcov]; norm_num
  refine ⟨z, hz, hcov', ?_⟩
  obtain ⟨g, hgm, hg, -⟩ := exists_gpdMLE_tendstoInDistribution isCompact_K K_sub mem_interior_K
    (by norm_num) (by norm_num) (by norm_num) hX hind HasLaw.id
  refine ⟨g, hgm, hg, ?_⟩
  have hθm : ∀ n : ℕ, AEMeasurable (fun ω ↦ g n fun i : Fin n ↦ X i ω) P := fun n ↦
    (hgm n).comp_aemeasurable (AEMeasurable.of_eval fun i ↦ (hX i).aemeasurable)
  have h := tendsto_measure_mem_gpdReturnLevelInterval (u := 1000) (ζ := ζ) (N := 36500)
    isCompact_K K_sub mem_interior_K (by norm_num) (by norm_num) (by norm_num) hX hind hθm
    (fun n ω ↦ (hg n _).1) (fun n ω ↦ (hg n _).2) (by norm_num [ζ]) z
  rw [returnLevel_eq] at h
  have h' := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  rw [← hcov']
  exact h'

/-- The hypotheses of `hundredYearFlood` can be met: such a sample exists. -/
theorem exists_sample :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ (∀ i, HasLaw (X i) (gpdMeasure (1 / 4) 100) P) ∧ iIndepFun X P := by
  obtain ⟨Ω, _, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (gpdMeasure (1 / 4) 100)
  exact ⟨Ω, _, P, X, hP, hlaw, hind⟩

end Examples.Applications.HundredYearFlood
