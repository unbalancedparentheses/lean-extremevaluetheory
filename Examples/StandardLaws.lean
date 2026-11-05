import ExtremeValueTheory

/-!
# The headline theorems on the standard laws

For Pareto, exponential, uniform, Gumbel, generalized Pareto, GEV, Student t and Cauchy laws, this
file applies the theorems on domains of attraction, norming constants, peaks over threshold and
(for heavy tails) the Hill estimator.

| Law | Domain | `ξ` | Norming constants | Peaks over threshold | Hill |
|---|---|---|---|---|---|
| Pareto(`α`) | Fréchet | `1/α` | explicit | yes | yes |
| Exponential | Gumbel | `0` | explicit | yes | not applicable |
| Uniform on `[0, 1]` | Weibull | `-1` | explicit | yes | not applicable |
| Gumbel | Gumbel | `0` | explicit, exact | yes | not applicable |
| GPD(`ξ`, `σ`) | by the sign of `ξ` | `ξ` | existence only | yes | `ξ > 0` |
| GEV(`ξ`, `μ`, `σ`) | by the sign of `ξ` | `ξ` | exact for `ξ ≠ 0`, standard law | yes | not done here |
| Student t(`ν`) | Fréchet | `1/ν` | existence only | yes | yes |
| Cauchy | Fréchet | `1` | existence only | yes | yes |

"Existence only" means that membership of the domain gives some affine maps `As n`
(`IsInMDAFrechet` and its siblings), with no formula.

The Hill statements are for an exact iid sample of the named law, with `k → ∞` and `k/n → 0`. They
are limits in probability, with no rate and no statement about a finite `n`.
-/

open Filter Topology Set MeasureTheory ProbabilityTheory
open CumulativeDistributionFunction ExtremeValueTheory
open scoped NNReal

namespace Examples.StandardLaws

/-- The conclusion of the Pickands–Balkema–de Haan theorem for `F` and shape `ξ`: there is a scale
`β(u) > 0` such that the excess survival function at `β(u) x` converges to the GPD survival
function of shape `ξ`, uniformly in `x ≥ 0`, as `u` tends to the right endpoint of `F`. This
abbreviation exists only to shorten the statements below. -/
def HasGPDExcessLimit (F : CumulativeDistributionFunction) (ξ : ℝ) : Prop :=
  ∃ β : ℝ → ℝ, (∀ᶠ u in F.upperEndpointFilter, 0 < β u) ∧
    TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
      (gpdSurvivalAll ξ 1) F.upperEndpointFilter (Ici 0)

/-- Pickands–Balkema–de Haan, in the abbreviation above. -/
theorem hasGPDExcessLimit {F : CumulativeDistributionFunction} {ξ : ℝ} (h : F.IsInMDAGEV ξ) :
    HasGPDExcessLimit F ξ :=
  (F.isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival ξ).1 h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
  {k : ℕ → ℕ}

/-! ### Pareto -/

section Pareto

variable {α : ℝ} (hα : 0 < α)
include hα

/-- Pareto(`α`) is in the Fréchet domain `MDA(Φ_α)`. -/
theorem pareto_domain : (paretoCDF hα).IsInMDAFrechet hα := isInMDAFrechet_paretoCDF hα

/-- Pareto norming constants: `F^n(n^{1/α} x) → Φ_α(x)`. -/
theorem pareto_norming (x : ℝ) :
    Tendsto (fun n : ℕ ↦ paretoCDF hα ((n : ℝ) ^ (1 / α) * x) ^ n) atTop
      (𝓝 (standardFrechetCDF hα x)) :=
  tendsto_paretoCDF_pow hα x

/-- Excesses of a Pareto law over a high threshold are asymptotically GPD with `ξ = 1/α`. -/
theorem pareto_pot : HasGPDExcessLimit (paretoCDF hα) (1 / α) :=
  hasGPDExcessLimit (isInMDAGEV_paretoCDF hα)

/-- The Hill estimator of a Pareto sample converges in probability to `1/α`. -/
theorem pareto_hill {t : ℝ} (ht : 0 < t) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (paretoMeasure t α) P) (hind : iIndepFun X P)
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ hill (fun i : Fin n ↦ X i ω) (k n)) atTop (fun _ ↦ 1 / α) :=
  tendstoInMeasure_hill_of_hasLaw hX hlaw hind hα
    (isRegularlyVarying_tail_paretoMeasure ht hα) hk hkn

end Pareto

/-! ### Exponential -/

/-- The standard exponential law is in the Gumbel domain, with `ξ = 0`. -/
theorem exponential_domain : standardExponentialCDF.IsInMDAGEV 0 :=
  isInMDAGEV_standardExponentialCDF

/-- Exponential norming constants: `F^n(x + log n) → Λ(x)`. -/
theorem exponential_norming (x : ℝ) :
    Tendsto (fun n : ℕ ↦ standardExponentialCDF (x + Real.log n) ^ n) atTop
      (𝓝 (standardGumbelCDF x)) :=
  tendsto_standardExponentialCDF_pow x

/-- Excesses of an exponential law over a high threshold are asymptotically GPD with `ξ = 0`. -/
theorem exponential_pot : HasGPDExcessLimit standardExponentialCDF 0 :=
  hasGPDExcessLimit isInMDAGEV_standardExponentialCDF

/-- In this case nothing is asymptotic: the law is memoryless, so the excess over any threshold
`u ≥ 0` is exactly standard exponential. -/
theorem exponential_excess_exact {u x : ℝ} (hu : 0 ≤ u) (hx : 0 ≤ x) :
    excessSurvival (fun y ↦ 1 - standardExponentialCDF y) u x = Real.exp (-x) := by
  simp only [excessSurvival]
  rw [standardExponentialCDF_apply_of_nonneg (add_nonneg hu hx),
    standardExponentialCDF_apply_of_nonneg hu, sub_sub_cancel, sub_sub_cancel, neg_add,
    Real.exp_add, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

/-! ### Uniform

The library's uniform law on `[0, 1]` is `powerCDF` with `α = 1`. Its c.d.f. is identified below;
a c.d.f. determines its law. -/

/-- `powerCDF one_pos` is the c.d.f. of the uniform law on `[0, 1]`. -/
theorem uniform_cdf {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : powerCDF one_pos x = x := by
  rw [powerCDF_apply_of_mem_Icc one_pos hx, Real.rpow_one, sub_sub_cancel]

/-- The uniform law is in the Weibull domain `MDA(Ψ_1)`, with `ξ = -1`. -/
theorem uniform_domain : (powerCDF one_pos).IsInMDAGEV (-1 / 1) :=
  isInMDAGEV_powerCDF one_pos

/-- Uniform norming constants: `F^n(1 + n⁻¹ x) → Ψ_1(x)`, written with `n ^ (-1 / 1)`. -/
theorem uniform_norming (x : ℝ) :
    Tendsto (fun n : ℕ ↦ powerCDF one_pos (1 + (n : ℝ) ^ (-1 / 1 : ℝ) * x) ^ n) atTop
      (𝓝 (standardWeibullCDF one_pos x)) :=
  tendsto_powerCDF_pow one_pos x

/-- Excesses of a uniform law below its endpoint are asymptotically GPD with `ξ = -1`. -/
theorem uniform_pot : HasGPDExcessLimit (powerCDF one_pos) (-1 / 1) :=
  hasGPDExcessLimit uniform_domain

/-! ### Gumbel -/

/-- The Gumbel law is in its own domain. -/
theorem gumbel_domain : standardGumbelCDF.IsInMDAGEV 0 :=
  isInMDAGumbel_standardGumbelCDF.isInMDAGEV

/-- Gumbel norming constants, with no limit needed: `Λ(x + log n)^n = Λ(x)` for `n ≥ 1`. -/
theorem gumbel_norming {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    standardGumbelCDF (1 * x + Real.log n) ^ n = standardGumbelCDF x :=
  standardGumbelCDF_pow_apply_add_log hn x

/-- Excesses of a Gumbel law over a high threshold are asymptotically GPD with `ξ = 0`. -/
theorem gumbel_pot : HasGPDExcessLimit standardGumbelCDF 0 :=
  hasGPDExcessLimit gumbel_domain

/-- The mean of the Gumbel law is the Euler–Mascheroni constant. -/
theorem gumbel_mean : ∫ x, x ∂standardGumbelCDF.measure = Real.eulerMascheroniConstant :=
  integral_id_standardGumbelCDF

/-! ### Generalized Pareto -/

section GPD

variable (ξ : ℝ) {σ : ℝ} (hσ : 0 < σ)
include hσ

/-- `GPD(ξ, σ)` is in `MDA(H_ξ)`, for every `ξ`. -/
theorem gpd_domain : (ofMeasure (gpdMeasure ξ σ)).IsInMDAGEV ξ :=
  isInMDAGEV_ofMeasure_gpdMeasure ξ hσ

/-- Excesses of a GPD over a high threshold are asymptotically GPD with the same shape. -/
theorem gpd_pot : HasGPDExcessLimit (ofMeasure (gpdMeasure ξ σ)) ξ :=
  hasGPDExcessLimit (gpd_domain ξ hσ)

variable {ξ}

/-- In this case nothing is asymptotic: excesses of a GPD over a threshold `u` in its support are
exactly GPD, with the same shape and scale `σ + ξ u` (threshold stability, `gpdSurvivalAll_add`). -/
theorem gpd_excess_exact {u : ℝ} (hu : 0 < σ + ξ * u) (t : ℝ) :
    excessSurvival (gpdSurvivalAll ξ σ) u t = gpdSurvivalAll ξ (σ + ξ * u) t := by
  rw [excessSurvival, gpdSurvivalAll_add hσ hu,
    mul_div_cancel_left₀ _ (gpdSurvivalAll_pos hσ hu).ne']

/-- For `ξ > 0`, the Hill estimator of a GPD sample converges in probability to `ξ`. -/
theorem gpd_hill (hξ : 0 < ξ) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (gpdMeasure ξ σ) P) (hind : iIndepFun X P)
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ hill (fun i : Fin n ↦ X i ω) (k n)) atTop (fun _ ↦ ξ) := by
  have := tendstoInMeasure_hill_of_hasLaw hX hlaw hind (one_div_pos.2 hξ)
    (isRegularlyVarying_measureReal_Ioi_gpdMeasure hξ hσ) hk hkn
  simpa using this

end GPD

/-! ### GEV -/

/-- The GEV law `H_{ξ,μ,σ}` is in `MDA(H_ξ)`. -/
theorem gev_domain (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : (gevLocScaleCDF ξ μ hσ).IsInMDAGEV ξ :=
  isInMDAGEV_gevLocScaleCDF ξ μ hσ

/-- GEV norming constants for the standard law, with no limit needed:
`H_ξ(n^ξ x + (n^ξ - 1) / ξ)^n = H_ξ(x)`, `ξ ≠ 0`, `n ≥ 1`. -/
theorem gev_norming {ξ : ℝ} (hξ : ξ ≠ 0) {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    gevFun ξ ((n : ℝ) ^ ξ * x + ((n : ℝ) ^ ξ - 1) / ξ) ^ n = gevFun ξ x :=
  gevFun_pow_apply hξ hn x

/-- Excesses of a GEV law over a high threshold are asymptotically GPD with the same shape. -/
theorem gev_pot (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) : HasGPDExcessLimit (gevLocScaleCDF ξ μ hσ) ξ :=
  hasGPDExcessLimit (gev_domain ξ μ hσ)

/-- The `m`-block return level `μ + σ z_m` is the `1 - 1/m` quantile of `H_{ξ,μ,σ}`. -/
theorem gev_returnLevel (ξ μ : ℝ) {σ : ℝ} (hσ : 0 < σ) {m : ℝ} (hm : 1 < m) :
    gevLocScaleCDF ξ μ hσ (μ + σ * returnLevel ξ m) = 1 - 1 / m :=
  gevLocScaleCDF_returnLevel ξ μ hσ hm

/-! ### Student t

**What the library has.** `studentTMeasure ν` is the law with density proportional to
`(1 + x² / ν) ^ (-(ν + 1) / 2)`. It is a probability measure (`isProbabilityMeasure_studentTMeasure`),
and for `ν = 1` it is Mathlib's Cauchy law (`studentTMeasure_one`). Its tail is regularly varying with
index `-ν`, by Karamata's theorem applied to the density.

**What is missing.**

* The normalizing constant is defined as an integral. The formula
  `Γ((ν + 1) / 2) / (√(ν π) Γ(ν / 2))` is not proved.
* The representation as `Z / √(χ²_ν / ν)` is not proved, so no statement here connects this law to
  a t statistic.
* There are no explicit norming constants or tail constant: the domain gives only the existence of
  the affine maps.
* Hill asymptotic normality for this law is not derived, since that needs a second-order condition
  on its tail quantile function. -/

section StudentT

variable {ν : ℝ} (hν : 0 < ν)
include hν

/-- Student's t law with `ν` degrees of freedom is in the Fréchet domain `MDA(Φ_ν)`. -/
theorem studentT_domain : (ofMeasure (studentTMeasure ν)).IsInMDAFrechet hν :=
  isInMDAFrechet_ofMeasure_studentTMeasure hν

/-- Excesses of a Student t law over a high threshold are asymptotically GPD with `ξ = 1/ν`. -/
theorem studentT_pot : HasGPDExcessLimit (ofMeasure (studentTMeasure ν)) (1 / ν) :=
  hasGPDExcessLimit (studentT_domain hν).isInMDAGEV

/-- The Hill estimator of a Student t sample converges in probability to `1/ν`. -/
theorem studentT_hill (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (studentTMeasure ν) P) (hind : iIndepFun X P)
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ hill (fun i : Fin n ↦ X i ω) (k n)) atTop (fun _ ↦ 1 / ν) :=
  tendstoInMeasure_hill_of_hasLaw hX hlaw hind hν
    (isRegularlyVarying_measureReal_Ioi_studentTMeasure hν) hk hkn

end StudentT

/-! ### Cauchy

The explicit norming constants `n / π` for the Cauchy law are not in the library: the domain gives
only the existence of the affine maps. -/

section Cauchy

variable (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0)
include hγ

/-- The Cauchy law is in the Fréchet domain `MDA(Φ_1)`. -/
theorem cauchy_domain : (ofMeasure (cauchyMeasure x₀ γ)).IsInMDAFrechet one_pos :=
  isInMDAFrechet_ofMeasure_cauchyMeasure x₀ hγ

/-- Excesses of a Cauchy law over a high threshold are asymptotically GPD with `ξ = 1`. -/
theorem cauchy_pot : HasGPDExcessLimit (ofMeasure (cauchyMeasure x₀ γ)) 1 := by
  simpa using hasGPDExcessLimit (cauchy_domain x₀ hγ).isInMDAGEV

/-- The Hill estimator of a Cauchy sample converges in probability to `1`. -/
theorem cauchy_hill (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (cauchyMeasure x₀ γ) P) (hind : iIndepFun X P)
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ hill (fun i : Fin n ↦ X i ω) (k n)) atTop (fun _ ↦ 1) := by
  simpa using tendstoInMeasure_hill_of_hasLaw hX hlaw hind one_pos
    (isRegularlyVarying_measureReal_Ioi_cauchyMeasure x₀ hγ) hk hkn

end Cauchy

/-- Student t with one degree of freedom and the standard Cauchy law are the same law, so the two
sections above agree there: `1/ν = 1`. -/
example : studentTMeasure 1 = cauchyMeasure 0 1 := studentTMeasure_one

end Examples.StandardLaws
