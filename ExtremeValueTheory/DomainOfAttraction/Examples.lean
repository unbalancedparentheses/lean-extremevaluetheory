/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.MDependent
import ExtremeValueTheory.DomainOfAttraction.NamedLaws
import ExtremeValueTheory.DomainOfAttraction.Norming
import ExtremeValueTheory.HeavyTails.Lognormal
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Gamma

/-!
# The standard laws in their domains of attraction, with explicit norming constants

## Main results

* `tendsto_standardNormalCDF_pow`: **the normal law**, the most cited example of the subject:
  `Φ (x / L_n + L_n - (log log n + log 4π) / (2 L_n)) ^ n → exp (-e^{-x})`, with `L_n = √(2 log n)`.
* `isInMDAGEV_standardNormalCDF`: the standard normal law is in `MDA(H_0)`.
* `isInMDAGEV_ofMeasure_gaussianReal`: so is every normal law with positive variance.
* `tendsto_gammaCDF_pow`, `isInMDAGEV_gammaCDF`: the Gamma law of shape `a` and rate `r`, in particular
  the Erlang laws (`a` a positive integer) and the exponential law (`a = 1`), with
  `b_n = (log n + (a - 1) log log n - log Γ(a)) / r` and `a_n = 1 / r`.
* `tendsto_standardCauchyCDF_pow`, `isInMDAGEV_standardCauchyCDF`: the standard Cauchy law, in
  `MDA(H_1)`, with `a_n = n / π`.
* `isInMDAGumbel_of_tendsto_mul_one_sub`: the criterion `n (1 - F (a_n x + b_n)) → e^{-x}`.

The Cauchy law of any location and scale, and Student's t laws, are in
`ExtremeValueTheory.DomainOfAttraction.NamedLaws`.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  §3.3 and §3.4 [EKM]. The constants are the textbook ones as we recall them; the book was not
  available to check them, but each limit is proved here.
-/

open Real Filter Topology Set MeasureTheory ProbabilityTheory ExtremeValueTheory
open scoped ENNReal NNReal

namespace CumulativeDistributionFunction

/-- **A criterion for the Gumbel domain**: if `a_n > 0` eventually and
`n (1 - F (a_n x + b_n)) → e^{-x}` for every `x`, then `F` is in `MDA(Λ)`. The positivity of `a_n` is
asked only eventually, which lets the constants be explicit formulas that are junk for small `n`. -/
theorem isInMDAGumbel_of_tendsto_mul_one_sub (F : CumulativeDistributionFunction) {a b : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (h : ∀ x, Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - F (a n * x + b n))) atTop (𝓝 (exp (-x)))) :
    F.IsInMDAGumbel := by
  classical
  refine ⟨fun n ↦ if hn : 0 < a n then (AffineIncrEquiv.mkOfCoefs hn (b n))⁻¹ else 1, fun x ↦ ?_⟩
  rw [standardGumbelCDF_apply_eq]
  refine (tendsto_pow_of_tendsto_mul_one_sub (h x)).congr' ?_
  filter_upwards [ha] with n hn
  simp only [hn, ↓reduceDIte]
  rw [mulAction_apply_eq, inv_inv]
  simp

/-! ### The normal law -/

/-- The c.d.f. of the standard normal law. -/
noncomputable def standardNormalCDF : CumulativeDistributionFunction :=
  ofMeasure (gaussianReal 0 1)

/-- The tail of the standard normal c.d.f. is `tail (gaussianReal 0 1)`. -/
theorem one_sub_standardNormalCDF (x : ℝ) : 1 - standardNormalCDF x = tail (gaussianReal 0 1) x :=
  one_sub_ofMeasure_apply x

/-- The textbook scale `1 / √(2 log n)` for maxima of normal variables. It is junk for `n ≤ 1`. -/
noncomputable def normalScale (n : ℕ) : ℝ := (√(2 * log n))⁻¹

/-- The textbook location `√(2 log n) - (log log n + log 4π) / (2 √(2 log n))` for maxima of normal
variables. It is junk for `n ≤ 2`. -/
noncomputable def normalLocation (n : ℕ) : ℝ :=
  √(2 * log n) - (log (log n) + log (4 * π)) / (2 * √(2 * log n))

/-- `exp (log z / 2) = √z`, for `z > 0`. -/
private lemma exp_log_div_two {z : ℝ} (hz : 0 < z) : exp (log z / 2) = √z := by
  rw [Real.sqrt_eq_rpow, rpow_def_of_pos hz]
  congr 1
  ring

/-- **Tail of the normal law at the textbook levels**:
`n (1 - Φ (x a_n + b_n)) → e^{-x}`, with `a_n = normalScale n`, `b_n = normalLocation n`. The proof
is the Mills ratio with the expansion
`u_n² / 2 = log n + x - (log log n + log 4π) / 2 + o(1)`. -/
theorem tendsto_mul_tail_gaussianReal_norming (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * tail (gaussianReal 0 1) (normalScale n * x + normalLocation n)) atTop
      (𝓝 (exp (-x))) := by
  set y : ℕ → ℝ := fun n ↦ log n with hy_def
  have hy : Tendsto y atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  set L : ℕ → ℝ := fun n ↦ √(2 * y n) with hL_def
  have hL : Tendsto L atTop atTop := Real.tendsto_sqrt_atTop.comp (hy.const_mul_atTop two_pos)
  set K : ℝ := log (4 * π) with hK
  set c : ℕ → ℝ := fun n ↦ x - (log (y n) + K) / 2 with hc_def
  -- `c / L → 0`
  have hcL : Tendsto (fun n ↦ c n / L n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ log (y n) / L n) atTop (𝓝 0) := by
      have := (tendsto_log_div_sqrt_atTop.comp hy).mul_const (√2)⁻¹
      rw [zero_mul] at this
      refine this.congr fun n ↦ ?_
      simp only [Function.comp_apply, hL_def]
      rw [Real.sqrt_mul zero_le_two, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    have h2 : Tendsto (fun n ↦ x / L n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hL
    have h3 : Tendsto (fun n ↦ (K / 2) / L n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hL
    have := (h2.sub (h1.const_mul (1 / 2))).sub h3
    simp only [mul_zero, sub_zero] at this
    refine this.congr fun n ↦ ?_
    simp only [hc_def]
    ring
  set u : ℕ → ℝ := fun n ↦ L n + c n / L n with hu_def
  have hu : Tendsto u atTop atTop := hL.atTop_add hcL
  -- the Mills ratio along `u`
  have hM : Tendsto (fun n ↦ tail (gaussianReal 0 1) (u n) /
      ((1 : ℝ≥0) * gaussianPDFReal 0 1 (u n) / (u n - 0))) atTop (𝓝 1) :=
    (tendsto_tail_gaussianReal_div (m := 0) (v := 1) one_ne_zero).comp hu
  -- the density along `u`
  have hmain : Tendsto (fun n : ℕ ↦ (n : ℝ) * (gaussianPDFReal 0 1 (u n) / u n)) atTop
      (𝓝 (exp (-x))) := by
    have h1 : Tendsto (fun n ↦ (1 + (c n / L n) / L n)⁻¹) atTop (𝓝 1) := by
      have := ((hcL.div_atTop hL).const_add 1).inv₀ (by norm_num)
      simpa using this
    have h2 : Tendsto (fun n ↦ exp (-(c n / L n) ^ 2 / 2)) atTop (𝓝 1) := by
      have := (continuous_exp.tendsto _).comp (((hcL.pow 2).neg).div_const 2)
      simpa [Function.comp_def] using this
    have := ((h1.const_mul (exp (-x))).mul h2)
    rw [mul_one, mul_one] at this
    refine this.congr' ?_
    filter_upwards [hy.eventually_gt_atTop 0, eventually_gt_atTop 0, hL.eventually_gt_atTop 0,
      hu.eventually_gt_atTop 0] with n hy0 hn hL0 hu0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hL2 : L n ^ 2 = 2 * y n := Real.sq_sqrt (by positivity)
    have hu2 : u n ^ 2 = 2 * y n + 2 * c n + (c n / L n) ^ 2 := by
      simp only [hu_def]
      field_simp
      rw [hL2]
      ring
    have hnexp : (n : ℝ) = exp (y n) := (exp_log hn').symm
    have hexp1 : (n : ℝ) * exp (-(u n) ^ 2 / 2) = exp (-c n) * exp (-(c n / L n) ^ 2 / 2) := by
      rw [hnexp, ← exp_add, ← exp_add, hu2]
      congr 1
      ring
    have h4π : 0 < 4 * π := by positivity
    have hexp2 : exp (-c n) = exp (-x) * (√(2 * π) * L n) := by
      have : -c n = -x + log (y n * (4 * π)) / 2 := by
        rw [log_mul hy0.ne' h4π.ne']
        simp only [hc_def]
        ring
      rw [this, exp_add, exp_log_div_two (by positivity)]
      congr 1
      simp only [hL_def]
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      ring
    have hs : 0 < √(2 * π) := by positivity
    have hpdf : gaussianPDFReal 0 1 (u n) = (√(2 * π))⁻¹ * exp (-(u n) ^ 2 / 2) := by
      simp [gaussianPDFReal]
    have hratio : (1 + (c n / L n) / L n)⁻¹ = L n / u n := by
      have : u n = L n * (1 + (c n / L n) / L n) := by
        simp only [hu_def]
        field_simp
      rw [this]
      have hne : 1 + c n / L n / L n ≠ 0 := by
        intro h0
        rw [this, h0, mul_zero] at hu0
        exact lt_irrefl _ hu0
      field_simp
    rw [hratio, hpdf]
    have : (n : ℝ) * ((√(2 * π))⁻¹ * exp (-(u n) ^ 2 / 2) / u n) =
        (√(2 * π))⁻¹ * ((n : ℝ) * exp (-(u n) ^ 2 / 2)) / u n := by ring
    rw [this, hexp1, hexp2]
    field_simp
  have := hM.mul hmain
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0, hu.eventually_gt_atTop 0] with n hL0 hu0
  have hp : 0 < gaussianPDFReal 0 1 (u n) := gaussianPDFReal_pos _ _ _ one_ne_zero
  have hscale : normalScale n * x + normalLocation n = u n := by
    have hL0' : √(2 * log n) ≠ 0 := hL0.ne'
    simp only [normalScale, normalLocation, hu_def, hc_def, hL_def, hy_def]
    field_simp
    ring
  rw [hscale]
  simp only [NNReal.coe_one, one_mul, sub_zero]
  have hne : gaussianPDFReal 0 1 (u n) / u n ≠ 0 := (div_pos hp hu0).ne'
  field_simp

/-- **The normal law, with explicit norming constants**: with
`a_n = 1 / √(2 log n)` and `b_n = √(2 log n) - (log log n + log 4π) / (2 √(2 log n))`,
`Φ (a_n x + b_n) ^ n → exp (-e^{-x})` for every `x`. -/
theorem tendsto_standardNormalCDF_pow (x : ℝ) :
    Tendsto (fun n ↦ standardNormalCDF (normalScale n * x + normalLocation n) ^ n) atTop
      (𝓝 (standardGumbelCDF x)) := by
  rw [standardGumbelCDF_apply_eq]
  refine tendsto_pow_of_tendsto_mul_one_sub ?_
  simpa only [one_sub_standardNormalCDF] using tendsto_mul_tail_gaussianReal_norming x

/-- `normalScale n > 0` for large `n`. -/
theorem eventually_normalScale_pos : ∀ᶠ n in atTop, 0 < normalScale n := by
  have hy : Tendsto (fun n : ℕ ↦ log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hy.eventually_gt_atTop 0] with n hn
  exact inv_pos.2 (Real.sqrt_pos.2 (by positivity))

/-- **The standard normal law is in the Gumbel domain of attraction.** -/
theorem isInMDAGumbel_standardNormalCDF : standardNormalCDF.IsInMDAGumbel :=
  standardNormalCDF.isInMDAGumbel_of_tendsto_mul_one_sub eventually_normalScale_pos fun x ↦ by
    simpa only [one_sub_standardNormalCDF] using tendsto_mul_tail_gaussianReal_norming x

/-- **The standard normal law is in `MDA(H_0)`**. -/
theorem isInMDAGEV_standardNormalCDF : standardNormalCDF.IsInMDAGEV 0 :=
  isInMDAGumbel_standardNormalCDF.isInMDAGEV

/-- **Every normal law with positive variance is in `MDA(H_0)`**. -/
theorem isInMDAGEV_ofMeasure_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (ofMeasure (gaussianReal m v)).IsInMDAGEV 0 := by
  have hσ : 0 < √(v : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hmap : gaussianReal m v = (gaussianReal 0 1).map fun z ↦ √(v : ℝ) * z + m := by
    have h1 := congrArg (Measure.map fun x ↦ x + m)
      (gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := 1) (√(v : ℝ)))
    rw [gaussianReal_map_add_const, Measure.map_map (by fun_prop) (by fun_prop)] at h1
    refine Eq.trans ?_ h1.symm
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  have heq : ofMeasure (gaussianReal m v) =
      AffineIncrEquiv.mkOfCoefs hσ m • standardNormalCDF := by
    apply CumulativeDistributionFunction.ext
    funext x
    rw [mulAction_apply_eq, standardNormalCDF, ofMeasure_apply, ofMeasure_apply, hmap,
      map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext z
    set B := AffineIncrEquiv.mkOfCoefs hσ m with hB
    have hw : √(v : ℝ) * B⁻¹ x + m = x := by
      have h1 : B (B⁻¹ x) = x := by
        rw [← AffineIncrEquiv.mul_apply_eq_comp_apply, mul_inv_cancel, AffineIncrEquiv.one_apply]
      rw [AffineIncrEquiv.apply_eq] at h1
      simpa [hB] using h1
    simp only [mem_preimage, mem_Iic]
    set w := B⁻¹ x with hw_def
    constructor
    · intro h
      exact le_of_mul_le_mul_left (by linarith) hσ
    · intro h
      have := mul_le_mul_of_nonneg_left h hσ.le
      linarith
  rw [heq]
  exact isInMDAGEV_standardNormalCDF.smul _

/-! ### The Cauchy law -/

/-- The c.d.f. of the standard Cauchy law. -/
noncomputable def standardCauchyCDF : CumulativeDistributionFunction :=
  ofMeasure (cauchyMeasure 0 1)

/-- The tail of the standard Cauchy law: `P(X > x) = (π / 2 - arctan x) / π`. -/
theorem one_sub_standardCauchyCDF (x : ℝ) : 1 - standardCauchyCDF x = π⁻¹ * (π / 2 - arctan x) := by
  have hpdf : ∀ t, cauchyPDFReal 0 1 t = π⁻¹ * (1 + t ^ 2)⁻¹ := fun t ↦ by
    rw [cauchyPDFReal_def']
    simp
  have h1 : cauchyMeasure 0 1 = volume.withDensity fun t ↦ ENNReal.ofReal (cauchyPDFReal 0 1 t) := by
    rw [cauchyMeasure_of_scale_ne_zero _ one_ne_zero]
    rfl
  rw [standardCauchyCDF, one_sub_ofMeasure_apply, h1,
    measureReal_withDensity_Ioi (fun t ↦ (cauchyPDF_pos 0 one_ne_zero t).le)
      (integrable_cauchyPDFReal 0) x]
  simp only [hpdf]
  rw [integral_const_mul, integral_Ioi_inv_one_add_sq]

/-- `x (1 - F x) → 1 / π` for the standard Cauchy law. -/
theorem tendsto_mul_one_sub_standardCauchyCDF :
    Tendsto (fun x ↦ x * (1 - standardCauchyCDF x)) atTop (𝓝 π⁻¹) := by
  -- `arctan y / y → 1` as `y → 0`, `y ≠ 0`
  have h0 : Tendsto (fun y ↦ arctan y / y) (𝓝[>] 0) (𝓝 1) := by
    have hd := (hasDerivAt_arctan 0).tendsto_slope_zero_right
    simp only [zero_add, arctan_zero, sub_zero, smul_eq_mul, zero_pow two_ne_zero] at hd
    norm_num at hd
    refine hd.congr fun y ↦ ?_
    rw [div_eq_inv_mul]
  have h1 := (h0.comp tendsto_inv_atTop_nhdsGT_zero).const_mul π⁻¹
  rw [mul_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [one_sub_standardCauchyCDF, ← arctan_inv_of_pos hx]
  simp only [Function.comp_apply]
  field_simp

/-- **The standard Cauchy law is in the Fréchet domain with `α = 1`.** Its tail is regularly varying
with index `-1`. -/
theorem isInMDAFrechet_standardCauchyCDF : standardCauchyCDF.IsInMDAFrechet one_pos :=
  isInMDAFrechet_ofMeasure_cauchyMeasure 0 one_ne_zero

/-- **The standard Cauchy law is in `MDA(H_1)`**. -/
theorem isInMDAGEV_standardCauchyCDF : standardCauchyCDF.IsInMDAGEV 1 := by
  simpa using isInMDAFrechet_standardCauchyCDF.isInMDAGEV

/-- **The standard Cauchy law, with explicit norming constants**:
`F (n x / π) ^ n → Φ_1 x`, the standard Fréchet law of index `1`, for every `x`. -/
theorem tendsto_standardCauchyCDF_pow (x : ℝ) :
    Tendsto (fun n : ℕ ↦ standardCauchyCDF ((n : ℝ) / π * x) ^ n) atTop
      (𝓝 (standardFrechetCDF one_pos x)) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [standardFrechetCDF_apply_nonpos_eq _ hx]
    have hhalf : standardCauchyCDF 0 = 1 / 2 := by
      have := one_sub_standardCauchyCDF 0
      rw [arctan_zero, sub_zero] at this
      have hπ := pi_ne_zero
      field_simp at this
      linarith
    have hle : ∀ n : ℕ, standardCauchyCDF ((n : ℝ) / π * x) ≤ 1 / 2 := fun n ↦ by
      rw [← hhalf]
      exact standardCauchyCDF.mono' (mul_nonpos_of_nonneg_of_nonpos (by positivity) hx)
    refine squeeze_zero (fun n ↦ pow_nonneg (standardCauchyCDF.apply_nonneg _) n)
      (fun n ↦ pow_le_pow_left₀ (standardCauchyCDF.apply_nonneg _) (hle n) n) ?_
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · rw [standardFrechetCDF_apply_pos_eq _ hx]
    have hu : Tendsto (fun n : ℕ ↦ (n : ℝ) / π * x) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_div_const pi_pos).atTop_mul_const hx
    have h1 := (tendsto_mul_one_sub_standardCauchyCDF.comp hu).mul_const (π / x)
    have hrw : π⁻¹ * (π / x) = rpow x (-1) := by
      change _ = x ^ (-1 : ℝ)
      rw [rpow_neg_one]
      field_simp
    rw [hrw] at h1
    refine tendsto_pow_of_tendsto_mul_one_sub (h1.congr fun n ↦ ?_)
    simp only [Function.comp_apply]
    field_simp

/-! ### The Gamma law, and the Erlang laws -/

/-- The c.d.f. of the Gamma law of shape `a` and rate `r`, with density
`r ^ a / Γ(a) * x ^ (a - 1) * exp (-r x)` on `x ≥ 0`. For `a` a positive integer it is the Erlang
law, for `a = 1` the exponential law. -/
noncomputable def gammaCDF (a r : ℝ) : CumulativeDistributionFunction :=
  ofMeasure (gammaMeasure a r)

section Gamma

variable {a r : ℝ}

/-- The density of the Gamma law for `t > 0`. -/
private noncomputable def gammaDensity (a r t : ℝ) : ℝ :=
  r ^ a / Gamma a * t ^ (a - 1) * exp (-(r * t))

private lemma gammaPDFReal_of_pos {t : ℝ} (ht : 0 < t) :
    gammaPDFReal a r t = gammaDensity a r t := by
  simp [gammaPDFReal, gammaDensity, ht.le]

private lemma integrable_gammaPDFReal (ha : 0 < a) (hr : 0 < r) : Integrable (gammaPDFReal a r) := by
  refine ⟨(measurable_gammaPDFReal a r).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ gammaPDFReal_nonneg ha hr x)]
  exact (lintegral_gammaPDF_eq_one ha hr).trans_lt ENNReal.one_lt_top

private lemma one_sub_gammaCDF (ha : 0 < a) (hr : 0 < r) (t : ℝ) :
    1 - gammaCDF a r t = ∫ s in Ioi t, gammaPDFReal a r s := by
  have := isProbabilityMeasure_gammaMeasure ha hr
  rw [gammaCDF, one_sub_ofMeasure_apply]
  exact measureReal_withDensity_Ioi (gammaPDFReal_nonneg ha hr) (integrable_gammaPDFReal ha hr) t

private lemma gammaDensity_pos (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    0 < gammaDensity a r t := by
  have := Gamma_pos_of_pos ha
  have := rpow_pos_of_pos hr a
  have := rpow_pos_of_pos ht (a - 1)
  simp only [gammaDensity]
  positivity

private lemma hasDerivAt_gammaDensity {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gammaDensity a r) (gammaDensity a r t * ((a - 1) / t - r)) t := by
  have h1 := (hasDerivAt_rpow_const (x := t) (p := a - 1) (Or.inl ht.ne')).const_mul (r ^ a / Gamma a)
  have h2 : HasDerivAt (fun s ↦ exp (-(r * s))) (exp (-(r * t)) * -r) t := by
    simpa using ((hasDerivAt_id t).const_mul r).neg.exp
  refine (h1.mul h2).congr_deriv ?_
  simp only [gammaDensity]
  rw [rpow_sub_one ht.ne']
  field_simp
  ring

private lemma hasDerivAt_one_sub_gammaCDF (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ 1 - gammaCDF a r s) (-gammaDensity a r t) t := by
  have hi := integrable_gammaPDFReal ha hr
  have hii : ∀ u v : ℝ, IntervalIntegrable (gammaPDFReal a r) volume u v := fun u v ↦
    hi.intervalIntegrable
  have hc : ContinuousAt (gammaPDFReal a r) t := by
    refine (hasDerivAt_gammaDensity (a := a) (r := r) ht).continuousAt.congr ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    exact (gammaPDFReal_of_pos hs).symm
  have hd := (intervalIntegral.integral_hasDerivAt_right (hii t t)
    ((measurable_gammaPDFReal a r).stronglyMeasurable.stronglyMeasurableAtFilter) hc).const_sub
    (∫ s in Ioi t, gammaPDFReal a r s)
  rw [gammaPDFReal_of_pos ht] at hd
  refine hd.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
  have := intervalIntegral.integral_interval_add_Ioi (a := t) (b := s) (hi.integrableOn)
    (hi.integrableOn)
  simp only [one_sub_gammaCDF ha hr]
  linarith

/-- The tail of the Gamma law is equivalent to its density divided by `r`, by L'Hôpital's rule. -/
private lemma tendsto_one_sub_gammaCDF_div_density (ha : 0 < a) (hr : 0 < r) :
    Tendsto (fun t ↦ (1 - gammaCDF a r t) / gammaDensity a r t) atTop (𝓝 (1 / r)) := by
  have hlin : Tendsto (fun t : ℝ ↦ (a - 1) / t - r) atTop (𝓝 (-r)) := by
    simpa using (tendsto_const_nhds (x := a - 1)).div_atTop tendsto_id |>.sub_const r
  refine HasDerivAt.lhopital_zero_atTop (f' := fun t ↦ -gammaDensity a r t)
    (g' := fun t ↦ gammaDensity a r t * ((a - 1) / t - r)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact hasDerivAt_one_sub_gammaCDF ha hr ht
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact hasDerivAt_gammaDensity ht
  · filter_upwards [eventually_gt_atTop 0, hlin.eventually (gt_mem_nhds (neg_lt_zero.2 hr))]
      with t ht hlt
    exact mul_ne_zero (gammaDensity_pos ha hr ht).ne' hlt.ne
  · simpa using (gammaCDF a r).tendsto_atTop.const_sub 1
  · have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a - 1) r hr).const_mul (r ^ a / Gamma a)
    rw [mul_zero] at this
    refine this.congr fun t ↦ ?_
    simp only [gammaDensity, neg_mul]
    ring
  · have := (hlin.inv₀ (neg_ne_zero.2 hr.ne')).neg
    rw [inv_neg, neg_neg, ← one_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have := (gammaDensity_pos ha hr ht).ne'
    by_cases h0 : (a - 1) / t - r = 0
    · simp [h0]
    · field_simp

/-- **Tail of the Gamma law at the textbook levels**: with
`b_n = (log n + (a - 1) log log n - log Γ(a)) / r`, `n (1 - F (x / r + b_n)) → e^{-x}`. -/
theorem tendsto_mul_one_sub_gammaCDF (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - gammaCDF a r
      (r⁻¹ * x + (log n + (a - 1) * log (log n) - log (Gamma a)) / r))) atTop (𝓝 (exp (-x))) := by
  set y : ℕ → ℝ := fun n ↦ log n with hy_def
  have hy : Tendsto y atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  set t : ℕ → ℝ := fun n ↦ r⁻¹ * x + (y n + (a - 1) * log (y n) - log (Gamma a)) / r with ht_def
  have hGam : 0 < Gamma a := Gamma_pos_of_pos ha
  -- `r t / y → 1`
  have hty : Tendsto (fun n ↦ r * t n / y n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n ↦ log (y n) / y n) atTop (𝓝 0) :=
      isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hy
    have h2 : Tendsto (fun n ↦ (x - log (Gamma a)) / y n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hy
    have := ((h1.const_mul (a - 1)).add h2).const_add 1
    simp only [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [hy.eventually_gt_atTop 0] with n hn
    simp only [ht_def]
    field_simp
    ring
  have ht : Tendsto t atTop atTop := by
    have h1 : Tendsto (fun n ↦ (r * t n / y n) * y n) atTop atTop :=
      (hty.pos_mul_atTop one_pos hy)
    have h2 : Tendsto (fun n ↦ r⁻¹ * ((r * t n / y n) * y n)) atTop atTop :=
      h1.const_mul_atTop (inv_pos.2 hr)
    refine h2.congr' ?_
    filter_upwards [hy.eventually_gt_atTop 0] with n hn
    field_simp
  have hT := (tendsto_one_sub_gammaCDF_div_density ha hr).comp ht
  -- the density along `t`
  have hmain : Tendsto (fun n : ℕ ↦ (n : ℝ) * gammaDensity a r (t n)) atTop (𝓝 (r * exp (-x))) := by
    have h1 : Tendsto (fun n ↦ (r * t n / y n) ^ (a - 1)) atTop (𝓝 1) := by
      simpa using hty.rpow_const (p := a - 1) (Or.inl one_ne_zero)
    have := (h1.const_mul (r * exp (-x)))
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hy.eventually_gt_atTop 0, eventually_gt_atTop 0, ht.eventually_gt_atTop 0]
      with n hy0 hn ht0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hexp : exp (-(r * t n)) = exp (-x) * ((n : ℝ)⁻¹ * ((y n ^ (a - 1))⁻¹ * Gamma a)) := by
      have : -(r * t n) = -x + (-y n + (-((a - 1) * log (y n)) + log (Gamma a))) := by
        simp only [ht_def]
        field_simp
        ring
      have hE : exp (-((a - 1) * log (y n))) = (y n ^ (a - 1))⁻¹ := by
        rw [exp_neg, mul_comm, ← rpow_def_of_pos hy0]
      have hn2 : exp (-y n) = (n : ℝ)⁻¹ := by
        rw [exp_neg, hy_def, exp_log hn']
      rw [this, exp_add, exp_add, exp_add, hn2, exp_log hGam, hE]
    simp only [gammaDensity]
    rw [hexp, div_rpow (mul_pos hr ht0).le hy0.le, mul_rpow hr.le ht0.le, rpow_sub_one hr.ne']
    have := (rpow_pos_of_pos hy0 (a - 1)).ne'
    have := (rpow_pos_of_pos hr a).ne'
    field_simp
  have := hT.mul hmain
  rw [one_div, inv_mul_cancel_left₀ hr.ne'] at this
  refine this.congr' ?_
  filter_upwards [ht.eventually_gt_atTop 0] with n ht0
  have hne := (gammaDensity_pos ha hr ht0).ne'
  show (1 - gammaCDF a r (t n)) / gammaDensity a r (t n) * ((n : ℝ) * gammaDensity a r (t n)) =
    (n : ℝ) * (1 - gammaCDF a r (t n))
  generalize gammaCDF a r (t n) = q
  field_simp

/-- **The Gamma law, with explicit norming constants**: with `a_n = 1 / r` and
`b_n = (log n + (a - 1) log log n - log Γ(a)) / r`, `F (a_n x + b_n) ^ n → exp (-e^{-x})` for every
`x`. -/
theorem tendsto_gammaCDF_pow (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ gammaCDF a r
      (r⁻¹ * x + (log n + (a - 1) * log (log n) - log (Gamma a)) / r) ^ n) atTop
      (𝓝 (standardGumbelCDF x)) := by
  rw [standardGumbelCDF_apply_eq]
  exact tendsto_pow_of_tendsto_mul_one_sub (tendsto_mul_one_sub_gammaCDF ha hr x)

/-- **The Gamma law is in `MDA(H_0)`**. This covers the Erlang laws, where `a` is
a positive integer. -/
theorem isInMDAGEV_gammaCDF (ha : 0 < a) (hr : 0 < r) : (gammaCDF a r).IsInMDAGEV 0 :=
  IsInMDAGumbel.isInMDAGEV <|
    (gammaCDF a r).isInMDAGumbel_of_tendsto_mul_one_sub (a := fun _ ↦ r⁻¹)
      (Eventually.of_forall fun _ ↦ inv_pos.2 hr) (tendsto_mul_one_sub_gammaCDF ha hr)

end Gamma

end CumulativeDistributionFunction
