import ExtremeValueTheory

/-!
# Known answers: regular variation, the GPD, subexponentiality, ruin and stable laws

References: [BGT] Bingham, Goldie, Teugels, *Regular Variation* (1987); [EKM] Embrechts,
Klüppelberg, Mikosch, *Modelling Extremal Events* (1997); [Feller] Feller, *An Introduction to
Probability Theory and Its Applications*, Vol. II (1971); [ST] Samorodnitsky, Taqqu, *Stable
Non-Gaussian Random Processes* (1994).
-/

open Real Filter Topology Set MeasureTheory ProbabilityTheory ExtremeValueTheory
open scoped NNReal
open ExtremeValueTheory.StableIntegral

namespace Test.KnownAnswers.HeavyTails

/-! ### Regular variation ([BGT, §1.4]) -/

/-- Uniqueness of the index of regular variation. -/
theorem rv_index_unique {f : ℝ → ℝ} {ρ σ : ℝ} (hρ : IsRegularlyVarying f ρ)
    (hσ : IsRegularlyVarying f σ) : ρ = σ := by
  have h := tendsto_nhds_unique (hρ.tendsto two_pos) (hσ.tendsto two_pos)
  have hlog := congrArg log h
  rw [log_rpow two_pos, log_rpow two_pos] at hlog
  exact mul_right_cancel₀ (log_pos one_lt_two).ne' hlog

/-- `x^α log x` is regularly varying with index `α` ([BGT, §1.4]: `x^α L(x)` with `L` slowly
varying). -/
theorem test_rpow_mul_log_rv (α : ℝ) : IsRegularlyVarying (fun x ↦ x ^ α * log x) α := by
  simpa using (IsRegularlyVarying.rpow_id α).mul isSlowlyVarying_log.isRegularlyVarying

/-- The index of `x^{-α}` is `-α`, and not `α` (for `α ≠ 0`). -/
theorem test_rpow_neg_index {α : ℝ} (hα : α ≠ 0) :
    IsRegularlyVarying (fun x ↦ x ^ (-α)) (-α) ∧ ¬ IsRegularlyVarying (fun x ↦ x ^ (-α)) α :=
  ⟨IsRegularlyVarying.rpow_id (-α), fun h ↦ hα (by
    have := rv_index_unique (IsRegularlyVarying.rpow_id (-α)) h; linarith)⟩

/-- `log` is slowly varying ([BGT, §1.2]) and hence has index `0`, not `1`. -/
theorem test_log_slowlyVarying :
    IsSlowlyVarying log ∧ ¬ IsRegularlyVarying log 1 :=
  ⟨isSlowlyVarying_log, fun h ↦ one_ne_zero (rv_index_unique h isSlowlyVarying_log.isRegularlyVarying)⟩

/-- `exp` is not regularly varying with any index: `e^{2x}/e^x = e^x → ∞` ([BGT, §1.4]). -/
theorem test_exp_not_rv (ρ : ℝ) : ¬ IsRegularlyVarying exp ρ := by
  intro h
  have h2 := h.tendsto two_pos
  have : Tendsto (fun x ↦ exp (2 * x) / exp x) atTop atTop :=
    tendsto_exp_atTop.congr fun x ↦ by rw [two_mul, exp_add, mul_div_cancel_right₀ _ (exp_pos _).ne']
  exact not_tendsto_nhds_of_tendsto_atTop this _ h2

/-- The Pareto law `Pareto(t, r)` has tail `(t/x)^r`: `P(X > 2) = 1/4` for `t = 1`, `r = 2`,
and its tail is regularly varying with index `-r` ([EKM, Table 1.2.6]). -/
theorem test_pareto_tail :
    tail (paretoMeasure 1 2) 2 = 1 / 4 ∧
      IsRegularlyVarying (tail (paretoMeasure 1 2)) (-2) := by
  refine ⟨?_, isRegularlyVarying_tail_paretoMeasure one_pos two_pos⟩
  rw [tail_paretoMeasure one_pos two_pos one_le_two]
  rw [one_rpow, one_mul, rpow_neg (by norm_num)]
  norm_num

/-! ### The generalized Pareto distribution ([EKM, Def. 3.4.9]) -/

/-- `Ḡ_{0,β}(x) = e^{-x/β}`: `Ḡ_{0,2}(2) = e⁻¹`. -/
theorem test_gpd_exponential : gpdSurvival 0 2 2 = exp (-1) := by
  rw [gpdSurvival_of_eq_zero]; norm_num

/-- `Ḡ_{1,1}(1) = (1 + 1)^{-1} = 1/2`. -/
theorem test_gpd_one_one : gpdSurvival 1 1 1 = 1 / 2 := by
  rw [gpdSurvival_of_ne_zero_of_nonneg one_ne_zero (by norm_num)]; norm_num [rpow_neg_one]

/-- `Ḡ_{1/2,1}(2) = (1 + 1)^{-2} = 1/4`: fails if the exponent were `-ξ` instead of `-1/ξ`. -/
theorem test_gpd_half_one : gpdSurvival (1 / 2) 1 2 = 1 / 4 := by
  rw [gpdSurvival_of_ne_zero_of_nonneg (by norm_num) (by norm_num)]
  rw [show (1 + 1 / 2 * 2 / 1 : ℝ) = 2 by norm_num, show -(1 / (1 / 2 : ℝ)) = -2 by norm_num,
    rpow_neg (by norm_num)]
  norm_num

/-- `ξ = -1`: `Ḡ_{-1,1}` is the uniform survival function `1 - x` on `[0, 1]`, and it vanishes
beyond the right endpoint `-β/ξ = 1` ([EKM, Def. 3.4.9]). -/
theorem test_gpd_uniform :
    gpdSurvival (-1) 1 (1 / 4) = 3 / 4 ∧ gpdSurvival (-1) 1 2 = 0 := by
  have h := gpdSurvival_neg_inv (α := 1) one_pos
  norm_num at h
  refine ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩

/-- `Ḡ_{-1/2,1}(1) = (1 - 1/2)^2 = 1/4`. -/
theorem test_gpd_neg_half : gpdSurvival (-1 / 2) 1 1 = 1 / 4 := by
  rw [gpdSurvival_neg_inv two_pos]
  norm_num [rpow_two]

/-- **The excess law of a Pareto tail is a GPD** ([EKM, Example 3.4.13 / Theorem 3.4.13(c)]):
for `F̄(x) = x^{-α}` and `u > 0`, `F̄(u + x)/F̄(u) = Ḡ_{1/α, u/α}(x)`. Fails if the GPD
shape-scale convention were different (e.g. scale `u` instead of `u/α`). -/
theorem test_pareto_excess_is_gpd {α u x : ℝ} (hα : 0 < α) (hu : 0 < u) (hx : 0 ≤ x) :
    excessSurvival (fun y ↦ y ^ (-α)) u x = gpdSurvival (1 / α) (u / α) x := by
  rw [excessSurvival, gpdSurvival_of_ne_zero_of_nonneg (one_div_pos.2 hα).ne' (by positivity), one_div_one_div,
    ← div_rpow (by linarith) hu.le]
  congr 1
  field_simp

/-- **Lack of memory**: the excess law of an exponential tail is the same exponential,
`Ḡ_{0,β}` ([EKM, §3.4]). -/
theorem test_exponential_excess {β u x : ℝ} :
    excessSurvival (fun y ↦ exp (-y / β)) u x = gpdSurvival 0 β x := by
  rw [excessSurvival, gpdSurvival_of_eq_zero, ← exp_sub]
  congr 1
  ring

/-- **Mean excess of the exponential GPD**: `e(u) = β` for `Ḡ_{0,β}` ([EKM, Theorem 3.4.13(e)]
with `ξ = 0`). -/
theorem test_meanExcess_gpd_zero {β : ℝ} (hβ : 0 < β) (u : ℝ) :
    meanExcess (gpdSurvival 0 β) u = β := by
  have hint : ∫ t in Ioi u, gpdSurvival 0 β t = β * exp (-u / β) := by
    simp only [gpdSurvival_of_eq_zero]
    have hd : ∀ t ∈ Ici u, HasDerivAt (fun t ↦ -β * exp (-t / β)) (exp (-t / β)) t := by
      intro t _
      have := ((hasDerivAt_neg t).div_const β).exp.const_mul (-β)
      convert this using 1
      field_simp
    have hlim : Tendsto (fun t ↦ -β * exp (-t / β)) atTop (𝓝 0) := by
      have : Tendsto (fun t ↦ -t / β) atTop atBot := by
        simp_rw [neg_div]
        exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const hβ)
      simpa using (tendsto_exp_atBot.comp this).const_mul (-β)
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun t _ ↦ (exp_pos _).le) hlim]
    ring
  rw [meanExcess, hint, gpdSurvival_of_eq_zero, mul_div_cancel_right₀ _ (exp_pos _).ne']

/-- **Mean excess of the GPD**: `e(u) = (β + ξ u)/(1 - ξ)` for `0 < ξ < 1`, `u ≥ 0`
([EKM, Theorem 3.4.13(e)]). Fails if the sign of `ξ u` or the factor `1/(1 - ξ)` were wrong. -/
theorem test_meanExcess_gpd {ξ β u : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hβ : 0 < β) (hu : 0 ≤ u) :
    meanExcess (gpdSurvival ξ β) u = (β + ξ * u) / (1 - ξ) := by
  set c := 1 + ξ * u / β with hc_def
  have hc : 0 < c := by have : 0 ≤ ξ * u / β := by positivity
                        linarith
  have hk : 0 < ξ / β := div_pos hξ0 hβ
  have ha : -(1 / ξ) < -1 := by
    have : 1 < 1 / ξ := by rw [lt_div_iff₀ hξ0]; linarith
    linarith
  have hint : ∫ t in Ioi u, gpdSurvival ξ β t = β / ξ * (c ^ (-(1 / ξ) + 1) / (1 / ξ - 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ gpdSurvival_of_ne_zero_of_nonneg hξ0.ne'
      (by have : 0 ≤ ξ * t / β := div_nonneg (mul_nonneg hξ0.le (hu.trans (le_of_lt ht))) hβ.le
          linarith)]
    set e := -(1 / ξ) with he
    have he1 : e + 1 < 0 := by linarith
    have hpos : ∀ t ∈ Ici u, 0 < 1 + ξ * t / β := fun t ht ↦ by
      have : 0 ≤ ξ * t / β := div_nonneg (mul_nonneg hξ0.le (hu.trans ht)) hβ.le
      linarith
    have hd : ∀ t ∈ Ici u, HasDerivAt (fun t ↦ β / ξ / (e + 1) * (1 + ξ * t / β) ^ (e + 1))
        ((1 + ξ * t / β) ^ e) t := by
      intro t ht
      have h0 : HasDerivAt (fun t ↦ 1 + ξ * t / β) (ξ / β) t := by
        simpa using (((hasDerivAt_id t).const_mul ξ).div_const β).const_add 1
      have := (h0.rpow_const (p := e + 1) (Or.inl (hpos t ht).ne')).const_mul (β / ξ / (e + 1))
      convert this using 1
      rw [add_sub_cancel_right]
      have := he1.ne
      field_simp
    have hlim : Tendsto (fun t ↦ β / ξ / (e + 1) * (1 + ξ * t / β) ^ (e + 1)) atTop (𝓝 0) := by
      have hb : Tendsto (fun t ↦ 1 + ξ * t / β) atTop atTop :=
        tendsto_atTop_add_const_left _ 1 ((tendsto_id.const_mul_atTop hξ0).atTop_div_const hβ)
      have := (tendsto_rpow_neg_atTop (y := -(e + 1)) (by linarith)).comp hb
      simpa using this.const_mul (β / ξ / (e + 1))
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun t ht ↦ (rpow_pos_of_pos
      (hpos t (Ioi_subset_Ici_self ht)) _).le) hlim]
    have : 1 / ξ - 1 = -(e + 1) := by rw [he]; ring
    rw [this, ← hc_def]
    field_simp
    ring
  rw [meanExcess, hint, gpdSurvival_of_ne_zero_of_nonneg hξ0.ne' hc.le, ← hc_def, rpow_add hc, rpow_one]
  have hcpow : 0 < c ^ (-(1 / ξ)) := rpow_pos_of_pos hc _
  have h1ξ : 1 / ξ - 1 = (1 - ξ) / ξ := by field_simp
  rw [h1ξ, hc_def]
  have : (1 - ξ) ≠ 0 := by linarith
  field_simp

/-! ### Subexponential distributions ([EKM, §1.3]) -/

/-- Pareto laws are subexponential ([EKM, Corollary 1.3.2]). -/
theorem test_pareto_subexponential : IsSubexponential (paretoMeasure 1 2) :=
  isSubexponential_paretoMeasure one_pos two_pos

/-- Weibull laws with tail `exp(-√x)` (shape `τ = 1/2 < 1`) are subexponential
([EKM, Table 1.4.4]). -/
theorem test_weibull_half_subexponential :
    IsSubexponential (weibullTailLaw (1 / 2) (by norm_num)) :=
  isSubexponential_weibullTailLaw _ (by norm_num)

/-- The lognormal law is subexponential ([EKM, Table 1.4.4]). -/
theorem test_lognormal_subexponential : IsSubexponential (lognormal 0 1) :=
  IsSubexponential.lognormal 0 one_ne_zero

/-- **The exponential law is not subexponential** ([EKM, §1.3]): it is not long-tailed,
`F̄(x - 1)/F̄(x) = e ≠ 1`. -/
theorem test_exponential_not_subexponential :
    ¬ IsSubexponential (weibullTailLaw 1 one_pos) := by
  intro h
  have h1 := h.tendsto_tail_sub_div 1
  have he : Tendsto (fun x ↦ tail (weibullTailLaw 1 one_pos) (x - 1) /
      tail (weibullTailLaw 1 one_pos) x) atTop (𝓝 (exp 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [tail_weibullTailLaw one_pos (by linarith), tail_weibullTailLaw one_pos (by linarith),
      rpow_one, rpow_one, ← exp_sub]
    ring_nf
  have := tendsto_nhds_unique he h1
  rw [exp_eq_one_iff] at this
  norm_num at this

/-- The Weibull law with shape `τ = 2` (lighter than exponential) is not subexponential. -/
theorem test_weibull_two_not_subexponential :
    ¬ IsSubexponential (weibullTailLaw 2 two_pos) := by
  intro h
  have h1 := h.tendsto_tail_sub_div 1
  have he : Tendsto (fun x ↦ tail (weibullTailLaw 2 two_pos) (x - 1) /
      tail (weibullTailLaw 2 two_pos) x) atTop atTop := by
    refine (tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ (-1)
      (tendsto_id.const_mul_atTop two_pos))).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [tail_weibullTailLaw two_pos (by linarith), tail_weibullTailLaw two_pos (by linarith),
      ← exp_sub, rpow_two, rpow_two]
    simp only [Function.comp, id]
    ring_nf
  exact not_tendsto_nhds_of_tendsto_atTop he _ h1

/-! ### Ruin ([EKM, §1.2]) -/

private theorem convPow_dirac_one (n : ℕ) : Subexp.convPow (Measure.dirac (1 : ℝ)) n =
    Measure.dirac (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Subexp.convPow_succ, ih, Measure.dirac_conv_dirac]
    push_cast; ring_nf

/-- **Ruin with zero initial capital**: `ψ(0) = 1/(1 + ρ)` ([EKM, Theorem 1.2.2 and (1.13)];
the value does not depend on the claim law, here the integrated tail law is `δ₁`). Fails if
the geometric weights `(1 + ρ)^{-n}` or the prefactor `ρ/(1 + ρ)` were off. -/
theorem test_pkRuin_zero {ρ : ℝ} (hρ : 0 < ρ) :
    pkRuin ρ (Measure.dirac 1) 0 = 1 / (1 + ρ) := by
  set q := 1 / (1 + ρ) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  have htail : ∀ n : ℕ, tail (Subexp.convPow (Measure.dirac (1 : ℝ)) n) 0 =
      if n = 0 then 0 else 1 := by
    intro n
    rw [convPow_dirac_one, tail, measureReal_def, Measure.dirac_apply' _ measurableSet_Ioi]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (0 : ℝ) < n := by exact_mod_cast hn
      simp [Set.indicator, this, hn.ne']
  have hsum : ∑' n : ℕ, q ^ n * tail (Subexp.convPow (Measure.dirac (1 : ℝ)) n) 0 =
      q / (1 - q) := by
    simp_rw [htail]
    have hs := summable_geometric_of_lt_one hq0 hq1
    have hf : Summable fun n : ℕ ↦ q ^ n * (if n = 0 then (0 : ℝ) else 1) :=
      hs.of_nonneg_of_le (fun n ↦ by split_ifs <;> simp [pow_nonneg hq0])
        (fun n ↦ by split_ifs <;> simp [pow_nonneg hq0])
    rw [hf.tsum_eq_zero_add]
    simp only [pow_zero, ↓reduceIte, mul_zero, zero_add, Nat.add_one_ne_zero, mul_one, pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
    have : 1 - q ≠ 0 := by linarith
    field_simp
  rw [pkRuin, ← hq, hsum, hq]
  have : (1 + ρ) ≠ 0 := by linarith
  have := hρ.ne'
  field_simp
  ring_nf
  field_simp

/-- **Embrechts–Veraverbeke** ([EKM, Theorem 1.3.6]): for a subexponential integrated tail law,
`ψ(u) ~ ρ⁻¹ F̄_I(u)`. Instantiated with a Pareto law and `ρ = 1/2`: `ψ(u)/F̄_I(u) → 2`. -/
theorem test_ruin_pareto :
    Tendsto (fun u ↦ pkRuin (1 / 2) (paretoMeasure 1 2) u / tail (paretoMeasure 1 2) u)
      atTop (𝓝 2) := by
  have := isProbabilityMeasure_paretoMeasure (one_pos : (0 : ℝ) < 1) two_pos
  simpa using IsSubexponential.tendsto_pkRuin_div test_pareto_subexponential
    (by norm_num : (0 : ℝ) < 1 / 2)

/-! ### Stable laws ([Feller, §VI.1, §XVII]; [ST, §1.1]) -/

/-- A symmetric `α`-stable law has stable index `α` (norming constants `n^{1/α}`). -/
theorem isStableIndex_of_isSymmStable {α c : ℝ} {μ : Measure ℝ} (h : IsSymmStable α c μ)
    (hα : 0 < α) (hc : 0 < c) : IsStableIndex α μ := by
  refine ⟨h.isStable hα hc, fun n hn ↦ ⟨0, ?_⟩⟩
  have := h.1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℝ) * c = c * |(n : ℝ) ^ α⁻¹| ^ α := by
    rw [abs_of_pos (rpow_pos_of_pos hn' _), rpow_inv_rpow hn'.le hα.ne']
    ring
  have h2 := (e ▸ h.convPow n).unique (h.map_mul ((n : ℝ) ^ α⁻¹))
  simpa using h2

/-- **The normal law is `2`-stable** ([Feller, §VI.1]): `stableIndex N(0, v) = 2`, with
characteristic function `exp(-v t²/2)`, i.e. `c = v/2`. -/
theorem test_gaussian_stableIndex {v : ℝ≥0} (hv : v ≠ 0) :
    stableIndex (gaussianReal 0 v) = 2 :=
  (isStableIndex_of_isSymmStable (isSymmStable_gaussianReal v) two_pos
    (by have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (by exact_mod_cast hv.symm); positivity)
    ).stableIndex_eq

/-- **The Cauchy law is `1`-stable** ([Feller, §VI.1]): `stableIndex Cauchy(0, γ) = 1`, with
characteristic function `exp(-γ |t|)`. -/
theorem test_cauchy_stableIndex {γ : ℝ≥0} (hγ : γ ≠ 0) :
    stableIndex (cauchyMeasure 0 γ) = 1 :=
  (isStableIndex_of_isSymmStable (isSymmStable_cauchyMeasure γ) one_pos
    (lt_of_le_of_ne γ.2 (by exact_mod_cast hγ.symm))).stableIndex_eq

/-- The Gaussian law is not `1`-stable. -/
theorem test_gaussian_not_index_one : ¬ IsStableIndex 1 (gaussianReal 0 1) := fun h ↦ by
  have := h.stableIndex_eq
  rw [test_gaussian_stableIndex one_ne_zero] at this
  norm_num at this

/-- `C_1 = π/2` ([Feller, §XVII.4]): the Cauchy constant. -/
theorem test_stableConst_one : stableConst 1 = π / 2 := stableConst_one

/-- `C_{1/2} = Γ(1/2) cos(π/4) = √(π/2)` ([Feller, §XVII.4, (4.9)]). -/
theorem test_stableConst_half : stableConst (1 / 2) = √(π / 2) := by
  rw [stableConst_eq_Gamma_mul_cos (by norm_num) (by norm_num) (by norm_num)]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Gamma_one_half_eq,
    show π * (1 / 2) / 2 = π / 4 by ring, cos_pi_div_four, sqrt_div' π (by norm_num : (0:ℝ) ≤ 2)]
  have h2 : (0 : ℝ) < √2 := by positivity
  field_simp
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- `C_{3/2} = Γ(-1/2) cos(3π/4) = √(2π) > 0` ([Feller, §XVII.4]): both factors are negative
for `1 < α < 2`. -/
theorem test_stableConst_three_halves : stableConst (3 / 2) = √(2 * π) := by
  rw [stableConst_eq_Gamma_mul_cos (by norm_num) (by norm_num) (by norm_num)]
  have hG : Gamma (1 - 3 / 2) = -2 * √π := by
    have := Gamma_add_one (s := -1 / 2) (by norm_num)
    rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Gamma_one_half_eq] at this
    rw [show (1 : ℝ) - 3 / 2 = -1 / 2 by norm_num]
    linarith
  have hc : cos (π * (3 / 2) / 2) = -(√2 / 2) := by
    rw [show π * (3 / 2) / 2 = π - π / 4 by ring, cos_pi_sub, cos_pi_div_four]
  rw [hG, hc, sqrt_mul (by norm_num)]
  ring

end Test.KnownAnswers.HeavyTails
