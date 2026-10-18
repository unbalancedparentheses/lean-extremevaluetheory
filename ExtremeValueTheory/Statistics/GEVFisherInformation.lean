/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLEFisher
import ExtremeValueTheory.ForMathlib.Analysis.SpecialFunctions.Gamma.Trigamma

/-!
# The full Fisher information of the GEV family

TODO
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

/-! ### The second derivative of `Γ` at `2` and `3` -/

namespace Complex

/-- `Γ''(s + 1) = 2 Γ'(s) + s Γ''(s)` on the right half-plane (differentiate
`Γ'(s + 1) = Γ(s) + s Γ'(s)`). -/
theorem deriv_deriv_Gamma_add_one {s : ℂ} (hs : 0 < s.re) :
    deriv (deriv Gamma) (s + 1) = 2 * deriv Gamma s + s * deriv (deriv Gamma) s := by
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hD : ∀ z : ℂ, 0 < z.re → HasDerivAt (deriv Gamma) (deriv (deriv Gamma) z) z :=
    fun z hz => (hasDerivAt_deriv_Gamma_of_re_pos hz).differentiableAt.hasDerivAt
  have hL : HasDerivAt (fun z => deriv Gamma (z + 1)) (deriv (deriv Gamma) (s + 1)) s :=
    (hD _ hs1).comp_add_const s 1
  have hG : HasDerivAt Gamma (deriv Gamma s) s :=
    (differentiableAt_Gamma s fun m h => by
      have : s.re = -m := by simp [h]
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      linarith).hasDerivAt
  have hR := hG.add ((hasDerivAt_id s).mul (hD s hs))
  have heq : (fun z => deriv Gamma (z + 1)) =ᶠ[𝓝 s]
      fun z => Gamma z + id z * deriv Gamma z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact deriv_Gamma_add_one z fun h => by simp [h] at hz
  have := hL.unique (hR.congr_of_eventuallyEq heq)
  rw [this]
  simp only [id, one_mul]
  ring

/-- `Γ'(2) = 1 - γ`. -/
theorem deriv_Gamma_two : deriv Gamma 2 = 1 - Real.eulerMascheroniConstant := by
  have := deriv_Gamma_add_one 1 one_ne_zero
  rw [show (1 : ℂ) + 1 = 2 by norm_num, hasDerivAt_Gamma_one.deriv, Gamma_one] at this
  rw [this]; ring

/-- `Γ''(2) = γ² + π²/6 - 2γ`. -/
theorem deriv_deriv_Gamma_two :
    deriv (deriv Gamma) 2 =
      Real.eulerMascheroniConstant ^ 2 + π ^ 2 / 6 - 2 * Real.eulerMascheroniConstant := by
  have := deriv_deriv_Gamma_add_one (s := 1) (by norm_num)
  rw [show (1 : ℂ) + 1 = 2 by norm_num, hasDerivAt_Gamma_one.deriv, deriv_deriv_Gamma_one]
    at this
  rw [this]; ring

/-- `Γ''(3) = 2γ² + π²/3 - 6γ + 2`. -/
theorem deriv_deriv_Gamma_three :
    deriv (deriv Gamma) 3 = 2 * Real.eulerMascheroniConstant ^ 2 + π ^ 2 / 3 -
      6 * Real.eulerMascheroniConstant + 2 := by
  have := deriv_deriv_Gamma_add_one (s := 2) (by norm_num)
  rw [show (2 : ℂ) + 1 = 3 by norm_num, deriv_Gamma_two, deriv_deriv_Gamma_two] at this
  rw [this]; ring

end Complex

namespace ExtremeValueTheory

/-! ### Logarithmic moments of the exponential law -/

section LogMoments

/-- `|log t| ≤ (t^ε + t^{-ε})/ε` for `t > 0`, `ε > 0`. -/
lemma abs_log_le_rpow_add_rpow {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    |log t| ≤ (t ^ ε + t ^ (-ε)) / ε := by
  have h1 : log t ≤ t ^ ε / ε := log_le_rpow_div ht.le hε
  have h2 : -t ^ (-ε) / ε ≤ log t := neg_rpow_div_le_log ht.le hε
  have h3 : 0 ≤ t ^ ε / ε := by positivity
  have h4 : 0 ≤ t ^ (-ε) / ε := by positivity
  rw [abs_le, add_div]
  constructor
  · rw [neg_div] at h2; linarith
  · linarith

/-- `∫_0^∞ e^{-t} t^a |log t| dt < ∞` for `a > -1`. -/
lemma integrableOn_exp_neg_mul_rpow_mul_log {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun t => exp (-t) * (t ^ a * log t)) (Ioi 0) := by
  set ε := (a + 1) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hb : IntegrableOn (fun t => (exp (-t) * t ^ (a + ε) + exp (-t) * t ^ (a + -ε)) / ε)
      (Ioi 0) :=
    ((integrableOn_exp_neg_mul_rpow (by linarith)).add
      (integrableOn_exp_neg_mul_rpow (by rw [hε_def]; linarith))).div_const ε
  refine hb.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
  have ht : 0 < t := ht
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _),
    abs_of_pos (rpow_pos_of_pos ht a), rpow_add ht, rpow_add ht]
  have := abs_log_le_rpow_add_rpow hε ht
  calc exp (-t) * (t ^ a * |log t|) ≤ exp (-t) * (t ^ a * ((t ^ ε + t ^ (-ε)) / ε)) := by
        gcongr
    _ = _ := by ring

/-- `∫_0^∞ e^{-t} t^a (log t)² dt < ∞` for `a > -1`. -/
lemma integrableOn_exp_neg_mul_rpow_mul_log_sq {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun t => exp (-t) * (t ^ a * log t ^ 2)) (Ioi 0) := by
  set ε := (a + 1) / 4 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hb : IntegrableOn (fun t => (exp (-t) * t ^ (a + 2 * ε) + 2 * (exp (-t) * t ^ a) +
      exp (-t) * t ^ (a + -(2 * ε))) / ε ^ 2) (Ioi 0) :=
    (((integrableOn_exp_neg_mul_rpow (by linarith)).add
      ((integrableOn_exp_neg_mul_rpow ha).const_mul 2)).add
      (integrableOn_exp_neg_mul_rpow (by rw [hε_def]; linarith))).div_const _
  refine hb.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
  have ht : 0 < t := ht
  have hl := abs_log_le_rpow_add_rpow hε ht
  have hsq : log t ^ 2 ≤ ((t ^ ε + t ^ (-ε)) / ε) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
  have e1 : t ^ (a + 2 * ε) = t ^ a * (t ^ ε) ^ 2 := by
    rw [rpow_add ht, ← rpow_natCast, ← rpow_mul ht.le]; ring_nf
  have e2 : t ^ (a + -(2 * ε)) = t ^ a * (t ^ (-ε)) ^ 2 := by
    rw [rpow_add ht, ← rpow_natCast, ← rpow_mul ht.le]; ring_nf
  have e3 : t ^ ε * t ^ (-ε) = 1 := by
    rw [← rpow_add ht, add_neg_cancel, rpow_zero]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), e1, e2]
  calc exp (-t) * (t ^ a * log t ^ 2) ≤
        exp (-t) * (t ^ a * ((t ^ ε + t ^ (-ε)) / ε) ^ 2) := by gcongr
    _ = (exp (-t) * (t ^ a * (t ^ ε) ^ 2) + 2 * (exp (-t) * t ^ a * (t ^ ε * t ^ (-ε))) +
          exp (-t) * (t ^ a * (t ^ (-ε)) ^ 2)) / ε ^ 2 := by
        field_simp; ring
    _ = _ := by rw [e3]; ring

/-- `∫_0^∞ e^{-t} t^a log t dt = Γ'(a + 1)` for `a > -1`. -/
lemma integral_exp_neg_mul_rpow_mul_log {a : ℝ} (ha : -1 < a) :
    ∫ t in Ioi 0, exp (-t) * (t ^ a * log t) = deriv Gamma (a + 1) := by
  rw [(Real.hasDerivAt_Gamma_of_pos (by linarith : 0 < a + 1)).deriv]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [add_sub_cancel_right]
  ring

lemma differentiableAt_Gamma_of_pos {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ Gamma s :=
  (Real.hasDerivAt_Gamma_of_pos hs).differentiableAt

/-- `Γ'(s + 1) = Γ(s) + s Γ'(s)` for `s > 0`. -/
theorem deriv_Gamma_add_one_of_pos {s : ℝ} (hs : 0 < s) :
    deriv Gamma (s + 1) = Gamma s + s * deriv Gamma s := by
  have hL : HasDerivAt (fun z => Gamma (z + 1)) (deriv Gamma (s + 1)) s :=
    (differentiableAt_Gamma_of_pos (by linarith : 0 < s + 1)).hasDerivAt.comp_add_const s 1
  have hR := (hasDerivAt_id s).mul (differentiableAt_Gamma_of_pos hs).hasDerivAt
  have heq : (fun z => Gamma (z + 1)) =ᶠ[𝓝 s] fun z => id z * Gamma z := by
    filter_upwards [lt_mem_nhds hs] with z hz
    exact Real.Gamma_add_one hz.ne'
  rw [hL.unique (hR.congr_of_eventuallyEq heq)]
  simp only [id, one_mul]

/-- `∫_0^∞ e^{-t} (log t)² dt = γ² + π²/6`. -/
lemma integral_exp_neg_mul_log_sq :
    ∫ t in Ioi 0, exp (-t) * log t ^ 2 = eulerMascheroniConstant ^ 2 + π ^ 2 / 6 := by
  rw [← integral_log_sq_mul_exp_neg]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring

/-- `∫_0^∞ e^{-t} t (log t)² dt = Γ''(2) = γ² + π²/6 - 2γ`. -/
lemma integral_exp_neg_mul_mul_log_sq :
    ∫ t in Ioi 0, exp (-t) * (t * log t ^ 2) =
      eulerMascheroniConstant ^ 2 + π ^ 2 / 6 - 2 * eulerMascheroniConstant := by
  have h := (Complex.hasDerivAt_deriv_Gamma_of_re_pos (s := 2) (by norm_num)).deriv
  rw [Complex.deriv_deriv_Gamma_two] at h
  have e : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((2 : ℂ) - 1) * ((log t ^ 2 * exp (-t) : ℝ) : ℂ) =
      ((∫ t in Ioi 0, exp (-t) * (t * log t ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show (2 : ℂ) - 1 = 1 by norm_num, Complex.cpow_one]
    push_cast; ring
  rw [e] at h
  exact_mod_cast h.symm

/-- `∫_0^∞ e^{-t} t² (log t)² dt = Γ''(3) = 2γ² + π²/3 - 6γ + 2`. -/
lemma integral_exp_neg_mul_sq_mul_log_sq :
    ∫ t in Ioi 0, exp (-t) * (t ^ 2 * log t ^ 2) =
      2 * eulerMascheroniConstant ^ 2 + π ^ 2 / 3 - 6 * eulerMascheroniConstant + 2 := by
  have h := (Complex.hasDerivAt_deriv_Gamma_of_re_pos (s := 3) (by norm_num)).deriv
  rw [Complex.deriv_deriv_Gamma_three] at h
  have e : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((3 : ℂ) - 1) * ((log t ^ 2 * exp (-t) : ℝ) : ℂ) =
      ((∫ t in Ioi 0, exp (-t) * (t ^ 2 * log t ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show (3 : ℂ) - 1 = 2 by norm_num, Complex.cpow_ofNat]
    push_cast; ring
  rw [e] at h
  exact_mod_cast h.symm

end LogMoments

/-! ### Logarithmic Gamma moments on the exponential scale -/

section LogRows

variable {β : ℝ}

private lemma logRow_eq {t : ℝ} (ht : 0 < t) (β a b c : ℝ) :
    exp (-t) * (t ^ β * log t * (a + b * t + c * t ^ 2)) =
      a * (exp (-t) * (t ^ β * log t)) + b * (exp (-t) * (t ^ (β + 1) * log t)) +
        c * (exp (-t) * (t ^ (β + 2) * log t)) := by
  rw [rpow_add ht, rpow_add ht, rpow_one, rpow_two]
  ring

lemma integrableOn_logRow (hβ : -1 < β) (a b c : ℝ) :
    IntegrableOn (fun t => exp (-t) * (t ^ β * log t * (a + b * t + c * t ^ 2))) (Ioi 0) :=
  IntegrableOn.congr_fun ((((integrableOn_exp_neg_mul_rpow_mul_log hβ).const_mul a).add
    ((integrableOn_exp_neg_mul_rpow_mul_log (a := β + 1) (by linarith)).const_mul b)).add
    ((integrableOn_exp_neg_mul_rpow_mul_log (a := β + 2) (by linarith)).const_mul c))
    (fun t ht => (logRow_eq ht β a b c).symm) measurableSet_Ioi

/-- `∫_0^∞ e^{-t} t^β log t (a + b t + c t²) dt
= Γ(β + 1)(b + (2β + 3) c) + Γ'(β + 1)(a + (β + 1) b + (β + 2)(β + 1) c)`. -/
theorem integral_logRow (hβ : -1 < β) (a b c : ℝ) :
    ∫ t in Ioi 0, exp (-t) * (t ^ β * log t * (a + b * t + c * t ^ 2)) =
      Gamma (β + 1) * (b + (2 * β + 3) * c) +
        deriv Gamma (β + 1) * (a + (β + 1) * b + (β + 2) * (β + 1) * c) := by
  have i0 := integrableOn_exp_neg_mul_rpow_mul_log hβ
  have i1 := integrableOn_exp_neg_mul_rpow_mul_log (a := β + 1) (by linarith)
  have i2 := integrableOn_exp_neg_mul_rpow_mul_log (a := β + 2) (by linarith)
  have i01 : IntegrableOn (fun t => a * (exp (-t) * (t ^ β * log t)) +
      b * (exp (-t) * (t ^ (β + 1) * log t))) (Ioi 0) := (i0.const_mul a).add (i1.const_mul b)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => logRow_eq ht β a b c),
    integral_add i01 (i2.const_mul c),
    integral_add (i0.const_mul a) (i1.const_mul b), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_exp_neg_mul_rpow_mul_log hβ,
    integral_exp_neg_mul_rpow_mul_log (by linarith),
    integral_exp_neg_mul_rpow_mul_log (by linarith)]
  have g1 : deriv Gamma (β + 1 + 1) = Gamma (β + 1) + (β + 1) * deriv Gamma (β + 1) :=
    deriv_Gamma_add_one_of_pos (by linarith)
  have g2 : deriv Gamma (β + 2 + 1) = Gamma (β + 2) + (β + 2) * deriv Gamma (β + 2) :=
    deriv_Gamma_add_one_of_pos (by linarith)
  have g3 : Gamma (β + 2) = (β + 1) * Gamma (β + 1) := by
    rw [show β + 2 = β + 1 + 1 by ring, Gamma_add_one (by linarith)]
  have g4 : deriv Gamma (β + 2) = Gamma (β + 1) + (β + 1) * deriv Gamma (β + 1) := by
    rw [show β + 2 = β + 1 + 1 by ring]; exact g1
  rw [g1, g2, g3, g4]
  ring

lemma integrableOn_exp_neg_mul_log_sq :
    IntegrableOn (fun t => exp (-t) * log t ^ 2) (Ioi 0) :=
  (integrableOn_exp_neg_mul_rpow_mul_log_sq (a := 0) (by norm_num)).congr_fun
    (fun t _ => by simp) measurableSet_Ioi

lemma integrableOn_exp_neg_mul_mul_log_sq :
    IntegrableOn (fun t => exp (-t) * (t * log t ^ 2)) (Ioi 0) :=
  (integrableOn_exp_neg_mul_rpow_mul_log_sq (a := 1) (by norm_num)).congr_fun
    (fun t _ => by simp) measurableSet_Ioi

lemma integrableOn_exp_neg_mul_sq_mul_log_sq :
    IntegrableOn (fun t => exp (-t) * (t ^ 2 * log t ^ 2)) (Ioi 0) :=
  (integrableOn_exp_neg_mul_rpow_mul_log_sq (a := 2) (by norm_num)).congr_fun
    (fun t _ => by simp) measurableSet_Ioi

private lemma logSqRow_eq (t a b c : ℝ) :
    exp (-t) * (log t ^ 2 * (a + b * t + c * t ^ 2)) =
      a * (exp (-t) * log t ^ 2) + b * (exp (-t) * (t * log t ^ 2)) +
        c * (exp (-t) * (t ^ 2 * log t ^ 2)) := by
  ring

lemma integrableOn_logSqRow (a b c : ℝ) :
    IntegrableOn (fun t => exp (-t) * (log t ^ 2 * (a + b * t + c * t ^ 2))) (Ioi 0) :=
  IntegrableOn.congr_fun (((integrableOn_exp_neg_mul_log_sq.const_mul a).add
    (integrableOn_exp_neg_mul_mul_log_sq.const_mul b)).add
    (integrableOn_exp_neg_mul_sq_mul_log_sq.const_mul c))
    (fun t _ => (logSqRow_eq t a b c).symm) measurableSet_Ioi

/-- `∫_0^∞ e^{-t} (log t)² (a + b t + c t²) dt = a Γ''(1) + b Γ''(2) + c Γ''(3)`, with
`Γ''(1) = γ² + π²/6`, `Γ''(2) = γ² + π²/6 - 2γ`, `Γ''(3) = 2γ² + π²/3 - 6γ + 2`. -/
theorem integral_logSqRow (a b c : ℝ) :
    ∫ t in Ioi 0, exp (-t) * (log t ^ 2 * (a + b * t + c * t ^ 2)) =
      a * (eulerMascheroniConstant ^ 2 + π ^ 2 / 6) +
        b * (eulerMascheroniConstant ^ 2 + π ^ 2 / 6 - 2 * eulerMascheroniConstant) +
        c * (2 * eulerMascheroniConstant ^ 2 + π ^ 2 / 3 - 6 * eulerMascheroniConstant + 2) := by
  have i0 := integrableOn_exp_neg_mul_log_sq
  have i1 := integrableOn_exp_neg_mul_mul_log_sq
  have i2 := integrableOn_exp_neg_mul_sq_mul_log_sq
  have i01 : IntegrableOn (fun t => a * (exp (-t) * log t ^ 2) +
      b * (exp (-t) * (t * log t ^ 2))) (Ioi 0) := (i0.const_mul a).add (i1.const_mul b)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => logSqRow_eq t a b c),
    integral_add i01 (i2.const_mul c),
    integral_add (i0.const_mul a) (i1.const_mul b), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_exp_neg_mul_log_sq, integral_exp_neg_mul_mul_log_sq,
    integral_exp_neg_mul_sq_mul_log_sq]

end LogRows

/-! ### Expectations of logarithmic polynomials against the GEV law -/

section LogPoly

variable {ξ μ σ : ℝ} {h : ℝ → ℝ}
  {a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ d₀ e₀ f₀ d₁ e₁ f₁ g₀ h₀ k₀ : ℝ}

/-- The combinations of `t^k (t^ξ)^j`, `t^k log t`, `t^k t^ξ log t` and `t^k (log t)²`,
`k, j ≤ 2`, whose expectations under the exponential law are explicit. -/
noncomputable def gevLogPoly (ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ d₀ e₀ f₀ d₁ e₁ f₁ g₀ h₀ k₀ t : ℝ) :
    ℝ :=
  gevPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t +
    log t * ((d₀ + e₀ * t + f₀ * t ^ 2) + t ^ ξ * (d₁ + e₁ * t + f₁ * t ^ 2)) +
    log t ^ 2 * (g₀ + h₀ * t + k₀ * t ^ 2)

private lemma exp_neg_mul_gevLogPoly (t : ℝ) :
    exp (-t) * gevLogPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ d₀ e₀ f₀ d₁ e₁ f₁ g₀ h₀ k₀ t =
      exp (-t) * gevPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t +
        exp (-t) * (t ^ (0 : ℝ) * log t * (d₀ + e₀ * t + f₀ * t ^ 2)) +
        exp (-t) * (t ^ ξ * log t * (d₁ + e₁ * t + f₁ * t ^ 2)) +
        exp (-t) * (log t ^ 2 * (g₀ + h₀ * t + k₀ * t ^ 2)) := by
  rw [gevLogPoly, rpow_zero]
  ring

lemma integrableOn_gevLogPoly (hξ : -1 / 2 < ξ) :
    IntegrableOn (fun t => exp (-t) *
      gevLogPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ d₀ e₀ f₀ d₁ e₁ f₁ g₀ h₀ k₀ t) (Ioi 0) :=
  IntegrableOn.congr_fun ((((integrableOn_gevPoly hξ).add
    (integrableOn_logRow (β := 0) (by norm_num) d₀ e₀ f₀)).add
    (integrableOn_logRow (β := ξ) (by linarith) d₁ e₁ f₁)).add (integrableOn_logSqRow g₀ h₀ k₀))
    (fun t _ => (exp_neg_mul_gevLogPoly t).symm) measurableSet_Ioi

/-- **Logarithmic Gamma moments**: the expectation of a `gevLogPoly` combination at a standard
exponential `T`, in terms of `Γ`, `Γ'(1 + ξ)`, Euler's constant `γ` and `π²/6`. -/
theorem integral_gevLogPoly (hξ : -1 / 2 < ξ) :
    ∫ t in Ioi 0, exp (-t) *
      gevLogPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ d₀ e₀ f₀ d₁ e₁ f₁ g₀ h₀ k₀ t =
      a₀ + b₀ + 2 * c₀ + Gamma (ξ + 1) * (a₁ + (ξ + 1) * b₁ + (ξ + 2) * (ξ + 1) * c₁) +
        Gamma (2 * ξ + 1) * (a₂ + (2 * ξ + 1) * b₂ + (2 * ξ + 2) * (2 * ξ + 1) * c₂) +
        ((e₀ + 3 * f₀) - eulerMascheroniConstant * (d₀ + e₀ + 2 * f₀)) +
        (Gamma (ξ + 1) * (e₁ + (2 * ξ + 3) * f₁) +
          deriv Gamma (ξ + 1) * (d₁ + (ξ + 1) * e₁ + (ξ + 2) * (ξ + 1) * f₁)) +
        (g₀ * (eulerMascheroniConstant ^ 2 + π ^ 2 / 6) +
          h₀ * (eulerMascheroniConstant ^ 2 + π ^ 2 / 6 - 2 * eulerMascheroniConstant) +
          k₀ * (2 * eulerMascheroniConstant ^ 2 + π ^ 2 / 3 - 6 * eulerMascheroniConstant + 2))
      := by
  have i0 := integrableOn_gevPoly (a₀ := a₀) (b₀ := b₀) (c₀ := c₀) (a₁ := a₁) (b₁ := b₁)
    (c₁ := c₁) (a₂ := a₂) (b₂ := b₂) (c₂ := c₂) hξ
  have i1 := integrableOn_logRow (β := 0) (by norm_num) d₀ e₀ f₀
  have i2 := integrableOn_logRow (β := ξ) (by linarith) d₁ e₁ f₁
  have i3 := integrableOn_logSqRow g₀ h₀ k₀
  have i01 : IntegrableOn (fun t => exp (-t) * gevPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t +
      exp (-t) * (t ^ (0 : ℝ) * log t * (d₀ + e₀ * t + f₀ * t ^ 2))) (Ioi 0) := i0.add i1
  have i012 : IntegrableOn (fun t => exp (-t) * gevPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ t +
      exp (-t) * (t ^ (0 : ℝ) * log t * (d₀ + e₀ * t + f₀ * t ^ 2)) +
      exp (-t) * (t ^ ξ * log t * (d₁ + e₁ * t + f₁ * t ^ 2))) (Ioi 0) := i01.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => exp_neg_mul_gevLogPoly t),
    integral_add i012 i3, integral_add i01 i2, integral_add i0 i1,
    integral_gevPoly _ _ _ _ _ _ _ _ _ hξ, integral_logRow (by norm_num),
    integral_logRow (by linarith), integral_logSqRow, zero_add, Gamma_one,
    (hasDerivAt_Gamma_one).deriv]
  ring

/-- The expectation against the GEV law of a function which, on the exponential scale, is a
`gevLogPoly` combination. -/
theorem integral_gevLocScaleCDF_of_logPoly (hξ : -1 / 2 < ξ) (hσ : 0 < σ) (hh : Measurable h)
    (heq : ∀ t, 0 < t → h (μ + σ * gevTransform ξ t) =
      gevLogPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ d₀ e₀ f₀ d₁ e₁ f₁ g₀ h₀ k₀ t) :
    ∫ x, h x ∂(gevLocScaleCDF ξ μ hσ).measure =
      a₀ + b₀ + 2 * c₀ + Gamma (ξ + 1) * (a₁ + (ξ + 1) * b₁ + (ξ + 2) * (ξ + 1) * c₁) +
        Gamma (2 * ξ + 1) * (a₂ + (2 * ξ + 1) * b₂ + (2 * ξ + 2) * (2 * ξ + 1) * c₂) +
        ((e₀ + 3 * f₀) - eulerMascheroniConstant * (d₀ + e₀ + 2 * f₀)) +
        (Gamma (ξ + 1) * (e₁ + (2 * ξ + 3) * f₁) +
          deriv Gamma (ξ + 1) * (d₁ + (ξ + 1) * e₁ + (ξ + 2) * (ξ + 1) * f₁)) +
        (g₀ * (eulerMascheroniConstant ^ 2 + π ^ 2 / 6) +
          h₀ * (eulerMascheroniConstant ^ 2 + π ^ 2 / 6 - 2 * eulerMascheroniConstant) +
          k₀ * (2 * eulerMascheroniConstant ^ 2 + π ^ 2 / 3 - 6 * eulerMascheroniConstant + 2))
      := by
  rw [integral_gevLocScaleCDF hσ hh, ← integral_gevLogPoly hξ]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => congrArg (exp (-t) * ·) (heq t ht)

theorem integrable_gevLocScaleCDF_of_logPoly (hξ : -1 / 2 < ξ) (hσ : 0 < σ) (hh : Measurable h)
    (heq : ∀ t, 0 < t → h (μ + σ * gevTransform ξ t) =
      gevLogPoly ξ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ d₀ e₀ f₀ d₁ e₁ f₁ g₀ h₀ k₀ t) :
    Integrable h (gevLocScaleCDF ξ μ hσ).measure := by
  rw [integrable_gevLocScaleCDF_iff hσ hh]
  exact (integrableOn_gevLogPoly hξ).congr_fun
    (fun t ht => congrArg (exp (-t) * ·) (heq t ht).symm) measurableSet_Ioi

end LogPoly

/-! ### The shape score -/

section ShapeScore

variable {ξ μ σ x : ℝ}

/-- The shape score `∂_ξ log(σ⁻¹ h_ξ((x - μ)/σ))`: with `z = (x - μ)/σ`, `u = 1 + ξ z`,
`log u/ξ² - (1/ξ + 1) z/u - u^{-1/ξ} (log u/ξ² - z/(ξ u))`. -/
noncomputable def gevScoreXi (ξ μ σ x : ℝ) : ℝ :=
  log (1 + ξ * ((x - μ) / σ)) / ξ ^ 2 -
    (1 / ξ + 1) * ((x - μ) / σ / (1 + ξ * ((x - μ) / σ))) -
    (1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ) *
      (log (1 + ξ * ((x - μ) / σ)) / ξ ^ 2 - (x - μ) / σ / (ξ * (1 + ξ * ((x - μ) / σ))))

lemma measurable_gevScoreXi (ξ μ σ : ℝ) : Measurable (gevScoreXi ξ μ σ) := by
  unfold gevScoreXi; fun_prop

/-- **The shape score is the derivative of the log-density in `ξ`.** -/
theorem hasDerivAt_log_gevLocScaleDensity_xi (hσ : 0 < σ) (hξ : ξ ≠ 0)
    (hu : 0 < 1 + ξ * ((x - μ) / σ)) :
    HasDerivAt (fun k => log (gevLocScaleDensity k μ σ x)) (gevScoreXi ξ μ σ x) ξ := by
  set z := (x - μ) / σ with hz
  have hU : HasDerivAt (fun k => 1 + k * z) z ξ := by
    simpa using ((hasDerivAt_id ξ).mul_const z).const_add 1
  have hcu : ContinuousAt (fun k => 1 + k * z) ξ := hU.continuousAt
  have hE : HasDerivAt (fun k => -1 / k) (1 / ξ ^ 2) ξ := by
    have := (hasDerivAt_inv hξ).neg
    convert this using 1
    · funext k; simp [div_eq_mul_inv]
    · field_simp
  have hI : HasDerivAt (fun k => 1 / k + 1) (-(1 / ξ ^ 2)) ξ := by
    have := (hasDerivAt_inv hξ).add_const 1
    simpa [one_div] using this
  have hu' : 0 < 1 + ξ * z := hu
  have heq : (fun k => -log σ - (1 / k + 1) * log (1 + k * z) - (1 + k * z) ^ (-1 / k)) =ᶠ[𝓝 ξ]
      fun k => log (gevLocScaleDensity k μ σ x) := by
    filter_upwards [hcu.eventually (lt_mem_nhds hu'), isOpen_ne.mem_nhds hξ] with k hk hk0
    rw [log_gevLocScaleDensity hσ hk0 hk]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq.symm
  have hd := ((hasDerivAt_const ξ (-log σ)).sub (hI.mul (hU.log hu'.ne'))).sub
    (hU.rpow hE hu')
  convert hd using 1
  rw [gevScoreXi, ← hz, rpow_sub_one hu'.ne']
  field_simp
  ring

/-- The shape score on the exponential scale: at `x = μ + σ (t^{-ξ} - 1)/ξ`,
`∂_ξ ℓ = (t - 1) log t/ξ + (t - 1 - ξ)(1 - t^ξ)/ξ²`. -/
lemma gevScoreXi_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) {t : ℝ} (ht : 0 < t) :
    gevScoreXi ξ μ σ (μ + σ * gevTransform ξ t) =
      (t - 1) * log t / ξ + (t - 1 - ξ) * (1 - t ^ ξ) / ξ ^ 2 := by
  have hz : (μ + σ * gevTransform ξ t - μ) / σ = gevTransform ξ t := by
    field_simp; ring
  have hw : 0 < t ^ ξ := rpow_pos_of_pos ht ξ
  rw [gevScoreXi, hz, one_add_mul_gevTransform hξ ht, rpow_neg_rpow_neg_one_div hξ ht,
    log_rpow ht]
  simp only [gevTransform, hξ, ↓reduceIte]
  rw [rpow_neg ht.le]
  field_simp
  ring

/-- A combination `a ∂_μ ℓ + b ∂_σ ℓ + c ∂_ξ ℓ` of the scores on the exponential scale:
`A₀ + B₀ t + t^ξ (A₁ + B₁ t) + (c/ξ)(t - 1) log t`. -/
lemma lin3_gevScore_transform (hσ : 0 < σ) (hξ : ξ ≠ 0) (a b c : ℝ) {t : ℝ} (ht : 0 < t) :
    a * gevScoreMu ξ μ σ (μ + σ * gevTransform ξ t) +
        b * gevScoreSigma ξ μ σ (μ + σ * gevTransform ξ t) +
        c * gevScoreXi ξ μ σ (μ + σ * gevTransform ξ t) =
      (b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2) + (-(b / (ξ * σ)) + c / ξ ^ 2) * t +
        t ^ ξ * ((a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2) +
          (b / (ξ * σ) - a / σ - c / ξ ^ 2) * t) + c / ξ * (t - 1) * log t := by
  rw [lin_gevScore_transform hσ hξ a b ht, gevScoreXi_transform hσ hξ ht]
  field_simp
  ring

end ShapeScore

/-! ### The Fisher information matrix -/

section Information

open Matrix

/-- The digamma function on the positive reals, `ψ(s) = Γ'(s)/Γ(s)`. -/
noncomputable def realDigamma (s : ℝ) : ℝ := deriv Gamma s / Gamma s

/-- `p = (1 + ξ)² Γ(1 + 2ξ)` (Prescott–Walden 1980). -/
noncomputable def gevInfoP (ξ : ℝ) : ℝ := (1 + ξ) ^ 2 * Gamma (1 + 2 * ξ)

/-- `q = Γ(2 + ξ) (ψ(1 + ξ) + (1 + ξ)/ξ)` (Prescott–Walden 1980). -/
noncomputable def gevInfoQ (ξ : ℝ) : ℝ := Gamma (2 + ξ) * (realDigamma (1 + ξ) + (1 + ξ) / ξ)

/-- **The Fisher information matrix of the GEV family** in the parametrization `(μ, σ, ξ)`
(Prescott–Walden 1980; Smith 1985), for `ξ ≠ 0`: with `p = (1 + ξ)² Γ(1 + 2ξ)`,
`q = Γ(2 + ξ)(ψ(1 + ξ) + (1 + ξ)/ξ)`, `γ` Euler's constant,

* `I_μμ = p/σ²`, `I_μσ = (Γ(2 + ξ) - p)/(ξ σ²)`, `I_σσ = (1 - 2Γ(2 + ξ) + p)/(ξ² σ²)`,
* `I_μξ = -(q - p/ξ)/(σ ξ)`, `I_σξ = -(1 - γ + (1 - Γ(2 + ξ))/ξ - q + p/ξ)/(σ ξ²)`,
* `I_ξξ = (π²/6 + (1 - γ + 1/ξ)² - 2q/ξ + p/ξ²)/ξ²`. -/
noncomputable def gevFisherInfo (ξ σ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![gevInfoP ξ / σ ^ 2, (Gamma (2 + ξ) - gevInfoP ξ) / (ξ * σ ^ 2),
      -(gevInfoQ ξ - gevInfoP ξ / ξ) / (σ * ξ);
    (Gamma (2 + ξ) - gevInfoP ξ) / (ξ * σ ^ 2),
      (1 - 2 * Gamma (2 + ξ) + gevInfoP ξ) / (ξ ^ 2 * σ ^ 2),
      -(1 - eulerMascheroniConstant + (1 - Gamma (2 + ξ)) / ξ - gevInfoQ ξ + gevInfoP ξ / ξ) /
        (σ * ξ ^ 2);
    -(gevInfoQ ξ - gevInfoP ξ / ξ) / (σ * ξ),
      -(1 - eulerMascheroniConstant + (1 - Gamma (2 + ξ)) / ξ - gevInfoQ ξ + gevInfoP ξ / ξ) /
        (σ * ξ ^ 2),
      (π ^ 2 / 6 + (1 - eulerMascheroniConstant + 1 / ξ) ^ 2 - 2 * gevInfoQ ξ / ξ +
        gevInfoP ξ / ξ ^ 2) / ξ ^ 2]

variable {ξ μ σ : ℝ}

lemma gevFisherInfo_isSymm : (gevFisherInfo ξ σ).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [gevFisherInfo]

/-- The location-scale block of the Fisher information is `gevFisherInfoMuSigma`. -/
theorem gevFisherInfo_submatrix_castLE :
    (gevFisherInfo ξ σ).submatrix (Fin.castLE (by norm_num)) (Fin.castLE (by norm_num)) =
      gevFisherInfoMuSigma ξ σ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gevFisherInfo, gevFisherInfoMuSigma, gevInfoP]

lemma dotProduct_gevFisherInfo_mulVec (v : Fin 3 → ℝ) :
    v ⬝ᵥ (gevFisherInfo ξ σ *ᵥ v) =
      v 0 ^ 2 * (gevInfoP ξ / σ ^ 2) + v 1 ^ 2 * ((1 - 2 * Gamma (2 + ξ) + gevInfoP ξ) /
        (ξ ^ 2 * σ ^ 2)) +
      v 2 ^ 2 * ((π ^ 2 / 6 + (1 - eulerMascheroniConstant + 1 / ξ) ^ 2 -
        2 * gevInfoQ ξ / ξ + gevInfoP ξ / ξ ^ 2) / ξ ^ 2) +
      2 * v 0 * v 1 * ((Gamma (2 + ξ) - gevInfoP ξ) / (ξ * σ ^ 2)) +
      2 * v 0 * v 2 * (-(gevInfoQ ξ - gevInfoP ξ / ξ) / (σ * ξ)) +
      2 * v 1 * v 2 * (-(1 - eulerMascheroniConstant + (1 - Gamma (2 + ξ)) / ξ - gevInfoQ ξ +
        gevInfoP ξ / ξ) / (σ * ξ ^ 2)) := by
  simp [gevFisherInfo, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

variable (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ)
include hσ hξ0 hξ

/-- **Every combination of the three scores has mean zero.** -/
theorem integral_lin3_gevScore (a b c : ℝ) :
    ∫ x, (a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x + c * gevScoreXi ξ μ σ x)
      ∂(gevLocScaleCDF ξ μ hσ).measure = 0 := by
  have hm : Measurable fun x =>
      a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x + c * gevScoreXi ξ μ σ x := by
    have := measurable_gevScoreMu ξ μ σ; have := measurable_gevScoreSigma ξ μ σ
    have := measurable_gevScoreXi ξ μ σ; fun_prop
  rw [integral_gevLocScaleCDF_of_logPoly hξ hσ hm
    (a₀ := b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2) (b₀ := -(b / (ξ * σ)) + c / ξ ^ 2) (c₀ := 0)
    (a₁ := a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2)
    (b₁ := b / (ξ * σ) - a / σ - c / ξ ^ 2) (c₁ := 0) (a₂ := 0) (b₂ := 0) (c₂ := 0)
    (d₀ := -(c / ξ)) (e₀ := c / ξ) (f₀ := 0) (d₁ := 0) (e₁ := 0) (f₁ := 0) (g₀ := 0) (h₀ := 0)
    (k₀ := 0) fun t ht => by
      rw [lin3_gevScore_transform hσ hξ0 a b c ht, gevLogPoly, gevPoly]; ring]
  field_simp
  ring

omit hξ in
/-- The quadratic form of the score covariance on the exponential scale. -/
private lemma sq_lin3_gevScore_transform (a b c : ℝ) {t : ℝ} (ht : 0 < t) :
    (a * gevScoreMu ξ μ σ (μ + σ * gevTransform ξ t) +
        b * gevScoreSigma ξ μ σ (μ + σ * gevTransform ξ t) +
        c * gevScoreXi ξ μ σ (μ + σ * gevTransform ξ t)) ^ 2 =
      gevLogPoly ξ ((b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2) ^ 2)
        (2 * (b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2) * (-(b / (ξ * σ)) + c / ξ ^ 2))
        ((-(b / (ξ * σ)) + c / ξ ^ 2) ^ 2)
        (2 * (b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2) *
          (a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2))
        (2 * ((b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2) * (b / (ξ * σ) - a / σ - c / ξ ^ 2) +
          (a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2) *
            (-(b / (ξ * σ)) + c / ξ ^ 2)))
        (2 * (-(b / (ξ * σ)) + c / ξ ^ 2) * (b / (ξ * σ) - a / σ - c / ξ ^ 2))
        ((a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2) ^ 2)
        (2 * (a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2) *
          (b / (ξ * σ) - a / σ - c / ξ ^ 2))
        ((b / (ξ * σ) - a / σ - c / ξ ^ 2) ^ 2)
        (-(2 * (c / ξ) * (b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2)))
        (2 * (c / ξ) * ((b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2) - (-(b / (ξ * σ)) + c / ξ ^ 2)))
        (2 * (c / ξ) * (-(b / (ξ * σ)) + c / ξ ^ 2))
        (-(2 * (c / ξ) * (a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2)))
        (2 * (c / ξ) * ((a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2) -
          (b / (ξ * σ) - a / σ - c / ξ ^ 2)))
        (2 * (c / ξ) * (b / (ξ * σ) - a / σ - c / ξ ^ 2))
        ((c / ξ) ^ 2) (-(2 * (c / ξ) ^ 2)) ((c / ξ) ^ 2) t := by
  rw [lin3_gevScore_transform hσ hξ0 a b c ht, gevLogPoly, gevPoly]
  ring

/-- **The quadratic form of the Fisher information**:
`E[(a ∂_μ ℓ + b ∂_σ ℓ + c ∂_ξ ℓ)²] = (a, b, c) I (a, b, c)ᵀ` for `ξ > -1/2`, `ξ ≠ 0`. -/
theorem integral_lin3_gevScore_sq (a b c : ℝ) :
    ∫ x, (a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x + c * gevScoreXi ξ μ σ x) ^ 2
      ∂(gevLocScaleCDF ξ μ hσ).measure = ![a, b, c] ⬝ᵥ (gevFisherInfo ξ σ *ᵥ ![a, b, c]) := by
  have hm : Measurable fun x =>
      (a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x + c * gevScoreXi ξ μ σ x) ^ 2 := by
    have := measurable_gevScoreMu ξ μ σ; have := measurable_gevScoreSigma ξ μ σ
    have := measurable_gevScoreXi ξ μ σ; fun_prop
  rw [integral_gevLocScaleCDF_of_logPoly hξ hσ hm
    (fun t ht => sq_lin3_gevScore_transform hσ hξ0 a b c ht),
    dotProduct_gevFisherInfo_mulVec]
  have h1ξ : 0 < 1 + ξ := by linarith
  have hG : Gamma (1 + ξ) ≠ 0 := (Gamma_pos_of_pos h1ξ).ne'
  have g2 : Gamma (2 + ξ) = (1 + ξ) * Gamma (1 + ξ) := by
    rw [show 2 + ξ = 1 + ξ + 1 by ring, Gamma_add_one h1ξ.ne']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [gevInfoQ, gevInfoP, realDigamma, g2, show ξ + 1 = 1 + ξ by ring,
    show 2 * ξ + 1 = 1 + 2 * ξ by ring]
  field_simp
  ring

/-- The combinations of the three scores are square integrable. -/
lemma memLp_lin3_gevScore (a b c : ℝ) :
    MemLp (fun x => a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x +
      c * gevScoreXi ξ μ σ x) 2 (gevLocScaleCDF ξ μ hσ).measure := by
  have hm : Measurable fun x =>
      a * gevScoreMu ξ μ σ x + b * gevScoreSigma ξ μ σ x + c * gevScoreXi ξ μ σ x := by
    have := measurable_gevScoreMu ξ μ σ; have := measurable_gevScoreSigma ξ μ σ
    have := measurable_gevScoreXi ξ μ σ; fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact integrable_gevLocScaleCDF_of_logPoly hξ hσ (hm.pow_const 2)
    (fun t ht => sq_lin3_gevScore_transform hσ hξ0 a b c ht)

end Information

/-! ### The score vector and its covariance -/

section Covariance

open Matrix

variable {ξ μ σ : ℝ}

/-- The score `(∂_μ ℓ, ∂_σ ℓ, ∂_ξ ℓ)` of one observation, as a function `Fin 3 → ℝ`. -/
noncomputable def gevScore (ξ μ σ x : ℝ) : Fin 3 → ℝ :=
  ![gevScoreMu ξ μ σ x, gevScoreSigma ξ μ σ x, gevScoreXi ξ μ σ x]

lemma dotProduct_gevScore (u : Fin 3 → ℝ) (x : ℝ) :
    u ⬝ᵥ gevScore ξ μ σ x =
      u 0 * gevScoreMu ξ μ σ x + u 1 * gevScoreSigma ξ μ σ x + u 2 * gevScoreXi ξ μ σ x := by
  simp [gevScore, dotProduct, Fin.sum_univ_three]

lemma measurable_dotProduct_gevScore (u : Fin 3 → ℝ) :
    Measurable fun x => u ⬝ᵥ gevScore ξ μ σ x := by
  simp_rw [dotProduct_gevScore]
  have := measurable_gevScoreMu ξ μ σ; have := measurable_gevScoreSigma ξ μ σ
  have := measurable_gevScoreXi ξ μ σ; fun_prop

lemma eq_vec_three (u : Fin 3 → ℝ) : u = ![u 0, u 1, u 2] := by
  ext i; fin_cases i <;> rfl

variable (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ)
include hσ hξ0 hξ

lemma memLp_dotProduct_gevScore (u : Fin 3 → ℝ) :
    MemLp (fun x => u ⬝ᵥ gevScore ξ μ σ x) 2 (gevLocScaleCDF ξ μ hσ).measure := by
  simp_rw [dotProduct_gevScore]
  exact memLp_lin3_gevScore hσ hξ0 hξ _ _ _

theorem integral_dotProduct_gevScore (u : Fin 3 → ℝ) :
    ∫ x, u ⬝ᵥ gevScore ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure = 0 := by
  simp_rw [dotProduct_gevScore]
  exact integral_lin3_gevScore hσ hξ0 hξ _ _ _

theorem integral_dotProduct_gevScore_sq (u : Fin 3 → ℝ) :
    ∫ x, (u ⬝ᵥ gevScore ξ μ σ x) ^ 2 ∂(gevLocScaleCDF ξ μ hσ).measure =
      u ⬝ᵥ (gevFisherInfo ξ σ *ᵥ u) := by
  simp_rw [dotProduct_gevScore]
  rw [integral_lin3_gevScore_sq hσ hξ0 hξ, ← eq_vec_three]

/-- **The covariance of the score is the Fisher information**:
`E[(u · ∇ℓ)(w · ∇ℓ)] = uᵀ I w`. -/
theorem integral_dotProduct_gevScore_mul (u w : Fin 3 → ℝ) :
    ∫ x, (u ⬝ᵥ gevScore ξ μ σ x) * (w ⬝ᵥ gevScore ξ μ σ x) ∂(gevLocScaleCDF ξ μ hσ).measure =
      u ⬝ᵥ (gevFisherInfo ξ σ *ᵥ w) := by
  have iuw := (memLp_dotProduct_gevScore (μ := μ) hσ hξ0 hξ (u + w)).integrable_sq
  have iu := (memLp_dotProduct_gevScore (μ := μ) hσ hξ0 hξ u).integrable_sq
  have iw := (memLp_dotProduct_gevScore (μ := μ) hσ hξ0 hξ w).integrable_sq
  have e : (fun x => (u ⬝ᵥ gevScore ξ μ σ x) * (w ⬝ᵥ gevScore ξ μ σ x)) = fun x =>
      (((u + w) ⬝ᵥ gevScore ξ μ σ x) ^ 2 - (u ⬝ᵥ gevScore ξ μ σ x) ^ 2 -
        (w ⬝ᵥ gevScore ξ μ σ x) ^ 2) / 2 := by
    funext x; rw [add_dotProduct]; ring
  have i2 : Integrable (fun x => ((u + w) ⬝ᵥ gevScore ξ μ σ x) ^ 2 -
      (u ⬝ᵥ gevScore ξ μ σ x) ^ 2) (gevLocScaleCDF ξ μ hσ).measure := iuw.sub iu
  rw [e, integral_div, integral_sub i2 iw, integral_sub iuw iu,
    integral_dotProduct_gevScore_sq hσ hξ0 hξ, integral_dotProduct_gevScore_sq hσ hξ0 hξ,
    integral_dotProduct_gevScore_sq hσ hξ0 hξ]
  have hsym : w ⬝ᵥ (gevFisherInfo ξ σ *ᵥ u) = u ⬝ᵥ (gevFisherInfo ξ σ *ᵥ w) := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, gevFisherInfo_isSymm.eq]
  simp only [mulVec_add, dotProduct_add, add_dotProduct]
  rw [hsym]
  ring

/-- **The Fisher information entries**: `E[∂_i ℓ ∂_j ℓ] = I_{ij}`. -/
theorem integral_gevScore_mul_gevScore (i j : Fin 3) :
    ∫ x, gevScore ξ μ σ x i * gevScore ξ μ σ x j ∂(gevLocScaleCDF ξ μ hσ).measure =
      gevFisherInfo ξ σ i j := by
  have := integral_dotProduct_gevScore_mul (μ := μ) hσ hξ0 hξ (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single] using this

/-- **Each score has mean zero.** -/
theorem integral_gevScore (i : Fin 3) :
    ∫ x, gevScore ξ μ σ x i ∂(gevLocScaleCDF ξ μ hσ).measure = 0 := by
  have := integral_dotProduct_gevScore (μ := μ) hσ hξ0 hξ (Pi.single i 1)
  simpa [single_dotProduct] using this

/-- **The shape score has mean zero.** -/
theorem integral_gevScoreXi : ∫ x, gevScoreXi ξ μ σ x ∂(gevLocScaleCDF ξ μ hσ).measure = 0 := by
  simpa [gevScore] using integral_gevScore (μ := μ) hσ hξ0 hξ 2

end Covariance

/-! ### Positive definiteness -/

section PosDef

open Matrix

/-- `(t - 1) log t` is not in the span of `1, t, t^ξ, t^{ξ + 1}` on `(0, ∞)` (`ξ ≠ 0`,
`ξ > -1`): compare growth at `0⁺` (for `ξ > 0`) or at `∞` (for `ξ < 0`). -/
theorem exists_logComb_ne_zero {ξ A₀ B₀ A₁ B₁ C : ℝ} (hξ0 : ξ ≠ 0) (hξ : -1 < ξ) (hC : C ≠ 0) :
    ∃ t, 0 < t ∧ A₀ + B₀ * t + t ^ ξ * (A₁ + B₁ * t) + C * (t - 1) * log t ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hC
  rcases lt_or_gt_of_ne hξ0 with hneg | hpos
  · -- `ξ < 0`: divide by `t log t` and let `t → ∞`.
    have hL : Tendsto (fun t : ℝ => C * (1 - t⁻¹)) atTop (𝓝 C) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_inv_atTop_zero).const_mul C
    have hp : Tendsto (fun t : ℝ => t ^ ξ) atTop (𝓝 0) := by
      simpa using tendsto_rpow_neg_atTop (y := -ξ) (by linarith)
    have hR : Tendsto (fun t : ℝ => -((log t)⁻¹ *
        (A₀ * t⁻¹ + B₀ + A₁ * (t ^ ξ * t⁻¹) + B₁ * t ^ ξ))) atTop (𝓝 0) := by
      have := (tendsto_log_atTop.inv_tendsto_atTop).mul
        ((((tendsto_inv_atTop_zero.const_mul A₀).add (tendsto_const_nhds (x := B₀))).add
          ((hp.mul tendsto_inv_atTop_zero).const_mul A₁)).add (hp.const_mul B₁))
      simpa using this.neg
    refine tendsto_nhds_unique hL (hR.congr' ?_)
    filter_upwards [eventually_gt_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    have hl : 0 < log t := log_pos ht
    have h := hcon t ht0
    field_simp
    linear_combination -h
  · -- `ξ > 0`: divide by `log t` and let `t → 0⁺`.
    have hL : Tendsto (fun t : ℝ => C * (t - 1)) (𝓝[>] 0) (𝓝 (C * (0 - 1))) :=
      ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have hp : Tendsto (fun t : ℝ => A₀ + B₀ * t + t ^ ξ * (A₁ + B₁ * t)) (𝓝[>] 0)
        (𝓝 (A₀ + B₀ * 0 + (0 : ℝ) ^ ξ * (A₁ + B₁ * 0))) := by
      refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
      exact (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).add
        ((Real.continuousAt_rpow_const _ _ (Or.inr hpos.le)).mul
          (continuousAt_const.add (continuousAt_const.mul continuousAt_id)))
    have hR : Tendsto (fun t : ℝ => -((log t)⁻¹ * (A₀ + B₀ * t + t ^ ξ * (A₁ + B₁ * t))))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_log_nhdsGT_zero.inv_tendsto_atBot.mul hp).neg
    have := tendsto_nhds_unique hL (hR.congr' ?_)
    · linarith
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hl : log t ≠ 0 := (log_neg ht.1 ht.2).ne
    have h := hcon t ht.1
    field_simp
    linear_combination -h

/-- A weighted integral of a square which is continuous and not identically zero on `(0, ∞)`
is positive. -/
lemma setIntegral_exp_neg_mul_sq_pos {F : ℝ → ℝ} (hF : ContinuousOn F (Ioi 0))
    (hint : IntegrableOn (fun t => exp (-t) * F t ^ 2) (Ioi 0)) (hne : ∃ t, 0 < t ∧ F t ≠ 0) :
    0 < ∫ t in Ioi 0, exp (-t) * F t ^ 2 := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun t => by simp only [Pi.zero_apply]; positivity) hint]
  have hU : IsOpen (Ioi (0 : ℝ) ∩ F ⁻¹' {0}ᶜ) :=
    hF.isOpen_inter_preimage isOpen_Ioi isOpen_compl_singleton
  obtain ⟨t, ht, hFt⟩ := hne
  have hpos := hU.measure_pos volume ⟨t, ht, hFt⟩
  refine hpos.trans_le (measure_mono fun s hs => ⟨?_, hs.1⟩)
  simp only [Function.mem_support]
  exact mul_ne_zero (exp_pos _).ne' (pow_ne_zero 2 hs.2)

variable {ξ μ σ : ℝ}

/-- **The Fisher information of the GEV family is positive definite** for `ξ > -1/2`,
`ξ ≠ 0`. -/
theorem posDef_gevFisherInfo (hσ : 0 < σ) (hξ0 : ξ ≠ 0) (hξ : -1 / 2 < ξ) :
    (gevFisherInfo ξ σ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun v hv => ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [gevFisherInfo]
  rw [star_trivial, eq_vec_three v, ← integral_lin3_gevScore_sq hσ hξ0 hξ (μ := 0)]
  rcases eq_or_ne (v 2) 0 with hc | hc
  · -- no shape component: the location-scale block
    have hw : ![v 0, v 1] ≠ 0 := by
      intro h
      apply hv
      have h0 : v 0 = 0 := by simpa using congrFun h 0
      have h1 : v 1 = 0 := by simpa using congrFun h 1
      ext i; fin_cases i <;> simp [h0, h1, hc]
    have := (Matrix.posDef_iff_dotProduct_mulVec.1
      (posDef_gevFisherInfoMuSigma hσ hξ0 hξ)).2 hw
    rw [star_trivial, dotProduct_gevFisherInfoMuSigma_mulVec,
      ← integral_lin_gevScore_sq hσ hξ0 hξ (μ := 0)] at this
    simpa [hc] using this
  · have hm : Measurable fun x => (v 0 * gevScoreMu ξ 0 σ x + v 1 * gevScoreSigma ξ 0 σ x +
        v 2 * gevScoreXi ξ 0 σ x) ^ 2 := by
      have := measurable_gevScoreMu ξ 0 σ; have := measurable_gevScoreSigma ξ 0 σ
      have := measurable_gevScoreXi ξ 0 σ; fun_prop
    have hint := (integrable_gevLocScaleCDF_iff hσ hm).1
      (integrable_gevLocScaleCDF_of_logPoly hξ hσ hm
        (fun t ht => sq_lin3_gevScore_transform hσ hξ0 _ _ _ ht))
    rw [integral_gevLocScaleCDF hσ hm]
    set a := v 0
    set b := v 1
    set c := v 2
    set F : ℝ → ℝ := fun t => (b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2) +
      (-(b / (ξ * σ)) + c / ξ ^ 2) * t +
      t ^ ξ * ((a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2) +
        (b / (ξ * σ) - a / σ - c / ξ ^ 2) * t) + c / ξ * (t - 1) * log t with hF
    have heq : ∀ t ∈ Ioi (0 : ℝ), exp (-t) * (a * gevScoreMu ξ 0 σ (0 + σ * gevTransform ξ t) +
        b * gevScoreSigma ξ 0 σ (0 + σ * gevTransform ξ t) +
        c * gevScoreXi ξ 0 σ (0 + σ * gevTransform ξ t)) ^ 2 = exp (-t) * F t ^ 2 :=
      fun t ht => by rw [lin3_gevScore_transform hσ hξ0 a b c ht]
    rw [setIntegral_congr_fun measurableSet_Ioi heq]
    refine setIntegral_exp_neg_mul_sq_pos ?_ (hint.congr_fun heq measurableSet_Ioi) ?_
    · intro t ht
      have ht0 : t ≠ 0 := (show (0 : ℝ) < t from ht).ne'
      refine ContinuousAt.continuousWithinAt ?_
      simp only [hF]
      fun_prop (disch := first | exact ht0 | exact Or.inl ht0)
    · obtain ⟨t, ht, hne⟩ := exists_logComb_ne_zero (A₀ := b / (ξ * σ) - c * (1 + ξ) / ξ ^ 2)
        (B₀ := -(b / (ξ * σ)) + c / ξ ^ 2)
        (A₁ := a * (1 + ξ) / σ - b * (1 + ξ) / (ξ * σ) + c * (1 + ξ) / ξ ^ 2)
        (B₁ := b / (ξ * σ) - a / σ - c / ξ ^ 2) hξ0 (by linarith) (div_ne_zero hc hξ0)
      exact ⟨t, ht, hne⟩

end PosDef

/-! ### The trivariate score CLT -/

section ScoreCLT

open RealInnerProductSpace Matrix

variable {ξ μ σ : ℝ}

/-- **The score vector** `(∂_μ ℓ, ∂_σ ℓ, ∂_ξ ℓ) ∈ ℝ³` of one observation. -/
noncomputable def gevScoreVec3 (ξ μ σ x : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (gevScore ξ μ σ x)

lemma measurable_gevScoreVec3 (ξ μ σ : ℝ) : Measurable (gevScoreVec3 ξ μ σ) := by
  unfold gevScoreVec3
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  · simpa [gevScore] using measurable_gevScoreMu ξ μ σ
  · simpa [gevScore] using measurable_gevScoreSigma ξ μ σ
  · simpa [gevScore] using measurable_gevScoreXi ξ μ σ

lemma inner_gevScoreVec3 (x : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    ⟪gevScoreVec3 ξ μ σ x, v⟫ = (fun i => v i) ⬝ᵥ gevScore ξ μ σ x := by
  simp [gevScoreVec3, PiLp.inner_apply, dotProduct, Fin.sum_univ_three, mul_comm]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ}

/-- **The trivariate central limit theorem for the GEV score.** Let `X₀, X₁, …` be iid with the
location-scale GEV law of parameters `(ξ, μ, σ)`, `-1/2 < ξ`, `ξ ≠ 0`. Then
`n^{-1/2} ∑_{i<n} (∂_μ ℓ, ∂_σ ℓ, ∂_ξ ℓ)(Xᵢ)` converges in distribution in `ℝ³` to the centered
Gaussian law whose covariance is the Fisher information `gevFisherInfo ξ σ`. -/
theorem tendstoInDistribution_gevScoreVec3 (hξ : -1 / 2 < ξ) (hξ0 : ξ ≠ 0) (hσ : 0 < σ)
    (hX : ∀ i, HasLaw (X i) (gevLocScaleCDF ξ μ hσ).measure P) (hind : iIndepFun X P)
    {Z : Ω' → EuclideanSpace ℝ (Fin 3)}
    (hZ : HasLaw Z (multivariateGaussian 0 (gevFisherInfo ξ σ)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, gevScoreVec3 ξ μ σ (X i ω))
      atTop Z (fun _ => P) P' := by
  refine TendstoInDistribution.of_inner hZ.aemeasurable (fun n => ?_) fun v => ?_
  · have := measurable_gevScoreVec3 ξ μ σ
    have := fun i => (hX i).aemeasurable
    fun_prop
  set u : Fin 3 → ℝ := fun i => v i
  set f : ℝ → ℝ := fun x => u ⬝ᵥ gevScore ξ μ σ x
  have hf : Measurable f := measurable_dotProduct_gevScore u
  set Y : ℕ → Ω → ℝ := fun i => f ∘ X i
  have hind' : iIndepFun Y P := hind.comp (fun _ => f) (fun _ => hf)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable,
      by rw [(hX i).map_eq, (hX 0).map_eq]⟩ hf
  have hmemLp : MemLp (Y 0) 2 P := by
    rw [← memLp_map_measure_iff hf.aestronglyMeasurable (hX 0).aemeasurable, (hX 0).map_eq]
    exact memLp_dotProduct_gevScore hσ hξ0 hξ u
  have hint : ∀ g : ℝ → ℝ, Measurable g →
      P[g ∘ X 0] = ∫ x, g x ∂(gevLocScaleCDF ξ μ hσ).measure :=
    fun g hg => (hX 0).integral_comp hg.aestronglyMeasurable
  have hmean : P[Y 0] = 0 := by
    rw [hint f hf]
    exact integral_dotProduct_gevScore hσ hξ0 hξ u
  have hvar : Var[Y 0; P] = v ⬝ᵥ gevFisherInfo ξ σ *ᵥ v := by
    rw [variance_of_integral_eq_zero (hf.comp_aemeasurable (hX 0).aemeasurable) hmean]
    have := hint (fun x => f x ^ 2) (hf.pow_const 2)
    simp only [Function.comp_def] at this
    simp only [Function.comp_def]
    rw [this, integral_dotProduct_gevScore_sq hσ hξ0 hξ]
  have hZt : HasLaw (fun ω => ⟪Z ω, v⟫) (gaussianReal 0 Var[Y 0; P].toNNReal) P' := by
    rw [hvar]
    exact hasLaw_inner_multivariateGaussian (posDef_gevFisherInfo hσ hξ0 hξ).posSemidef hZ v
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hZt hmemLp hind' hident
  rw [hmean] at hclt
  convert hclt using 3 with n ω
  rw [inner_smul_left, sum_inner]
  simp [Y, f, u, inner_gevScoreVec3]

end ScoreCLT

end ExtremeValueTheory
