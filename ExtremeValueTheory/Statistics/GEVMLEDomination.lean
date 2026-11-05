/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLECoordinates

/-!
# Domination of the second derivative of the GEV log-density near a moving endpoint

We work in the coordinates `η = (ξ, κ₀, κ₁)` of `ExtremeValueTheory.Statistics.GEVMLECoordinates`,
in the box `gevEtaBox ξ₀` around the truth `η₀ = (ξ₀, 0, 1)`, `u = κ₀ + κ₁ v`. Since the support
moves with the parameter, there is no integrable two-sided bound which holds for every observation
in the support: `u` can be arbitrarily small at a fixed `v`. There are two substitutes.

* **A one-sided bound for every observation in the support** (`exists_gevEtaM_self_le`):
  `M(η, v)[d, d] ≤ K |d|² E(v)`, with `E(v) = v^{-a} + v^b` integrable under the true law. For `u`
  small the blow-up has the good sign: `M(η, v)[d, d] ≤ d₁²/ξ²`
  (`gevEtaM_self_le_of_log_le`). This holds for both signs of the shape; it is a statement about a
  quadratic form in `(d₁, Dy)` (`quad_nonpos_of_discriminant`), with `y = -log u/ξ`, `Dy` its
  derivative in the direction `d`, whose discriminant has the right sign when `u` is small
  (`exists_log_threshold`).
* **A two-sided bound for good observations** (`exists_abs_gevEtaM_le_of_comparable`): if
  `v/2 ≤ u ≤ 2v` then `|M(η, v)[d, e]| ≤ K |d| |e| E(v)`.

The exponents are `a = a_w + 2 + 2ε`, `b = b_w + 2ε`, with `a_w = max(0, 2/ξ₀)`,
`b_w = max(0, -2/ξ₀)`, the exponents of `w = u^{-1/ξ}` in the box. The condition for `E` to be
integrable under the true law, `-1 < a ξ₀` and `b ξ₀ < 1`, can be met for `ξ₀ > -1/2`
(`exists_gevEnvM_integrable`): for `-1/2 < ξ₀ < 0` it reads `(2 + 2ε) |ξ₀| < 1`.

On the compact sets `{c ≤ v ≤ 1/c}` the second derivative is uniformly continuous
(`exists_delta_abs_gevEtaM_sub_le`). Together, for parameters near the truth
(`exists_gevEtaM_dev_le`), the second derivative is close to its value at the truth, up to the
error `gevEtaTail K c v`, which vanishes on `{c ≤ v ≤ 1/c}` and whose expectation tends to `0` as
`c → 0` (`ExtremeValueTheory.tendsto_integral_gevEtaTail`).

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

/-! ### The box -/

section Box

variable {ξ₀ : ℝ}

/-- The box `|ξ - ξ₀| ≤ |ξ₀|/2`, `|κ₀| ≤ 1/4`, `|κ₁ - 1| ≤ 1/4` around the truth `(ξ₀, 0, 1)`. -/
def gevEtaBox (ξ₀ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc (ξ₀ - |ξ₀| / 2) (ξ₀ + |ξ₀| / 2) ×ˢ Icc (-(1 / 4)) (1 / 4) ×ˢ Icc (3 / 4) (5 / 4)

lemma convex_gevEtaBox : Convex ℝ (gevEtaBox ξ₀) :=
  (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))

lemma isCompact_gevEtaBox : IsCompact (gevEtaBox ξ₀) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

lemma mem_gevEtaBox_self : (ξ₀, (0 : ℝ), (1 : ℝ)) ∈ gevEtaBox ξ₀ := by
  have := abs_nonneg ξ₀
  refine ⟨⟨by simp only; linarith, by simp only; linarith⟩, ⟨by norm_num, by norm_num⟩, ?_, ?_⟩ <;>
    norm_num

lemma gevEtaBox_mem_nhds (hξ₀ : ξ₀ ≠ 0) : gevEtaBox ξ₀ ∈ 𝓝 (ξ₀, (0 : ℝ), (1 : ℝ)) := by
  have h : 0 < |ξ₀| := abs_pos.2 hξ₀
  refine prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
    (prod_mem_nhds (Icc_mem_nhds (by norm_num) (by norm_num))
      (Icc_mem_nhds (by norm_num) (by norm_num)))

/-- The facts about a point of the box which we use. -/
lemma bounds_of_mem_gevEtaBox (hξ₀ : ξ₀ ≠ 0) {η : ℝ × ℝ × ℝ} (hη : η ∈ gevEtaBox ξ₀) :
    |η.1 - ξ₀| ≤ |ξ₀| / 2 ∧ |ξ₀| / 2 ≤ |η.1| ∧ |η.1| ≤ 3 * |ξ₀| / 2 ∧ η.1 ≠ 0 ∧ 0 < η.1 / ξ₀ ∧
      |η.2.1| ≤ 1 / 4 ∧ 3 / 4 ≤ η.2.2 ∧ η.2.2 ≤ 5 / 4 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := hη
  have ha : 0 < |ξ₀| := abs_pos.2 hξ₀
  have hd : |η.1 - ξ₀| ≤ |ξ₀| / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hlo : |ξ₀| / 2 ≤ |η.1| := by
    have := abs_sub_abs_le_abs_sub ξ₀ η.1
    rw [abs_sub_comm] at this
    linarith
  have hne : η.1 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hlo
    linarith
  refine ⟨hd, hlo, ?_, hne, ?_, abs_le.2 ⟨h3, h4⟩, h5, h6⟩
  · have := abs_sub_abs_le_abs_sub η.1 ξ₀
    linarith
  · rcases lt_or_gt_of_ne hξ₀ with h | h
    · rw [abs_of_neg h] at h2
      exact div_pos_of_neg_of_neg (by linarith) h
    · rw [abs_of_pos h] at h1
      exact div_pos (by linarith) h

/-- `u = κ₀ + κ₁ v` is at most `1/4 + 5 v/4` in the box, for `v ≥ 0`. -/
lemma gevEtaU_le (hξ₀ : ξ₀ ≠ 0) {η : ℝ × ℝ × ℝ} (hη : η ∈ gevEtaBox ξ₀) {v : ℝ} (hv : 0 ≤ v) :
    gevEtaU η v ≤ 1 / 4 + 5 / 4 * v := by
  obtain ⟨-, -, -, -, -, h6, -, h8⟩ := bounds_of_mem_gevEtaBox hξ₀ hη
  have := (abs_le.1 h6).2
  unfold gevEtaU
  nlinarith

end Box

/-! ### The exponents of `w = u^{-1/ξ}` -/

section Exponents

variable {ξ₀ ξ : ℝ}

/-- The exponent `a_w = max(0, 2/ξ₀)`. -/
noncomputable def gevAw (ξ₀ : ℝ) : ℝ := max 0 (2 / ξ₀)

/-- The exponent `b_w = max(0, -2/ξ₀)`. -/
noncomputable def gevBw (ξ₀ : ℝ) : ℝ := max 0 (-2 / ξ₀)

lemma gevAw_nonneg : 0 ≤ gevAw ξ₀ := le_max_left _ _

lemma gevBw_nonneg : 0 ≤ gevBw ξ₀ := le_max_left _ _

/-- For `|ξ - ξ₀| ≤ |ξ₀|/2`, the exponent `-1/ξ` lies in `[-a_w, b_w]`. -/
lemma neg_one_div_mem (hξ₀ : ξ₀ ≠ 0) (hξ : |ξ - ξ₀| ≤ |ξ₀| / 2) :
    -gevAw ξ₀ ≤ -1 / ξ ∧ -1 / ξ ≤ gevBw ξ₀ := by
  rw [abs_le] at hξ
  rcases lt_or_gt_of_ne hξ₀ with h | h
  · rw [abs_of_neg h] at hξ
    have hξn : 0 < -ξ := by linarith
    have hA : gevAw ξ₀ = 0 := max_eq_left (div_nonpos_of_nonneg_of_nonpos (by norm_num) h.le)
    have e1 : -1 / ξ = 1 / -ξ := by rw [div_neg, neg_div]
    constructor
    · rw [hA, e1]
      have : 0 < 1 / -ξ := by positivity
      linarith
    · refine le_trans ?_ (le_max_right _ _)
      have e2 : -2 / ξ₀ = 2 / -ξ₀ := by rw [div_neg, neg_div]
      rw [e1, e2, div_le_div_iff₀ hξn (by linarith)]
      linarith
  · rw [abs_of_pos h] at hξ
    have hξp : 0 < ξ := by linarith
    have hA : gevAw ξ₀ = 2 / ξ₀ := max_eq_right (by positivity)
    constructor
    · rw [hA, neg_div, neg_le_neg_iff, div_le_div_iff₀ hξp h]
      linarith
    · refine le_trans ?_ (le_max_left _ _)
      have : 0 < 1 / ξ := by positivity
      rw [neg_div]
      linarith

/-- The envelope `v^{-(a_w + 2 + 2ε)} + v^{b_w + 2ε}` which dominates the second derivative. -/
noncomputable def gevEnvM (ξ₀ ε v : ℝ) : ℝ := gevEnv (gevAw ξ₀ + 2 + 2 * ε) (gevBw ξ₀ + 2 * ε) v

lemma one_le_gevEnvM {ε v : ℝ} (hε : 0 < ε) (hv : 0 < v) : 1 ≤ gevEnvM ξ₀ ε v :=
  one_le_gevEnv hv (by have := gevAw_nonneg (ξ₀ := ξ₀); linarith)
    (by have := gevBw_nonneg (ξ₀ := ξ₀); linarith)

/-- **Where `ξ₀ > -1/2` enters**: `ε` can be chosen so that the envelope `gevEnvM` is integrable
under the true law, that is `-1 < a ξ₀` and `b ξ₀ < 1`. -/
lemma exists_gevEnvM_integrable (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ -1 < (gevAw ξ₀ + 2 + 2 * ε) * ξ₀ ∧ (gevBw ξ₀ + 2 * ε) * ξ₀ < 1 := by
  rcases lt_or_gt_of_ne hξ₀0 with h | h
  · have hA : gevAw ξ₀ = 0 := max_eq_left (div_nonpos_of_nonneg_of_nonpos (by norm_num) h.le)
    have h1 : 0 < -ξ₀ := by linarith
    refine ⟨(1 / -ξ₀ - 2) / 4, ?_, ?_, ?_⟩
    · have : 2 < 1 / -ξ₀ := by rw [lt_div_iff₀ h1]; linarith
      linarith
    · rw [hA]
      have e : (0 + 2 + 2 * ((1 / -ξ₀ - 2) / 4)) * ξ₀ = ξ₀ - 1 / 2 := by
        have := h.ne
        field_simp
        ring
      rw [e]
      linarith
    · have hb : 0 ≤ gevBw ξ₀ + 2 * ((1 / -ξ₀ - 2) / 4) := by
        have := gevBw_nonneg (ξ₀ := ξ₀)
        have : 2 < 1 / -ξ₀ := by rw [lt_div_iff₀ h1]; linarith
        linarith
      nlinarith
  · have hB : gevBw ξ₀ = 0 :=
      max_eq_left (div_nonpos_of_nonpos_of_nonneg (by norm_num) h.le)
    refine ⟨1 / (4 * ξ₀), by positivity, ?_, ?_⟩
    · have : 0 ≤ (gevAw ξ₀ + 2 + 2 * (1 / (4 * ξ₀))) * ξ₀ := by
        have := gevAw_nonneg (ξ₀ := ξ₀)
        positivity
      linarith
    · rw [hB]
      have e : (0 + 2 * (1 / (4 * ξ₀))) * ξ₀ = 1 / 2 := by
        field_simp
        norm_num
      rw [e]
      norm_num

/-- The envelope `gevEnvM` is integrable under the true law, for the `ε` of
`exists_gevEnvM_integrable`. -/
lemma integrable_gevEnvM {μ₀ σ₀ ε : ℝ} (hξ₀0 : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀)
    (ha : -1 < (gevAw ξ₀ + 2 + 2 * ε) * ξ₀) (hb : (gevBw ξ₀ + 2 * ε) * ξ₀ < 1) :
    Integrable (fun x => gevEnvM ξ₀ ε (gevU ξ₀ μ₀ σ₀ x)) (gevLocScaleCDF ξ₀ μ₀ hσ₀).measure :=
  integrable_gevEnv hξ₀0 hσ₀ ha hb

end Exponents

/-! ### The bound by weights -/

section Weights

private lemma abs_mul_le_mul' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) ((abs_nonneg a).trans ha)

/-- A bound for the expression of the second derivative, given bounds for its ingredients. -/
private lemma abs_M_le {K P N N' τ τ' c c' Y Y' w y ξ q κi : ℝ} (hK : 1 ≤ K) (hP : 1 ≤ P)
    (hN : 0 ≤ N) (hN' : 0 ≤ N') (hw : 0 ≤ w) (hτ : |τ| ≤ N) (hτ' : |τ'| ≤ N') (hc : |c| ≤ N)
    (hc' : |c'| ≤ N') (hY : |Y| ≤ K * N * P) (hY' : |Y'| ≤ K * N' * P) (hy : |y| ≤ K * P)
    (hξ : |ξ| ≤ K) (hq : |q| ≤ K) (hκ : |κi| ≤ K) :
    |-(c * c') * κi + τ * τ' * q ^ 2 + τ * Y' + τ' * Y - w * Y * Y' +
      (1 + ξ - w) * (ξ * Y * Y' + (τ * Y' + τ' * Y) * (y - q) + q * τ * τ' * y ^ 2)| ≤
      17 * K ^ 4 * N * N' * ((1 + w) * P ^ 2) := by
  have hK0 : 0 ≤ K := by linarith
  have hP0 : 0 ≤ P := by linarith
  set B := N * N' with hB
  have hB0 : 0 ≤ B := by positivity
  set Q := (1 + w) * P ^ 2 with hQ
  have hP2 : 1 ≤ P ^ 2 := one_le_pow₀ hP
  have hPP : P ≤ P ^ 2 := le_self_pow₀ hP two_ne_zero
  have hQ1 : P ^ 2 ≤ Q :=
    le_mul_of_one_le_left (sq_nonneg P) (by linarith)
  have hwQ : w * P ^ 2 ≤ Q :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg P)
  set X := B * Q with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ Q := by linarith
    positivity
  have hBP2 : B * P ^ 2 ≤ X := mul_le_mul_of_nonneg_left hQ1 hB0
  have hBP : B * P ≤ X := (mul_le_mul_of_nonneg_left hPP hB0).trans hBP2
  have hB1 : B ≤ X := by
    have : B * 1 ≤ B * P := mul_le_mul_of_nonneg_left hP hB0
    linarith
  have hwBP2 : w * (B * P ^ 2) ≤ X := by
    have := mul_le_mul_of_nonneg_left hwQ hB0
    calc w * (B * P ^ 2) = B * (w * P ^ 2) := by ring
      _ ≤ _ := this
  have hK2 : K ≤ K ^ 2 := le_self_pow₀ hK two_ne_zero
  have hK3 : K ^ 2 ≤ K ^ 3 := pow_le_pow_right₀ hK (by norm_num)
  have hK4 : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have m : ∀ {a b : ℝ}, a ≤ b → a * X ≤ b * X := fun h => mul_le_mul_of_nonneg_right h hX0
  -- the terms
  have t1 : |-(c * c') * κi| ≤ K ^ 4 * X := by
    have : |-(c * c') * κi| ≤ N * N' * K := by
      refine abs_mul_le_mul' ?_ hκ
      rw [abs_neg]
      exact abs_mul_le_mul' hc hc'
    have h2 : N * N' * K ≤ K * X := by
      rw [mul_comm K]
      exact mul_le_mul_of_nonneg_right hB1 hK0
    have h3 := m (hK2.trans (hK3.trans hK4))
    linarith
  have t2 : |τ * τ' * q ^ 2| ≤ K ^ 4 * X := by
    have hq2 : |q ^ 2| ≤ K ^ 2 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg q) hq 2
    have : |τ * τ' * q ^ 2| ≤ N * N' * K ^ 2 := abs_mul_le_mul' (abs_mul_le_mul' hτ hτ') hq2
    have h2 : N * N' * K ^ 2 ≤ K ^ 2 * X := by
      rw [mul_comm (K ^ 2)]
      exact mul_le_mul_of_nonneg_right hB1 (by positivity)
    have h3 := m (hK3.trans hK4)
    linarith
  have t3 : |τ * Y'| ≤ K ^ 4 * X := by
    have : |τ * Y'| ≤ N * (K * N' * P) := abs_mul_le_mul' hτ hY'
    have h2 : N * (K * N' * P) = K * (B * P) := by rw [hB]; ring
    have h3 : K * (B * P) ≤ K * X := mul_le_mul_of_nonneg_left hBP hK0
    have h4 := m (hK2.trans (hK3.trans hK4))
    linarith
  have t4 : |τ' * Y| ≤ K ^ 4 * X := by
    have : |τ' * Y| ≤ N' * (K * N * P) := abs_mul_le_mul' hτ' hY
    have h2 : N' * (K * N * P) = K * (B * P) := by rw [hB]; ring
    have h3 : K * (B * P) ≤ K * X := mul_le_mul_of_nonneg_left hBP hK0
    have h4 := m (hK2.trans (hK3.trans hK4))
    linarith
  have hYY : |Y * Y'| ≤ K ^ 2 * (B * P ^ 2) := by
    have := abs_mul_le_mul' hY hY'
    refine this.trans (le_of_eq ?_)
    rw [hB]
    ring
  have t5 : |w * Y * Y'| ≤ K ^ 4 * X := by
    have : |w * Y * Y'| ≤ w * (K ^ 2 * (B * P ^ 2)) := by
      rw [mul_assoc, abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left hYY hw
    have h2 : w * (K ^ 2 * (B * P ^ 2)) = K ^ 2 * (w * (B * P ^ 2)) := by ring
    have h3 : K ^ 2 * (w * (B * P ^ 2)) ≤ K ^ 2 * X :=
      mul_le_mul_of_nonneg_left hwBP2 (by positivity)
    have h4 := m (hK3.trans hK4)
    linarith
  -- the bracket
  have s1 : |ξ * Y * Y'| ≤ K ^ 3 * (B * P ^ 2) := by
    have := abs_mul_le_mul' hξ hYY
    rw [mul_assoc]
    refine this.trans (le_of_eq ?_)
    ring
  have s2 : |(τ * Y' + τ' * Y) * (y - q)| ≤ 4 * K ^ 2 * (B * P ^ 2) := by
    have h1 : |τ * Y' + τ' * Y| ≤ 2 * K * (B * P) := by
      refine (abs_add_le _ _).trans ?_
      have a1 : |τ * Y'| ≤ N * (K * N' * P) := abs_mul_le_mul' hτ hY'
      have a2 : |τ' * Y| ≤ N' * (K * N * P) := abs_mul_le_mul' hτ' hY
      have e1 : N * (K * N' * P) = K * (B * P) := by rw [hB]; ring
      have e2 : N' * (K * N * P) = K * (B * P) := by rw [hB]; ring
      linarith
    have h2 : |y - q| ≤ 2 * K * P := by
      refine (abs_sub _ _).trans ?_
      have : K * 1 ≤ K * P := mul_le_mul_of_nonneg_left hP hK0
      linarith
    refine (abs_mul_le_mul' h1 h2).trans (le_of_eq ?_)
    ring
  have s3 : |q * τ * τ' * y ^ 2| ≤ K ^ 3 * (B * P ^ 2) := by
    have hy2 : |y ^ 2| ≤ K ^ 2 * P ^ 2 := by
      rw [abs_pow, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg y) hy 2
    have h1 : |q * τ * τ'| ≤ K * N * N' := abs_mul_le_mul' (abs_mul_le_mul' hq hτ) hτ'
    refine (abs_mul_le_mul' h1 hy2).trans (le_of_eq ?_)
    rw [hB]
    ring
  set S := ξ * Y * Y' + (τ * Y' + τ' * Y) * (y - q) + q * τ * τ' * y ^ 2 with hS
  have hSb : |S| ≤ 6 * K ^ 3 * (B * P ^ 2) := by
    have h := abs_add_three (ξ * Y * Y') ((τ * Y' + τ' * Y) * (y - q)) (q * τ * τ' * y ^ 2)
    have h2 : 4 * K ^ 2 * (B * P ^ 2) ≤ 4 * K ^ 3 * (B * P ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK3 (by norm_num)) (by positivity)
    rw [hS]
    linarith
  have hm : |1 + ξ - w| ≤ 2 * K * (1 + w) := by
    have h1 : |1 + ξ - w| ≤ 1 + K + w := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg hw]
      have := (abs_add_le 1 ξ)
      rw [abs_one] at this
      linarith
    have h2 : w ≤ K * w := le_mul_of_one_le_left hw hK
    linarith
  have t6 : |(1 + ξ - w) * S| ≤ 12 * K ^ 4 * X := by
    refine (abs_mul_le_mul' hm hSb).trans (le_of_eq ?_)
    rw [hX, hQ]
    ring
  have htotal := abs_add_le (-(c * c') * κi + τ * τ' * q ^ 2 + τ * Y' + τ' * Y - w * Y * Y')
    ((1 + ξ - w) * S)
  have h5 : |-(c * c') * κi + τ * τ' * q ^ 2 + τ * Y' + τ' * Y - w * Y * Y'| ≤
      |-(c * c') * κi| + |τ * τ' * q ^ 2| + |τ * Y'| + |τ' * Y| + |w * Y * Y'| := by
    refine (abs_sub _ _).trans ?_
    have a1 := abs_add_le (-(c * c') * κi + τ * τ' * q ^ 2 + τ * Y') (τ' * Y)
    have a2 := abs_add_le (-(c * c') * κi + τ * τ' * q ^ 2) (τ * Y')
    have a3 := abs_add_le (-(c * c') * κi) (τ * τ' * q ^ 2)
    linarith
  have e : 17 * K ^ 4 * N * N' * Q = 17 * K ^ 4 * X := by rw [hX, hB]; ring
  rw [e]
  linarith

variable {ξ₀ : ℝ}

/-- The constant of `abs_gevEtaM_le_weights`. -/
noncomputable def gevK (ξ₀ : ℝ) : ℝ := 2 + 2 / |ξ₀| + 4 / ξ₀ ^ 2 + 3 * |ξ₀| / 2

lemma one_le_gevK : 1 ≤ gevK ξ₀ := by
  unfold gevK
  have : 0 ≤ 2 / |ξ₀| := by positivity
  have : 0 ≤ 4 / ξ₀ ^ 2 := by positivity
  have := abs_nonneg ξ₀
  linarith

/-- **The second derivative is bounded by weights**: with `w = u^{-1/ξ}`, `L = log u`, for `η` in
the box and `u, v > 0`,
`|M(η, v)[d, e]| ≤ 17 K⁴ |d| |e| (1 + w) (1 + |L| + (1 + v)/u)²`. -/
theorem abs_gevEtaM_le_weights (hξ₀ : ξ₀ ≠ 0) {η : ℝ × ℝ × ℝ} (hη : η ∈ gevEtaBox ξ₀) {v : ℝ}
    (hv : 0 < v) (hu : 0 < gevEtaU η v) (d e : ℝ × ℝ × ℝ) :
    |gevEtaM η v d e| ≤ 17 * gevK ξ₀ ^ 4 * gevEtaNorm d * gevEtaNorm e *
      ((1 + exp (gevEtaY η v)) *
        (1 + |log (gevEtaU η v)| + (1 + v) / gevEtaU η v) ^ 2) := by
  obtain ⟨-, h2, h3, hne, -, -, h7, -⟩ := bounds_of_mem_gevEtaBox hξ₀ hη
  have ha : 0 < |ξ₀| := abs_pos.2 hξ₀
  set K := gevK ξ₀ with hK
  have hK1 : 1 ≤ K := one_le_gevK
  set L := log (gevEtaU η v) with hL
  set u := gevEtaU η v with hu_def
  set P := 1 + |L| + (1 + v) / u with hP
  have hA0 : 0 ≤ (1 + v) / u := by positivity
  have hP1 : 1 ≤ P := by rw [hP]; have := abs_nonneg L; linarith
  have hξi : |1 / η.1| ≤ 2 / |ξ₀| := by
    rw [abs_div, abs_one, div_le_div_iff₀ (by linarith) ha]
    linarith
  have hq : |1 / η.1| ≤ K := by
    refine hξi.trans ?_
    have : 0 ≤ 4 / ξ₀ ^ 2 := by positivity
    rw [hK, gevK]
    linarith
  have hq2 : (1 / η.1) ^ 2 ≤ K := by
    have h : (1 / η.1) ^ 2 ≤ (2 / |ξ₀|) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hξi 2
    have e : (2 / |ξ₀|) ^ 2 = 4 / ξ₀ ^ 2 := by
      rw [div_pow, sq_abs]
      norm_num
    rw [e] at h
    refine h.trans ?_
    have : 0 ≤ 2 / |ξ₀| := by positivity
    rw [hK, gevK]
    linarith
  have hξ : |η.1| ≤ K := by
    refine h3.trans ?_
    have : 0 ≤ 2 / |ξ₀| := by positivity
    have : 0 ≤ 4 / ξ₀ ^ 2 := by positivity
    rw [hK, gevK]
    linarith
  have hκ : |1 / η.2.2 ^ 2| ≤ K := by
    have hκ0 : 0 < η.2.2 := by linarith
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have : (3 / 4) ^ 2 ≤ η.2.2 ^ 2 := pow_le_pow_left₀ (by norm_num) h7 2
    have hK2 : 2 ≤ K := by
      have : 0 ≤ 2 / |ξ₀| := by positivity
      have : 0 ≤ 4 / ξ₀ ^ 2 := by positivity
      rw [hK, gevK]
      linarith
    nlinarith
  have hDY : ∀ f : ℝ × ℝ × ℝ, |gevEtaDY η v f| ≤ K * gevEtaNorm f * P := fun f => by
    have hf1 := abs_fst_le_gevEtaNorm f
    have hf2 := abs_snd_fst_le_gevEtaNorm f
    have hf3 := abs_snd_snd_le_gevEtaNorm f
    have hN := gevEtaNorm_nonneg f
    have e : gevEtaDY η v f = f.1 * L * (1 / η.1) ^ 2 -
        (f.2.1 + f.2.2 * v) * (1 / η.1) * (1 / u) := by
      simp only [gevEtaDY, ← hu_def, ← hL]
      field_simp
    rw [e]
    have hb : |f.2.1 + f.2.2 * v| ≤ gevEtaNorm f * (1 + v) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hv]
      nlinarith
    have a1 : |f.1 * L * (1 / η.1) ^ 2| ≤ gevEtaNorm f * |L| * K := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (1 / η.1))]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hf1 (abs_nonneg L)) hq2 (sq_nonneg _)
        (by positivity)
    have a2 : |(f.2.1 + f.2.2 * v) * (1 / η.1) * (1 / u)| ≤
        gevEtaNorm f * K * ((1 + v) / u) := by
      have e2 : (f.2.1 + f.2.2 * v) * (1 / η.1) * (1 / u) =
          (f.2.1 + f.2.2 * v) * (1 / u) * (1 / η.1) := by ring
      have b1 := abs_mul_le_mul' hb (abs_of_pos (one_div_pos.2 hu)).le
      have b2 := abs_mul_le_mul' b1 hq
      rw [e2]
      refine b2.trans (le_of_eq ?_)
      field_simp
    refine (abs_sub _ _).trans ?_
    have hLa := abs_nonneg L
    have e3 : K * gevEtaNorm f * P = gevEtaNorm f * |L| * K + gevEtaNorm f * K * ((1 + v) / u) +
        K * gevEtaNorm f := by
      rw [hP]; ring
    have : 0 ≤ K * gevEtaNorm f := by positivity
    linarith
  have hy : |gevEtaY η v| ≤ K * P := by
    have e : gevEtaY η v = -L * (1 / η.1) := by
      simp only [gevEtaY, ← hu_def, ← hL]
      ring
    rw [e, abs_mul, abs_neg, mul_comm]
    refine mul_le_mul hq ?_ (abs_nonneg L) (by linarith)
    rw [hP]
    linarith
  have hmain := abs_M_le (τ := d.1) (τ' := e.1) (c := d.2.2) (c' := e.2.2)
    (Y := gevEtaDY η v d) (Y' := gevEtaDY η v e) (w := exp (gevEtaY η v)) (y := gevEtaY η v)
    (ξ := η.1) (q := 1 / η.1) (κi := 1 / η.2.2 ^ 2) hK1 hP1 (gevEtaNorm_nonneg d)
    (gevEtaNorm_nonneg e) (exp_pos _).le (abs_fst_le_gevEtaNorm d) (abs_fst_le_gevEtaNorm e)
    (abs_snd_snd_le_gevEtaNorm d) (abs_snd_snd_le_gevEtaNorm e) (hDY d) (hDY e) hy hξ hq hκ
  convert hmain using 2
  simp only [gevEtaM, gevEtaDDY]
  generalize gevEtaDY η v d = Yd
  generalize gevEtaDY η v e = Ye
  generalize exp (gevEtaY η v) = w
  generalize gevEtaY η v = y
  field_simp

end Weights

/-! ### From the weights to the envelope -/

section Envelope

variable {ξ₀ ε : ℝ}

/-- **The two-sided bound under a comparison of `u` with `v`.** If the envelopes at `u` are
controlled by the envelopes at `v`, with constant `Kc`, and `(1 + v)/u ≤ Kc (1 + 1/v)`, then
`|M(η, v)[d, e]| ≤ K |d| |e| E(v)`, with `K` depending on `ξ₀, ε, Kc` only. -/
theorem exists_abs_gevEtaM_le_of_control (hξ₀ : ξ₀ ≠ 0) (hε : 0 < ε) {Kc : ℝ} (hKc : 0 ≤ Kc) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η ∈ gevEtaBox ξ₀, ∀ v : ℝ, 0 < v → 0 < gevEtaU η v →
      gevEnv (gevAw ξ₀) (gevBw ξ₀) (gevEtaU η v) ≤ Kc * gevEnv (gevAw ξ₀) (gevBw ξ₀) v →
      gevEnv ε ε (gevEtaU η v) ≤ Kc * gevEnv ε ε v →
      (1 + v) / gevEtaU η v ≤ Kc * (1 + 1 / v) →
      ∀ d e : ℝ × ℝ × ℝ, |gevEtaM η v d e| ≤ K * gevEtaNorm d * gevEtaNorm e * gevEnvM ξ₀ ε v := by
  set KP := 1 + 2 * Kc / ε + 2 * Kc + 2 * Kc with hKP
  have hKP1 : 1 ≤ KP := by
    have : 0 ≤ 2 * Kc / ε := by positivity
    rw [hKP]
    linarith
  have hKg := one_le_gevK (ξ₀ := ξ₀)
  refine ⟨17 * gevK ξ₀ ^ 4 * ((1 + Kc) * KP ^ 2 * (2 * 3 * 3)), by positivity,
    fun η hη v hv hu h1 h2 h3 d e => ?_⟩
  have hw := abs_gevEtaM_le_weights hξ₀ hη hv hu d e
  obtain ⟨hd, -, -, -, -, -, -, -⟩ := bounds_of_mem_gevEtaBox hξ₀ hη
  set u := gevEtaU η v with hu_def
  have hAw := gevAw_nonneg (ξ₀ := ξ₀)
  have hBw := gevBw_nonneg (ξ₀ := ξ₀)
  set Ew := gevEnv (gevAw ξ₀) (gevBw ξ₀) v with hEw
  set EP := gevEnv (1 + ε) ε v with hEP
  have hEw1 : 1 ≤ Ew := one_le_gevEnv hv hAw hBw
  have hEP1 : 1 ≤ EP := one_le_gevEnv hv (by linarith) hε.le
  -- `w`
  have hexp : exp (gevEtaY η v) = u ^ (-1 / η.1) := by
    rw [rpow_def_of_pos hu]
    congr 1
    simp only [gevEtaY, ← hu_def]
    ring
  obtain ⟨r1, r2⟩ := neg_one_div_mem hξ₀ hd
  have hw1 : 1 + exp (gevEtaY η v) ≤ (1 + Kc) * Ew := by
    rw [hexp]
    have := (rpow_le_gevEnv hu r1 r2).trans h1
    have h9 : 0 ≤ Kc * Ew := by positivity
    nlinarith
  -- the second factor
  have hE1 : gevEnv ε ε v ≤ 2 * EP :=
    gevEnv_le_of_le hv hε.le hε.le (by linarith) le_rfl
  have hinv : 1 / v ≤ EP := by
    rw [one_div]
    exact inv_le_gevEnv hv (by linarith) hε.le
  have hL : |log u| ≤ Kc / ε * (2 * EP) := by
    have a := abs_log_le_gevEnv hε hu
    have b : gevEnv ε ε u / ε ≤ Kc * gevEnv ε ε v / ε :=
      div_le_div_of_nonneg_right h2 hε.le
    have c : Kc * gevEnv ε ε v / ε ≤ Kc / ε * (2 * EP) := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hE1 (by positivity)
    linarith
  have hP : 1 + |log u| + (1 + v) / u ≤ KP * EP := by
    have a : (1 + v) / u ≤ Kc * (1 + EP) :=
      h3.trans (mul_le_mul_of_nonneg_left (by linarith) hKc)
    have e : KP * EP = EP + 2 * Kc / ε * EP + 2 * Kc * EP + 2 * Kc * EP := by rw [hKP]; ring
    have b : Kc / ε * (2 * EP) = 2 * Kc / ε * EP := by ring
    have c : Kc * (1 + EP) ≤ 2 * Kc * EP := by nlinarith
    have d' : 0 ≤ 2 * Kc * EP := by positivity
    rw [e]
    linarith
  have hP0 : 0 ≤ 1 + |log u| + (1 + v) / u := by
    have := abs_nonneg (log u)
    positivity
  have hP2 : (1 + |log u| + (1 + v) / u) ^ 2 ≤ (KP * EP) ^ 2 := pow_le_pow_left₀ hP0 hP 2
  -- the envelope
  have h1a : (0 : ℝ) ≤ 1 + ε := by linarith
  have hprod1 : EP * EP ≤ 3 * gevEnv (1 + ε + (1 + ε)) (ε + ε) v :=
    gevEnv_mul_le hv h1a hε.le h1a hε.le
  have hprod2 : Ew * gevEnv (1 + ε + (1 + ε)) (ε + ε) v ≤
      3 * gevEnv (gevAw ξ₀ + (1 + ε + (1 + ε))) (gevBw ξ₀ + (ε + ε)) v :=
    gevEnv_mul_le hv hAw hBw (by linarith) (by linarith)
  have hEM : gevEnv (gevAw ξ₀ + (1 + ε + (1 + ε))) (gevBw ξ₀ + (ε + ε)) v = gevEnvM ξ₀ ε v := by
    rw [gevEnvM]
    congr 1 <;> ring
  rw [hEM] at hprod2
  have hEE : Ew * (EP * EP) ≤ 3 * 3 * gevEnvM ξ₀ ε v := by
    calc Ew * (EP * EP) ≤ Ew * (3 * gevEnv (1 + ε + (1 + ε)) (ε + ε) v) :=
          mul_le_mul_of_nonneg_left hprod1 (by positivity)
      _ = 3 * (Ew * gevEnv (1 + ε + (1 + ε)) (ε + ε) v) := by ring
      _ ≤ 3 * (3 * gevEnvM ξ₀ ε v) := by linarith
      _ = _ := by ring
  have hfinal : (1 + exp (gevEtaY η v)) * (1 + |log u| + (1 + v) / u) ^ 2 ≤
      (1 + Kc) * KP ^ 2 * (2 * 3 * 3) * gevEnvM ξ₀ ε v := by
    have hEM0 : 0 ≤ gevEnvM ξ₀ ε v := by
      have := one_le_gevEnvM (ξ₀ := ξ₀) hε hv
      linarith
    calc (1 + exp (gevEtaY η v)) * (1 + |log u| + (1 + v) / u) ^ 2
        ≤ ((1 + Kc) * Ew) * (KP * EP) ^ 2 :=
          mul_le_mul hw1 hP2 (sq_nonneg _) (by positivity)
      _ = (1 + Kc) * KP ^ 2 * (Ew * (EP * EP)) := by ring
      _ ≤ (1 + Kc) * KP ^ 2 * (3 * 3 * gevEnvM ξ₀ ε v) :=
          mul_le_mul_of_nonneg_left hEE (by positivity)
      _ ≤ (1 + Kc) * KP ^ 2 * (2 * 3 * 3) * gevEnvM ξ₀ ε v := by
          have : 0 ≤ (1 + Kc) * KP ^ 2 * gevEnvM ξ₀ ε v := by positivity
          nlinarith
  have hN := mul_nonneg (gevEtaNorm_nonneg d) (gevEtaNorm_nonneg e)
  refine hw.trans ?_
  calc 17 * gevK ξ₀ ^ 4 * gevEtaNorm d * gevEtaNorm e *
        ((1 + exp (gevEtaY η v)) * (1 + |log u| + (1 + v) / u) ^ 2)
      ≤ 17 * gevK ξ₀ ^ 4 * gevEtaNorm d * gevEtaNorm e *
        ((1 + Kc) * KP ^ 2 * (2 * 3 * 3) * gevEnvM ξ₀ ε v) :=
        mul_le_mul_of_nonneg_left hfinal
          (mul_nonneg (mul_nonneg (by positivity) (gevEtaNorm_nonneg d)) (gevEtaNorm_nonneg e))
    _ = _ := by ring

/-- **The two-sided bound for good observations**: if `v/2 ≤ u ≤ 2v`, then
`|M(η, v)[d, e]| ≤ K |d| |e| E(v)`. -/
theorem exists_abs_gevEtaM_le_of_comparable (hξ₀ : ξ₀ ≠ 0) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η ∈ gevEtaBox ξ₀, ∀ v : ℝ, 0 < v → v / 2 ≤ gevEtaU η v →
      gevEtaU η v ≤ 2 * v →
      ∀ d e : ℝ × ℝ × ℝ, |gevEtaM η v d e| ≤ K * gevEtaNorm d * gevEtaNorm e * gevEnvM ξ₀ ε v := by
  have hAw := gevAw_nonneg (ξ₀ := ξ₀)
  have hBw := gevBw_nonneg (ξ₀ := ξ₀)
  set Kc : ℝ := 2 ^ (gevAw ξ₀ + gevBw ξ₀) + 2 ^ (ε + ε) + 2 with hKc
  have p1 : (0 : ℝ) < 2 ^ (gevAw ξ₀ + gevBw ξ₀) := by positivity
  have p2 : (0 : ℝ) < 2 ^ (ε + ε) := by positivity
  obtain ⟨K, hK0, hK⟩ := exists_abs_gevEtaM_le_of_control hξ₀ hε (Kc := Kc) (by positivity)
  refine ⟨K, hK0, fun η hη v hv h1 h2 d e => hK η hη v hv (by linarith [half_pos hv]) ?_ ?_ ?_ d e⟩
  · have := gevEnv_le_of_comparable (a := gevAw ξ₀) (b := gevBw ξ₀) hv one_le_two h1 h2 hAw hBw
    have h3 : 0 ≤ gevEnv (gevAw ξ₀) (gevBw ξ₀) v := gevEnv_nonneg hv.le
    refine this.trans (mul_le_mul_of_nonneg_right ?_ h3)
    rw [hKc]
    linarith
  · have := gevEnv_le_of_comparable (a := ε) (b := ε) hv one_le_two h1 h2 hε.le hε.le
    have h3 : 0 ≤ gevEnv ε ε v := gevEnv_nonneg hv.le
    refine this.trans (mul_le_mul_of_nonneg_right ?_ h3)
    rw [hKc]
    linarith
  · have hu : 0 < gevEtaU η v := by linarith [half_pos hv]
    have : (1 + v) / gevEtaU η v ≤ 2 * (1 + 1 / v) := by
      rw [div_le_iff₀ hu]
      have h5 : 2 * (1 + 1 / v) * (v / 2) = 1 + v := by
        field_simp
        ring
      have h6 : 2 * (1 + 1 / v) * (v / 2) ≤ 2 * (1 + 1 / v) * gevEtaU η v :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [hKc]
    linarith

/-- A lower bound for `u` also controls the envelope. -/
private lemma gevEnv_le_of_lower {a b u v us : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hus : 0 < us)
    (hv : 0 < v) (h1 : us ≤ u) (h2 : u ≤ 1 / 4 + 5 / 4 * v) :
    gevEnv a b u ≤ (us ^ (-a) + 2 ^ b * 2) * gevEnv a b v := by
  have hu : 0 < u := by linarith
  have h3 : u ^ (-a) ≤ us ^ (-a) := rpow_le_rpow_of_nonpos hus h1 (by linarith)
  have hE1 : 1 ≤ gevEnv a b v := one_le_gevEnv hv ha hb
  have hvb : v ^ b ≤ gevEnv a b v := rpow_le_gevEnv hv (by linarith) le_rfl
  have hub : u ^ b ≤ 2 ^ b * 2 * gevEnv a b v := by
    have h2b : (0 : ℝ) < 2 ^ b := by positivity
    rcases le_total v 1 with h | h
    · have : u ^ b ≤ 2 ^ b := rpow_le_rpow hu.le (by linarith) hb
      nlinarith
    · have : u ^ b ≤ (2 * v) ^ b := rpow_le_rpow hu.le (by linarith) hb
      rw [mul_rpow (by norm_num) hv.le] at this
      nlinarith
  have hus0 : 0 ≤ us ^ (-a) := by positivity
  unfold gevEnv at *
  nlinarith

/-- `|M(η, v)[d, e]| ≤ K |d| |e| E(v)` as soon as `u` is bounded below. -/
private lemma exists_abs_gevEtaM_le_of_lower (hξ₀ : ξ₀ ≠ 0) (hε : 0 < ε) {us : ℝ} (hus : 0 < us) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η ∈ gevEtaBox ξ₀, ∀ v : ℝ, 0 < v → us ≤ gevEtaU η v →
      ∀ d e : ℝ × ℝ × ℝ, |gevEtaM η v d e| ≤ K * gevEtaNorm d * gevEtaNorm e * gevEnvM ξ₀ ε v := by
  have hAw := gevAw_nonneg (ξ₀ := ξ₀)
  have hBw := gevBw_nonneg (ξ₀ := ξ₀)
  set K1 := us ^ (-gevAw ξ₀) + 2 ^ gevBw ξ₀ * 2 with hK1
  set K2 := us ^ (-ε) + 2 ^ ε * 2 with hK2
  have p1 : 0 ≤ K1 := by positivity
  have p2 : 0 ≤ K2 := by positivity
  set K3 := 4 / 3 * (1 / us + 1) with hK3
  have p3 : 0 ≤ K3 := by positivity
  set Kc := K1 + K2 + K3 with hKc
  obtain ⟨K, hK0, hK⟩ := exists_abs_gevEtaM_le_of_control hξ₀ hε (Kc := Kc) (by positivity)
  refine ⟨K, hK0, fun η hη v hv h1 d e => ?_⟩
  have hu : 0 < gevEtaU η v := by linarith
  have h2 := gevEtaU_le hξ₀ hη hv.le
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := bounds_of_mem_gevEtaBox hξ₀ hη
  refine hK η hη v hv hu ?_ ?_ ?_ d e
  · refine (gevEnv_le_of_lower hAw hBw hus hv h1 h2).trans
      (mul_le_mul_of_nonneg_right ?_ (gevEnv_nonneg hv.le))
    linarith
  · refine (gevEnv_le_of_lower hε.le hε.le hus hv h1 h2).trans
      (mul_le_mul_of_nonneg_right ?_ (gevEnv_nonneg hv.le))
    linarith
  · have hvle : 1 + v ≤ 4 / 3 * (1 + gevEtaU η v) := by
      have := (abs_le.1 h6).1
      unfold gevEtaU at *
      nlinarith
    have h4 : (1 + v) / gevEtaU η v ≤ K3 := by
      rw [div_le_iff₀ hu, hK3]
      have h5 : 1 ≤ 1 / us * gevEtaU η v := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hus]
        linarith
      nlinarith
    have h5 : K3 ≤ Kc := by rw [hKc]; linarith
    have h6' : 1 ≤ 1 + 1 / v := by
      have : 0 < 1 / v := by positivity
      linarith
    have hKc0 : 0 ≤ Kc := by positivity
    nlinarith

end Envelope

/-! ### The one-sided bound -/

section OneSided

/-- A quadratic form with the right discriminant is nonpositive. -/
lemma quad_nonpos_of_discriminant {ξ q y m w Y τ : ℝ} (hq : ξ * q = 1) (hw : 0 ≤ w)
    (h1 : m * ξ ≤ 0) (h2 : m * (y - q) ≤ 0) (h3 : 1 ≤ m ^ 2 * (2 * y * q - q ^ 2)) :
    2 * τ * Y - w * Y ^ 2 + m * (ξ * Y ^ 2 + 2 * τ * Y * (y - q) + q * τ ^ 2 * y ^ 2) ≤ 0 := by
  set A := w - m * ξ with hA
  set B := 1 + m * (y - q) with hB
  set C := -(m * q) * y ^ 2 with hC
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hmq : m * q ≤ 0 := by
    have : m * q = (m * ξ) * q ^ 2 := by
      have : (m * ξ) * q ^ 2 = m * q * (ξ * q) := by ring
      rw [this, hq, mul_one]
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg h1 (sq_nonneg q)
  have hC0 : 0 ≤ C := mul_nonneg (by linarith) (sq_nonneg y)
  have hdisc : B ^ 2 ≤ A * C := by
    have e : A * C - B ^ 2 = -(w * (m * q) * y ^ 2) - 2 * (m * (y - q)) +
        (m ^ 2 * (2 * y * q - q ^ 2) - 1) + m ^ 2 * y ^ 2 * (ξ * q - 1) := by
      rw [hA, hB, hC]
      ring
    have h4 : 0 ≤ -(w * (m * q) * y ^ 2) := by
      have : w * (m * q) * y ^ 2 = -(w * (-(m * q) * y ^ 2)) := by ring
      rw [this, neg_neg]
      exact mul_nonneg hw hC0
    rw [hq, sub_self, mul_zero] at e
    linarith
  have e : 2 * τ * Y - w * Y ^ 2 + m * (ξ * Y ^ 2 + 2 * τ * Y * (y - q) + q * τ ^ 2 * y ^ 2) =
      -A * Y ^ 2 + 2 * B * τ * Y - C * τ ^ 2 := by
    rw [hA, hB, hC]
    ring
  rw [e]
  rcases hA0.eq_or_lt with h | h
  · have hB0 : B = 0 := by
      rw [← h, zero_mul] at hdisc
      nlinarith [sq_nonneg B]
    rw [← h, hB0]
    nlinarith [mul_nonneg hC0 (sq_nonneg τ)]
  · have h5 : A * (-A * Y ^ 2 + 2 * B * τ * Y - C * τ ^ 2) ≤ 0 := by
      have e2 : A * (-A * Y ^ 2 + 2 * B * τ * Y - C * τ ^ 2) =
          -(A * Y - B * τ) ^ 2 - (A * C - B ^ 2) * τ ^ 2 := by ring
      rw [e2]
      nlinarith [sq_nonneg (A * Y - B * τ), mul_nonneg (sub_nonneg.2 hdisc) (sq_nonneg τ)]
    by_contra h6
    push Not at h6
    have := mul_pos h h6
    linarith

/-- **The threshold**: when `L = log u` is sufficiently negative (when `u` is small), the
discriminant condition of `quad_nonpos_of_discriminant` holds, for both signs of the shape. -/
lemma exists_log_threshold {ξ₀ : ℝ} (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ ξ : ℝ, |ξ - ξ₀| ≤ |ξ₀| / 2 → ∀ L : ℝ, L ≤ -L₀ →
      (1 + ξ - exp (-L / ξ)) * ξ ≤ 0 ∧ (1 + ξ - exp (-L / ξ)) * (-L / ξ - 1 / ξ) ≤ 0 ∧
        1 ≤ (1 + ξ - exp (-L / ξ)) ^ 2 * (2 * (-L / ξ) * (1 / ξ) - (1 / ξ) ^ 2) := by
  set ξM := 3 * |ξ₀| / 2 with hξM
  have hξM0 : 0 ≤ ξM := by positivity
  refine ⟨max 19 (ξM * (1 + 2 * ξM)), (by norm_num : (1 : ℝ) ≤ 19).trans (le_max_left _ _),
    fun ξ hξ L hL => ?_⟩
  have hL19 : L ≤ -19 := hL.trans (neg_le_neg (le_max_left _ _))
  have hLM : L ≤ -(ξM * (1 + 2 * ξM)) := hL.trans (neg_le_neg (le_max_right _ _))
  set ℓ := -L with hℓ
  have hℓ19 : 19 ≤ ℓ := by rw [hℓ]; linarith
  have hℓM : ξM * (1 + 2 * ξM) ≤ ℓ := by rw [hℓ]; linarith
  have hb := abs_le.1 hξ
  rcases lt_or_gt_of_ne hξ₀0 with h | h
  · -- negative shape: `w` is small and `m ≥ 1/8`
    rw [abs_of_neg h] at hb
    have hξlo : -(3 / 4) < ξ := by linarith [hb.1]
    have hξhi : ξ < 0 := by linarith [hb.2]
    have hξa : ξ ^ 2 ≤ (3 / 4) ^ 2 := by nlinarith
    have hξ2 : 0 < ξ ^ 2 := sq_pos_of_neg hξhi
    have hy : ℓ / ξ ≤ -ℓ := by
      rw [div_le_iff_of_neg hξhi]
      nlinarith
    have hw : exp (ℓ / ξ) ≤ 1 / 20 := by
      have h1 : exp (ℓ / ξ) ≤ exp (-ℓ) := exp_le_exp.2 hy
      have h2 : 1 + ℓ ≤ exp ℓ := by linarith [add_one_le_exp ℓ]
      have h3 : exp (-ℓ) ≤ 1 / 20 := by
        rw [exp_neg, inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hw0 := exp_pos (ℓ / ξ)
    set m := 1 + ξ - exp (ℓ / ξ) with hm
    have hm8 : 1 / 8 ≤ m := by rw [hm]; linarith
    refine ⟨mul_nonpos_of_nonneg_of_nonpos (by linarith) hξhi.le, ?_, ?_⟩
    · have e : ℓ / ξ - 1 / ξ = (ℓ - 1) / ξ := by ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (div_nonpos_of_nonneg_of_nonpos (by linarith) hξhi.le)
    · have e : 2 * (ℓ / ξ) * (1 / ξ) - (1 / ξ) ^ 2 = (2 * ℓ - 1) / ξ ^ 2 := by
        field_simp
      rw [e, mul_div_assoc', le_div_iff₀ hξ2, one_mul]
      have hm2 : (1 / 8) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm8 2
      nlinarith
  · -- positive shape: `w` is large and `m ≤ -(1 + ξ)`
    rw [abs_of_pos h] at hb
    have hξ0 : 0 < ξ := by linarith [hb.1]
    have hξle : ξ ≤ ξM := by rw [hξM, abs_of_pos h]; linarith [hb.2]
    have hy : 1 + 2 * ξ ≤ ℓ / ξ := by
      rw [le_div_iff₀ hξ0]
      nlinarith
    have hw : 2 + 2 * ξ ≤ exp (ℓ / ξ) := by linarith [add_one_le_exp (ℓ / ξ)]
    set m := 1 + ξ - exp (ℓ / ξ) with hm
    have hm0 : m ≤ -(1 + ξ) := by rw [hm]; linarith
    have hξ2 : 0 < ξ ^ 2 := by positivity
    refine ⟨mul_nonpos_of_nonpos_of_nonneg (by linarith) hξ0.le, ?_, ?_⟩
    · have e : ℓ / ξ - 1 / ξ = (ℓ - 1) / ξ := by ring
      rw [e]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (div_nonneg (by linarith) hξ0.le)
    · have e : 2 * (ℓ / ξ) * (1 / ξ) - (1 / ξ) ^ 2 = (2 * ℓ - 1) / ξ ^ 2 := by
        field_simp
      rw [e, mul_div_assoc', le_div_iff₀ hξ2, one_mul]
      have hm2 : (1 + ξ) ^ 2 ≤ m ^ 2 := by nlinarith
      nlinarith

variable {ξ₀ ε : ℝ}

/-- **When `u` is small the blow-up has the good sign**: if `log u ≤ -L₀`, then
`M(η, v)[d, d] ≤ d₁²/ξ²`. -/
theorem gevEtaM_self_le_of_log_le {L₀ : ℝ} (h : ∀ ξ : ℝ, |ξ - ξ₀| ≤ |ξ₀| / 2 → ∀ L : ℝ, L ≤ -L₀ →
      (1 + ξ - exp (-L / ξ)) * ξ ≤ 0 ∧ (1 + ξ - exp (-L / ξ)) * (-L / ξ - 1 / ξ) ≤ 0 ∧
        1 ≤ (1 + ξ - exp (-L / ξ)) ^ 2 * (2 * (-L / ξ) * (1 / ξ) - (1 / ξ) ^ 2))
    (hξ₀ : ξ₀ ≠ 0) {η : ℝ × ℝ × ℝ} (hη : η ∈ gevEtaBox ξ₀) {v : ℝ}
    (hL : log (gevEtaU η v) ≤ -L₀) (d : ℝ × ℝ × ℝ) :
    gevEtaM η v d d ≤ d.1 ^ 2 / η.1 ^ 2 := by
  obtain ⟨hd, -, -, hne, -, -, h7, -⟩ := bounds_of_mem_gevEtaBox hξ₀ hη
  obtain ⟨h1, h2, h3⟩ := h η.1 hd _ hL
  have hq := quad_nonpos_of_discriminant (ξ := η.1) (q := 1 / η.1) (y := gevEtaY η v)
    (m := 1 + η.1 - exp (gevEtaY η v)) (w := exp (gevEtaY η v)) (Y := gevEtaDY η v d) (τ := d.1)
    (by field_simp) (exp_pos _).le h1 h2 h3
  have hκ : 0 ≤ d.2.2 ^ 2 / η.2.2 ^ 2 := by positivity
  have e : gevEtaM η v d d = -(d.2.2 ^ 2 / η.2.2 ^ 2) + d.1 ^ 2 / η.1 ^ 2 +
      (2 * d.1 * gevEtaDY η v d - exp (gevEtaY η v) * gevEtaDY η v d ^ 2 +
        (1 + η.1 - exp (gevEtaY η v)) * (η.1 * gevEtaDY η v d ^ 2 +
          2 * d.1 * gevEtaDY η v d * (gevEtaY η v - 1 / η.1) +
          1 / η.1 * d.1 ^ 2 * gevEtaY η v ^ 2)) := by
    simp only [gevEtaM, gevEtaDDY]
    ring
  rw [e]
  linarith

/-- **The one-sided bound for every observation in the support of `η`**:
`M(η, v)[d, d] ≤ K |d|² E(v)`. -/
theorem exists_gevEtaM_self_le (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η ∈ gevEtaBox ξ₀, ∀ v : ℝ, 0 < v → 0 < gevEtaU η v → ∀ d : ℝ × ℝ × ℝ,
      gevEtaM η v d d ≤ K * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v := by
  obtain ⟨L₀, -, hL₀⟩ := exists_log_threshold hξ₀ hξ₀0
  obtain ⟨K, hK0, hK⟩ := exists_abs_gevEtaM_le_of_lower hξ₀0 hε (exp_pos (-L₀))
  have ha : 0 < |ξ₀| := abs_pos.2 hξ₀0
  refine ⟨K + 4 / ξ₀ ^ 2, by positivity, fun η hη v hv hu d => ?_⟩
  have hE1 := one_le_gevEnvM (ξ₀ := ξ₀) hε hv
  have hN2 : 0 ≤ gevEtaNorm d ^ 2 := sq_nonneg _
  have hKE : 0 ≤ K * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v := by positivity
  have hQ : 0 ≤ 4 / ξ₀ ^ 2 * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v := by positivity
  have e : (K + 4 / ξ₀ ^ 2) * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v =
      K * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v + 4 / ξ₀ ^ 2 * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v := by
    ring
  rw [e]
  rcases le_or_gt (log (gevEtaU η v)) (-L₀) with hL | hL
  · have h1 := gevEtaM_self_le_of_log_le hL₀ hξ₀0 hη hL d
    obtain ⟨-, h2, -, hne, -, -, -, -⟩ := bounds_of_mem_gevEtaBox hξ₀0 hη
    have h3 : d.1 ^ 2 / η.1 ^ 2 ≤ 4 / ξ₀ ^ 2 * gevEtaNorm d ^ 2 := by
      have h4 : d.1 ^ 2 ≤ gevEtaNorm d ^ 2 := by
        rw [← sq_abs d.1]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_fst_le_gevEtaNorm d) 2
      have h5 : (|ξ₀| / 2) ^ 2 ≤ η.1 ^ 2 := by
        rw [← sq_abs η.1]
        exact pow_le_pow_left₀ (by positivity) h2 2
      have h6 : ξ₀ ^ 2 / 4 ≤ η.1 ^ 2 := by
        rw [div_pow, sq_abs] at h5
        norm_num at h5
        exact h5
      have h7 : 0 < ξ₀ ^ 2 := by positivity
      rw [div_le_iff₀ (by positivity : 0 < η.1 ^ 2)]
      have h8 : 4 / ξ₀ ^ 2 * (ξ₀ ^ 2 / 4) = 1 := by field_simp
      calc d.1 ^ 2 ≤ gevEtaNorm d ^ 2 := h4
        _ = gevEtaNorm d ^ 2 * (4 / ξ₀ ^ 2 * (ξ₀ ^ 2 / 4)) := by rw [h8, mul_one]
        _ ≤ gevEtaNorm d ^ 2 * (4 / ξ₀ ^ 2 * η.1 ^ 2) := by gcongr
        _ = _ := by ring
    have h4 : 4 / ξ₀ ^ 2 * gevEtaNorm d ^ 2 ≤ 4 / ξ₀ ^ 2 * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v :=
      le_mul_of_one_le_right (by positivity) hE1
    linarith
  · have hus : exp (-L₀) ≤ gevEtaU η v := by
      rw [← exp_log hu]
      exact exp_le_exp.2 hL.le
    have h1 := hK η hη v hv hus d d
    have h2 := (le_abs_self _).trans h1
    have e2 : K * gevEtaNorm d * gevEtaNorm d * gevEnvM ξ₀ ε v =
        K * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v := by ring
    linarith

end OneSided

/-! ### Uniform continuity on `{c ≤ v ≤ 1/c}` and the deviation from the truth -/

section Continuity

variable {ξ₀ ε : ℝ}

private lemma continuousAt_gevEtaM {p : (ℝ × ℝ × ℝ) × ℝ} (h1 : p.1.1 ≠ 0) (h2 : p.1.2.2 ≠ 0)
    (h3 : gevEtaU p.1 p.2 ≠ 0) (d e : ℝ × ℝ × ℝ) :
    ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevEtaM p.1 p.2 d e) p := by
  have hξ : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.1) p := by fun_prop
  have hκ : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.2) p := by fun_prop
  have hv : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => p.2) p := by fun_prop
  have hu : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevEtaU p.1 p.2) p := by
    unfold gevEtaU
    fun_prop
  have hL := hu.log h3
  have hY : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevEtaY p.1 p.2) p := by
    unfold gevEtaY
    exact hL.neg.div hξ h1
  have hW := hY.rexp
  have hDY : ∀ f : ℝ × ℝ × ℝ, ContinuousAt
      (fun p : (ℝ × ℝ × ℝ) × ℝ => gevEtaDY p.1 p.2 f) p := fun f => by
    unfold gevEtaDY
    exact ((continuousAt_const.mul hL).div (hξ.pow 2) (pow_ne_zero 2 h1)).sub
      ((continuousAt_const.add (continuousAt_const.mul hv)).div (hξ.mul hu) (mul_ne_zero h1 h3))
  have hDDY : ContinuousAt (fun p : (ℝ × ℝ × ℝ) × ℝ => gevEtaDDY p.1 p.2 d e) p := by
    unfold gevEtaDDY
    exact ((((hξ.mul (hDY d)).mul (hDY e))).add
      (((continuousAt_const.mul (hDY e)).add (continuousAt_const.mul (hDY d))).mul
        (hY.sub (continuousAt_const.div hξ h1)))).add
      ((((continuousAt_const.div hξ h1).mul continuousAt_const).mul continuousAt_const).mul
        (hY.pow 2))
  unfold gevEtaM
  exact ((((((continuousAt_const.div (hκ.pow 2) (pow_ne_zero 2 h2)).add
    (continuousAt_const.div (hξ.pow 2) (pow_ne_zero 2 h1))).add
    (continuousAt_const.mul (hDY e))).add (continuousAt_const.mul (hDY d))).sub
    ((hW.mul (hDY d)).mul (hDY e)))).add
    (((continuousAt_const.add hξ).sub hW).mul hDDY)

private lemma dist_le_gevEtaNorm (η η' : ℝ × ℝ × ℝ) : dist η η' ≤ gevEtaNorm (η - η') := by
  have h1 : dist η.1 η'.1 ≤ gevEtaNorm (η - η') := by
    rw [Real.dist_eq]
    exact abs_fst_le_gevEtaNorm (η - η')
  have h2 : dist η.2.1 η'.2.1 ≤ gevEtaNorm (η - η') := by
    rw [Real.dist_eq]
    exact abs_snd_fst_le_gevEtaNorm (η - η')
  have h3 : dist η.2.2 η'.2.2 ≤ gevEtaNorm (η - η') := by
    rw [Real.dist_eq]
    exact abs_snd_snd_le_gevEtaNorm (η - η')
  exact Prod.dist_eq.trans_le (max_le h1 (Prod.dist_eq.trans_le (max_le h2 h3)))

/-- **Uniform continuity on `{c ≤ v ≤ 1/c}`.** -/
theorem exists_delta_abs_gevEtaM_sub_le (hξ₀ : ξ₀ ≠ 0) {c : ℝ} (hc : 0 < c) {e' : ℝ}
    (he' : 0 < e') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η ∈ gevEtaBox ξ₀, gevEtaNorm (η - (ξ₀, 0, 1)) ≤ δ →
      ∀ v ∈ Icc c (1 / c), ∀ d e : ℝ × ℝ × ℝ,
        |gevEtaM η v d e - gevEtaM (ξ₀, 0, 1) v d e| ≤ e' * gevEtaNorm d * gevEtaNorm e := by
  set η₀ : ℝ × ℝ × ℝ := (ξ₀, 0, 1) with hη₀
  set C : Set ((ℝ × ℝ × ℝ) × ℝ) :=
    (gevEtaBox ξ₀ ∩ {η | |η.2.1| ≤ c / 4}) ×ˢ Icc c (1 / c) with hC
  have hCc : IsCompact C := by
    refine (isCompact_gevEtaBox.inter_right ?_).prod isCompact_Icc
    exact isClosed_le (by fun_prop) continuous_const
  have hsupp : ∀ p ∈ C, 0 < gevEtaU p.1 p.2 := fun p hp => by
    obtain ⟨⟨h1, h2⟩, h3, -⟩ := hp
    obtain ⟨-, -, -, -, -, -, h7, -⟩ := bounds_of_mem_gevEtaBox hξ₀ h1
    have h2' := (abs_le.1 (show |p.1.2.1| ≤ c / 4 from h2)).1
    unfold gevEtaU
    nlinarith
  set G : (ℝ × ℝ × ℝ) × ℝ → ℝ := fun p => ∑ j, ∑ k,
    |gevEtaM p.1 p.2 (gevEtaBasis j) (gevEtaBasis k) -
      gevEtaM η₀ p.2 (gevEtaBasis j) (gevEtaBasis k)| with hG
  have hGc : ContinuousOn G C := by
    intro p hp
    have hη := hp.1.1
    obtain ⟨-, -, -, h4, -, -, h7, -⟩ := bounds_of_mem_gevEtaBox hξ₀ hη
    have hp0 : 0 < p.2 := hc.trans_le hp.2.1
    have hu0 : gevEtaU (η₀, p.2).1 (η₀, p.2).2 ≠ 0 := by
      simp only [hη₀, gevEtaU]
      nlinarith
    refine ContinuousAt.continuousWithinAt ?_
    refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ => ?_
    refine Continuous.tendsto continuous_abs _ |>.comp ?_
    refine (continuousAt_gevEtaM h4 (by linarith) (hsupp p hp).ne' _ _).tendsto.sub ?_
    have h9 : ContinuousAt (fun q : (ℝ × ℝ × ℝ) × ℝ => (η₀, q.2)) p := by fun_prop
    have h10 := continuousAt_gevEtaM (p := (η₀, p.2)) (by simpa [hη₀] using hξ₀)
      (by simp [hη₀]) hu0 (gevEtaBasis j) (gevEtaBasis k)
    exact (ContinuousAt.comp (f := fun q : (ℝ × ℝ × ℝ) × ℝ => (η₀, q.2)) h10 h9).tendsto
  have hGu := hCc.uniformContinuousOn_of_continuous hGc
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 hGu e' he'
  refine ⟨min (δ / 2) (c / 4), by positivity, fun η hη hdist v hv d e => ?_⟩
  have hd1 : gevEtaNorm (η - η₀) ≤ δ / 2 := hdist.trans (min_le_left _ _)
  have hd2 : gevEtaNorm (η - η₀) ≤ c / 4 := hdist.trans (min_le_right _ _)
  have hk : |η.2.1| ≤ c / 4 := by
    have := abs_snd_fst_le_gevEtaNorm (η - η₀)
    simp only [Prod.snd_sub, Prod.fst_sub, hη₀, sub_zero] at this
    linarith
  have hk0 : |η₀.2.1| ≤ c / 4 := by simp only [hη₀, abs_zero]; positivity
  have hmem : ((η, v) : (ℝ × ℝ × ℝ) × ℝ) ∈ C := ⟨⟨hη, hk⟩, hv⟩
  have hmem0 : ((η₀, v) : (ℝ × ℝ × ℝ) × ℝ) ∈ C := ⟨⟨mem_gevEtaBox_self, hk0⟩, hv⟩
  have hdist' : dist ((η, v) : (ℝ × ℝ × ℝ) × ℝ) (η₀, v) < δ := by
    rw [Prod.dist_eq, dist_self]
    refine max_lt (((dist_le_gevEtaNorm η η₀).trans hd1).trans_lt (half_lt_self hδ)) hδ
  have h1 := hδu _ hmem _ hmem0 hdist'
  have hG0 : G (η₀, v) = 0 := by simp [hG]
  rw [hG0, Real.dist_eq, sub_zero] at h1
  have hG1 : G (η, v) ≤ e' := (le_abs_self _).trans h1.le
  have hNd := gevEtaNorm_nonneg d
  have hNe := gevEtaNorm_nonneg e
  have hc_d : ∀ j, |gevEtaCoord d j| ≤ gevEtaNorm d := fun j => by
    rw [gevEtaNorm_eq_sum]
    exact Finset.single_le_sum (f := fun j => |gevEtaCoord d j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
  have hc_e : ∀ j, |gevEtaCoord e j| ≤ gevEtaNorm e := fun j => by
    rw [gevEtaNorm_eq_sum]
    exact Finset.single_le_sum (f := fun j => |gevEtaCoord e j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
  rw [gevEtaM_eq_sum η v d e, gevEtaM_eq_sum η₀ v d e, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  have hb : |∑ j, ∑ k, gevEtaCoord d j * gevEtaCoord e k *
      (gevEtaM η v (gevEtaBasis j) (gevEtaBasis k) -
        gevEtaM η₀ v (gevEtaBasis j) (gevEtaBasis k))| ≤
      ∑ j, ∑ k, gevEtaNorm d * gevEtaNorm e *
        |gevEtaM η v (gevEtaBasis j) (gevEtaBasis k) -
          gevEtaM η₀ v (gevEtaBasis j) (gevEtaBasis k)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hc_d j) (hc_e k) (abs_nonneg _) hNd)
      (abs_nonneg _)
  refine hb.trans ?_
  simp_rw [← Finset.mul_sum]
  have hG2 : ∑ j, ∑ k, |gevEtaM η v (gevEtaBasis j) (gevEtaBasis k) -
      gevEtaM η₀ v (gevEtaBasis j) (gevEtaBasis k)| ≤ e' := hG1
  calc gevEtaNorm d * gevEtaNorm e * ∑ j, ∑ k, |gevEtaM η v (gevEtaBasis j) (gevEtaBasis k) -
        gevEtaM η₀ v (gevEtaBasis j) (gevEtaBasis k)|
      ≤ gevEtaNorm d * gevEtaNorm e * e' := mul_le_mul_of_nonneg_left hG2 (by positivity)
    _ = _ := by ring

/-- The error term: `K E(v)` outside `{c ≤ v ≤ 1/c}`, and `0` on this set. -/
noncomputable def gevEtaTail (ξ₀ ε K c v : ℝ) : ℝ :=
  (Icc c (1 / c))ᶜ.indicator (fun v => K * gevEnvM ξ₀ ε v) v

lemma gevEtaTail_of_mem {K c v : ℝ} (h : v ∈ Icc c (1 / c)) : gevEtaTail ξ₀ ε K c v = 0 :=
  Set.indicator_of_notMem (show v ∉ (Icc c (1 / c))ᶜ from not_not.2 h) _

lemma gevEtaTail_of_notMem {K c v : ℝ} (h : v ∉ Icc c (1 / c)) :
    gevEtaTail ξ₀ ε K c v = K * gevEnvM ξ₀ ε v :=
  Set.indicator_of_mem h _

lemma gevEtaTail_nonneg {K c v : ℝ} (hK : 0 ≤ K) (hv : 0 < v) : 0 ≤ gevEtaTail ξ₀ ε K c v :=
  Set.indicator_nonneg (fun _ _ => mul_nonneg hK (gevEnv_nonneg hv.le)) v

/-- **The deviation from the truth.** There is `K` such that for every `c, e' > 0` there is `δ > 0`
such that, for `η` in the box within `δ` of the truth, and `v > 0`:

* for an observation in the support of `η`,
  `M(η, v)[d, d] ≤ M(η₀, v)[d, d] + (e' + T(v)) |d|²`,
* for a good observation, `v/2 ≤ u ≤ 2 v`,
  `|M(η, v)[d, e] - M(η₀, v)[d, e]| ≤ (e' + T(v)) |d| |e|`,

where `T = gevEtaTail ξ₀ ε K c`. -/
theorem exists_gevEtaM_dev_le (hξ₀ : -1 / 2 < ξ₀) (hξ₀0 : ξ₀ ≠ 0) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 < c → ∀ e' : ℝ, 0 < e' → ∃ δ : ℝ, 0 < δ ∧
      ∀ η ∈ gevEtaBox ξ₀, gevEtaNorm (η - (ξ₀, 0, 1)) ≤ δ → ∀ v : ℝ, 0 < v →
        (0 < gevEtaU η v → ∀ d : ℝ × ℝ × ℝ, gevEtaM η v d d ≤ gevEtaM (ξ₀, 0, 1) v d d +
          (e' + gevEtaTail ξ₀ ε K c v) * gevEtaNorm d ^ 2) ∧
        (v / 2 ≤ gevEtaU η v → gevEtaU η v ≤ 2 * v → ∀ d e : ℝ × ℝ × ℝ,
          |gevEtaM η v d e - gevEtaM (ξ₀, 0, 1) v d e| ≤
            (e' + gevEtaTail ξ₀ ε K c v) * gevEtaNorm d * gevEtaNorm e) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_gevEtaM_self_le hξ₀ hξ₀0 hε
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_abs_gevEtaM_le_of_comparable hξ₀0 hε
  refine ⟨K₁ + 2 * K₂, by positivity, fun c hc e' he' => ?_⟩
  obtain ⟨δ, hδ, hδu⟩ := exists_delta_abs_gevEtaM_sub_le hξ₀0 hc he'
  refine ⟨δ, hδ, fun η hη hdist v hv => ?_⟩
  have hself : ∀ d e, |gevEtaM (ξ₀, 0, 1) v d e| ≤
      K₂ * gevEtaNorm d * gevEtaNorm e * gevEnvM ξ₀ ε v := fun d e => by
    refine hK₂ _ mem_gevEtaBox_self v hv ?_ ?_ d e
    · simp only [gevEtaU]; linarith
    · simp only [gevEtaU]; linarith
  by_cases hmem : v ∈ Icc c (1 / c)
  · have hT : gevEtaTail ξ₀ ε (K₁ + 2 * K₂) c v = 0 := gevEtaTail_of_mem hmem
    rw [hT, add_zero]
    refine ⟨fun _ d => ?_, fun _ _ d e => hδu η hη hdist v hmem d e⟩
    have := (le_abs_self _).trans (hδu η hη hdist v hmem d d)
    nlinarith
  · have hT : gevEtaTail ξ₀ ε (K₁ + 2 * K₂) c v = (K₁ + 2 * K₂) * gevEnvM ξ₀ ε v :=
      gevEtaTail_of_notMem hmem
    rw [hT]
    have hE0 : 0 ≤ gevEnvM ξ₀ ε v := (one_le_gevEnvM hε hv).trans' zero_le_one
    refine ⟨fun hu d => ?_, fun h1 h2 d e => ?_⟩
    · have a1 := hK₁ η hη v hv hu d
      have a2 := (abs_le.1 (hself d d)).1
      have hN := sq_nonneg (gevEtaNorm d)
      have e2 : K₂ * gevEtaNorm d * gevEtaNorm d * gevEnvM ξ₀ ε v =
          K₂ * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v := by ring
      rw [e2] at a2
      have a3 : 0 ≤ e' * gevEtaNorm d ^ 2 := by positivity
      have a4 : 0 ≤ K₂ * gevEtaNorm d ^ 2 * gevEnvM ξ₀ ε v := by positivity
      nlinarith
    · have a1 := hK₂ η hη v hv h1 h2 d e
      have a2 := hself d e
      have hNN := mul_nonneg (gevEtaNorm_nonneg d) (gevEtaNorm_nonneg e)
      have a3 : 0 ≤ e' * gevEtaNorm d * gevEtaNorm e :=
        mul_nonneg (mul_nonneg he'.le (gevEtaNorm_nonneg d)) (gevEtaNorm_nonneg e)
      have a4 : 0 ≤ K₁ * gevEtaNorm d * gevEtaNorm e * gevEnvM ξ₀ ε v :=
        mul_nonneg (mul_nonneg (mul_nonneg hK₁0 (gevEtaNorm_nonneg d)) (gevEtaNorm_nonneg e)) hE0
      refine (abs_sub _ _).trans ?_
      nlinarith

end Continuity

end ExtremeValueTheory
