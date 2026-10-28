/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.GEVMLEBasis

/-!
# Domination of the GEV Hessian near a moving endpoint

Let `θ₀ = (ξ₀, μ₀, σ₀)`, `ξ₀ ≠ 0`, `σ₀ > 0`, and `u₀(x) = 1 + ξ₀ (x - μ₀)/σ₀`. For every
observation `x` which is *good* for the parameter `θ`, `ρ(θ) (1 + 1/u₀(x)) ≤ c₀`
(`ExtremeValueTheory.gevC₀`), we bound the log-density, the score and the Hessian at `θ` by
envelopes `gevEnv a b u₀(x) = u₀^{-a} + u₀^b` which do not depend on `θ`
(`exists_abs_gevHessT_le`, `exists_abs_gevScoreT_le`, `exists_abs_gevLogDensT_le`):

* `|∇²ℓ(θ, x)| ≤ K (u₀^{-(2 + a_w + 2ε)} + u₀^{b_w + 2ε})`,
* `|∇ℓ(θ, x)| ≤ K (u₀^{-(1 + a_w + ε)} + u₀^{b_w + ε})`,
* `|ℓ(θ, x)| ≤ K (u₀^{-(a_w + ε)} + u₀^{b_w + ε})`,

with `a_w = max(0, 2/ξ₀)`, `b_w = max(0, -2/ξ₀)` (the exponents of `w = u^{-1/ξ}` for
`|ξ - ξ₀| ≤ |ξ₀|/2`) and any `ε > 0`. Under the true law these envelopes are integrable as soon as
`-1 < a ξ₀` and `b ξ₀ < 1` (`ExtremeValueTheory.integrable_gevEnv`); for the Hessian, when
`-1/2 < ξ₀ < 0`, this is `(2 + 2ε) |ξ₀| < 1`, which is where `ξ₀ > -1/2` enters.

The proof writes each quantity in the basis of `ExtremeValueTheory.Statistics.GEVMLEBasis`,
bounds the coefficients (continuous in `(ξ, σ)`) on a compact box, and bounds the monomials using
`u₀/3 ≤ u ≤ 3 u₀` (`ExtremeValueTheory.gevU_comparable`).

## References

* R. L. Smith, *Maximum likelihood estimation in a class of nonregular cases*, Biometrika 72
  (1985).
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

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
    · rw [hA, e1]; have : 0 < 1 / -ξ := by positivity
      linarith
    · refine le_trans ?_ (le_max_right _ _)
      have e2 : -2 / ξ₀ = 2 / -ξ₀ := by rw [div_neg, neg_div]
      rw [e1, e2, div_le_div_iff₀ hξn (by linarith)]
      linarith
  · rw [abs_of_pos h] at hξ
    have hξp : 0 < ξ := by linarith
    constructor
    · refine le_trans (neg_le_neg (max_le (by positivity) le_rfl)) ?_
      · exact le_of_eq rfl |>.trans' ?_
      rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ hξp h]
      linarith
    · refine le_trans ?_ (le_max_left _ _)
      have : 0 < 1 / ξ := by positivity
      rw [neg_div]; linarith

end Exponents

/-! ### The weights at good observations -/

section Weights

variable {ξ₀ μ₀ σ₀ ξ μ σ x ε : ℝ}

/-- **The basic weights at a good observation**: `u > 0`, `1 + 1/u ≤ 4 E(1, 0)`,
`1 + w ≤ (1 + 3^{a_w + b_w}) E(a_w, b_w)` and `1 + |log u| ≤ (1 + 3^{2ε}/ε) E(ε, ε)`, where
`E(a, b) = gevEnv a b u₀`. -/
theorem gevWeights_le (hξ₀ : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) (hu₀ : 0 < gevU ξ₀ μ₀ σ₀ x)
    (hgood : gevDist (ξ₀, μ₀, σ₀) (ξ, μ, σ) * (1 + (gevU ξ₀ μ₀ σ₀ x)⁻¹) ≤ gevC₀ ξ₀ σ₀)
    (hε : 0 < ε) :
    0 < gevU ξ μ σ x ∧
      1 + (gevU ξ μ σ x)⁻¹ ≤ 4 * gevEnv 1 0 (gevU ξ₀ μ₀ σ₀ x) ∧
      1 + gevU ξ μ σ x ^ (-1 / ξ) ≤
        (1 + 3 ^ (gevAw ξ₀ + gevBw ξ₀)) * gevEnv (gevAw ξ₀) (gevBw ξ₀) (gevU ξ₀ μ₀ σ₀ x) ∧
      1 + |log (gevU ξ μ σ x)| ≤ (1 + 3 ^ (2 * ε) / ε) * gevEnv ε ε (gevU ξ₀ μ₀ σ₀ x) := by
  obtain ⟨hξ1, -, hlo, hhi⟩ := gevU_comparable hξ₀ hσ₀ (θ := (ξ, μ, σ)) hu₀ hgood
  simp only at hξ1 hlo hhi
  set u₀ := gevU ξ₀ μ₀ σ₀ x
  set u := gevU ξ μ σ x
  have hu : 0 < u := lt_of_lt_of_le (by positivity) hlo
  have hlo' : u₀ / 3 ≤ u := hlo
  have hhi' : u ≤ 3 * u₀ := hhi
  refine ⟨hu, ?_, ?_, ?_⟩
  · have h1 : u⁻¹ ≤ 3 * u₀⁻¹ := by
      rw [inv_le_comm₀ hu (by positivity)]
      calc (3 * u₀⁻¹)⁻¹ = u₀ / 3 := by field_simp
        _ ≤ u := hlo'
    have h2 := inv_le_gevEnv (a := 1) (b := 0) hu₀ le_rfl le_rfl
    have h3 := one_le_gevEnv (a := 1) (b := 0) hu₀ zero_le_one le_rfl
    linarith
  · obtain ⟨r1, r2⟩ := neg_one_div_mem (ξ := ξ) hξ₀ hξ1
    have h1 := rpow_le_gevEnv (a := gevAw ξ₀) (b := gevBw ξ₀) hu r1 r2
    have h2 := gevEnv_le_of_comparable (a := gevAw ξ₀) (b := gevBw ξ₀) hu₀ (by norm_num : (1 : ℝ) ≤ 3)
      hlo' hhi' gevAw_nonneg gevBw_nonneg
    have h3 := one_le_gevEnv (a := gevAw ξ₀) (b := gevBw ξ₀) hu₀ gevAw_nonneg gevBw_nonneg
    nlinarith
  · have h1 := abs_log_le_gevEnv hε hu
    have h2 := gevEnv_le_of_comparable (a := ε) (b := ε) hu₀ (by norm_num : (1 : ℝ) ≤ 3)
      hlo' hhi' hε.le hε.le
    have h3 := one_le_gevEnv (a := ε) (b := ε) hu₀ hε.le hε.le
    have e : ε + ε = 2 * ε := by ring
    rw [e] at h2
    have h4 : gevEnv ε ε u / ε ≤ 3 ^ (2 * ε) / ε * gevEnv ε ε u₀ := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]; exact h2
    nlinarith

end Weights

/-! ### The coefficients on a compact box -/

section Coefficients

variable {ξ₀ σ₀ : ℝ}

/-- The compact box `|ξ - ξ₀| ≤ |ξ₀|/2`, `|σ - σ₀| ≤ σ₀/2` of shapes and scales. -/
def gevParamBox (ξ₀ σ₀ : ℝ) : Set (ℝ × ℝ) :=
  Icc (ξ₀ - |ξ₀| / 2) (ξ₀ + |ξ₀| / 2) ×ˢ Icc (σ₀ / 2) (3 * σ₀ / 2)

lemma isCompact_gevParamBox : IsCompact (gevParamBox ξ₀ σ₀) := isCompact_Icc.prod isCompact_Icc

lemma mem_gevParamBox {ξ σ : ℝ} (hξ : |ξ - ξ₀| ≤ |ξ₀| / 2) (hσ : |σ - σ₀| ≤ σ₀ / 2) :
    (ξ, σ) ∈ gevParamBox ξ₀ σ₀ := by
  rw [abs_le] at hξ hσ
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma ne_zero_of_mem_gevParamBox (hξ₀ : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) {p : ℝ × ℝ}
    (hp : p ∈ gevParamBox ξ₀ σ₀) : p.1 ≠ 0 ∧ 0 < p.2 := by
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := hp
  refine ⟨?_, by linarith⟩
  rcases lt_or_gt_of_ne hξ₀ with h | h
  · rw [abs_of_neg h] at h2; intro h0; rw [h0] at h2; linarith
  · rw [abs_of_pos h] at h1; intro h0; rw [h0] at h1; linarith

lemma continuousAt_gevCoefH (j k : Fin 3) (m : Fin 10) {p : ℝ × ℝ} (h1 : p.1 ≠ 0)
    (h2 : p.2 ≠ 0) : ContinuousAt (fun p : ℝ × ℝ => gevCoefH j k p.1 p.2 m) p := by
  fin_cases j <;> fin_cases k <;> fin_cases m <;> simp [gevCoefH] <;>
    fun_prop (disch := simp [*])

lemma continuousAt_gevCoefS (j : Fin 3) (m : Fin 6) {p : ℝ × ℝ} (h1 : p.1 ≠ 0)
    (h2 : p.2 ≠ 0) : ContinuousAt (fun p : ℝ × ℝ => gevCoefS j p.1 p.2 m) p := by
  fin_cases j <;> fin_cases m <;> simp [gevCoefS] <;> fun_prop (disch := simp [*])

lemma continuousAt_gevCoefL (m : Fin 3) {p : ℝ × ℝ} (h1 : p.1 ≠ 0) (h2 : p.2 ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => gevCoefL p.1 p.2 m) p := by
  fin_cases m <;> simp [gevCoefL] <;> fun_prop (disch := simp [*])

/-- **The coefficients are bounded on the box.** -/
theorem exists_gevCoef_bound (hξ₀ : ξ₀ ≠ 0) (hσ₀ : 0 < σ₀) :
    ∃ C, 0 ≤ C ∧ ∀ p ∈ gevParamBox ξ₀ σ₀,
      (∀ j k, ∑ m, |gevCoefH j k p.1 p.2 m| ≤ C) ∧ (∀ j, ∑ m, |gevCoefS j p.1 p.2 m| ≤ C) ∧
        ∑ m, |gevCoefL p.1 p.2 m| ≤ C := by
  set F : ℝ × ℝ → ℝ := fun p => ∑ j, ∑ k, ∑ m, |gevCoefH j k p.1 p.2 m| +
    ∑ j, ∑ m, |gevCoefS j p.1 p.2 m| + ∑ m, |gevCoefL p.1 p.2 m| with hF
  have hc : ContinuousOn F (gevParamBox ξ₀ σ₀) := by
    intro p hp
    obtain ⟨h1, h2⟩ := ne_zero_of_mem_gevParamBox hξ₀ hσ₀ hp
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hF]
    refine ((continuousAt_finsetSum fun j _ => continuousAt_finsetSum fun k _ =>
      continuousAt_finsetSum fun m _ => (continuousAt_gevCoefH j k m h1 h2.ne').abs).add
      (continuousAt_finsetSum fun j _ => continuousAt_finsetSum fun m _ =>
        (continuousAt_gevCoefS j m h1 h2.ne').abs)).add
      (continuousAt_finsetSum fun m _ => (continuousAt_gevCoefL m h1 h2.ne').abs)
  obtain ⟨C, hC⟩ := isCompact_gevParamBox.exists_bound_of_continuousOn hc
  have hF0 : ∀ p, 0 ≤ F p := fun p => by simp only [hF]; positivity
  have hle : ∀ p ∈ gevParamBox ξ₀ σ₀, F p ≤ C := fun p hp => by
    have := hC p hp; rwa [Real.norm_eq_abs, abs_of_nonneg (hF0 p)] at this
  have hmem : (ξ₀, σ₀) ∈ gevParamBox ξ₀ σ₀ :=
    mem_gevParamBox (by simp; positivity) (by simp; positivity)
  refine ⟨C, (hF0 _).trans (hle _ hmem), fun p hp => ⟨fun j k => ?_, fun j => ?_, ?_⟩⟩
  · have h1 : ∑ m, |gevCoefH j k p.1 p.2 m| ≤ ∑ k, ∑ m, |gevCoefH j k p.1 p.2 m| :=
      Finset.single_le_sum (f := fun k => ∑ m, |gevCoefH j k p.1 p.2 m|)
        (fun _ _ => by positivity) (Finset.mem_univ k)
    have h2 : ∑ k, ∑ m, |gevCoefH j k p.1 p.2 m| ≤ ∑ j, ∑ k, ∑ m, |gevCoefH j k p.1 p.2 m| :=
      Finset.single_le_sum (f := fun j => ∑ k, ∑ m, |gevCoefH j k p.1 p.2 m|)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h3 : 0 ≤ ∑ j, ∑ m, |gevCoefS j p.1 p.2 m| := by positivity
    have h4 : 0 ≤ ∑ m, |gevCoefL p.1 p.2 m| := by positivity
    have := hle p hp
    simp only [hF] at this
    linarith
  · have h1 : ∑ m, |gevCoefS j p.1 p.2 m| ≤ ∑ j, ∑ m, |gevCoefS j p.1 p.2 m| :=
      Finset.single_le_sum (f := fun j => ∑ m, |gevCoefS j p.1 p.2 m|)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h3 : 0 ≤ ∑ j, ∑ k, ∑ m, |gevCoefH j k p.1 p.2 m| := by positivity
    have h4 : 0 ≤ ∑ m, |gevCoefL p.1 p.2 m| := by positivity
    have := hle p hp
    simp only [hF] at this
    linarith
  · have h3 : 0 ≤ ∑ j, ∑ k, ∑ m, |gevCoefH j k p.1 p.2 m| := by positivity
    have h4 : 0 ≤ ∑ j, ∑ m, |gevCoefS j p.1 p.2 m| := by positivity
    have := hle p hp
    simp only [hF] at this
    linarith

end Coefficients

end ExtremeValueTheory
