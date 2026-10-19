/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.LMoments
import ExtremeValueTheory.Statistics.GEVLikelihood

/-!
# Sample probability-weighted moments, sample L-moments and the PWM estimator of the GPD

For observations `x₀, x₁, …` and `n ≥ 1`, let `Rᵢ = #{j < n : xⱼ ≤ xᵢ}` be the rank of `xᵢ`
among the first `n` observations. The **unbiased sample PWMs** of Landwehr, Matalas and Wallis
(1979) (Hosking 1990, (2.4)) are

  `b_r = n⁻¹ ∑_{i<n} xᵢ ∏_{k<r} (Rᵢ - 1 - k)/(n - 1 - k)` (`samplePWM x n r`).

When there are no ties, `Rᵢ = j` for the `j`-th order statistic `x_{j:n}`, and this is
Hosking's `b_r = n⁻¹ ∑_j (j-1)⋯(j-r)/((n-1)⋯(n-r)) x_{j:n}`. The sample L-moments are
`l₁ = b₀`, `l₂ = 2b₁ - b₀`, `l₃ = 6b₂ - 6b₁ + b₀`, `t₃ = l₃/l₂`, and the **PWM estimator of the
generalized Pareto law** (Hosking and Wallis 1987) is `ξ̂ = 2 - l₁/l₂`, `σ̂ = l₁ (l₁/l₂ - 1)`
(`gpdPWMShape`, `gpdPWMScale`; in the `α`-form, `ξ̂ = 2 - a₀/(a₀ - 2a₁)`).

## Main results

* `eventually_abs_empCDF_sub_le_of_grid` (deterministic), `ae_glivenkoCantelli`: the
  **Glivenko–Cantelli theorem** for a continuous distribution function: almost surely
  `sup_t |Fₙ(t) - F(t)| → 0`.
* `abs_samplePWM_sub_le`: the deterministic comparison
  `|b_r - n⁻¹ ∑ xᵢ F(xᵢ)^r| ≤ (n⁻¹ ∑ |xᵢ|)(r²/(n - r) + r sup_t |Fₙ(t) - F(t)|)`.
* `ae_tendsto_samplePWM`: **strong consistency of the sample PWMs**: for iid observations with
  a continuous distribution function and `E|X| < ∞`, `b_r → β_r` almost surely, for every `r`.
* `ae_tendsto_sampleLMoment1/2/3`, `ae_tendsto_sampleLSkewness`: strong consistency of the
  sample L-moments and L-skewness.
* `ae_tendsto_gpdPWMShapeEst`, `ae_tendsto_gpdPWMScaleEst`: **strong consistency of the PWM
  estimator of the GPD** for `ξ < 1` (the range in which the mean, hence `λ₁`, `λ₂`, exist).
* `ae_tendsto_sampleLSkewness_gev`: for GEV data with `ξ < 1`, `ξ ≠ 0`, `t₃ → τ₃(ξ)`.

## Scope

The unbiasedness `E b_r = β_r` of the sample PWMs and their asymptotic normality (for
`ξ < 1/2`) are not formalized here.

## References

* J. M. Landwehr, N. C. Matalas and J. R. Wallis, *Probability weighted moments compared with
  some traditional techniques in estimating Gumbel parameters and quantiles*, Water Resources
  Research 15 (1979).
* J. R. M. Hosking and J. R. Wallis, *Parameter and quantile estimation for the generalized
  Pareto distribution*, Technometrics 29 (1987).
* J. R. M. Hosking, *L-moments*, J. R. Statist. Soc. B 52 (1990).
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

/-! ### Empirical distribution function, ranks and sample PWMs -/

section Deterministic

/-- The number `#{j < n : xⱼ ≤ t}` of the first `n` observations that are at most `t`. -/
noncomputable def countLE (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  ((Finset.range n).filter fun j ↦ x j ≤ t).card

/-- The **empirical distribution function** `Fₙ(t) = #{j < n : xⱼ ≤ t} / n`. -/
noncomputable def empCDF (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ := (countLE x n t : ℝ) / n

/-- The weight `∏_{k<r} (R - 1 - k)/(n - 1 - k)` of an observation of rank `R` in `b_r`. -/
noncomputable def pwmWeight (n r R : ℕ) : ℝ :=
  ∏ k ∈ Finset.range r, ((R : ℝ) - 1 - k) / ((n : ℝ) - 1 - k)

/-- The **unbiased sample probability-weighted moment** `b_r` of the first `n` observations;
the rank of `xᵢ` is `countLE x n (x i)`. -/
noncomputable def samplePWM (x : ℕ → ℝ) (n r : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i * pwmWeight n r (countLE x n (x i))

/-- The first sample L-moment `l₁ = b₀` (the sample mean). -/
noncomputable def sampleLMoment1 (x : ℕ → ℝ) (n : ℕ) : ℝ := samplePWM x n 0

/-- The second sample L-moment `l₂ = 2 b₁ - b₀`. -/
noncomputable def sampleLMoment2 (x : ℕ → ℝ) (n : ℕ) : ℝ := 2 * samplePWM x n 1 - samplePWM x n 0

/-- The third sample L-moment `l₃ = 6 b₂ - 6 b₁ + b₀`. -/
noncomputable def sampleLMoment3 (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  6 * samplePWM x n 2 - 6 * samplePWM x n 1 + samplePWM x n 0

/-- The sample L-skewness `t₃ = l₃ / l₂`. -/
noncomputable def sampleLSkewness (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  sampleLMoment3 x n / sampleLMoment2 x n

/-- The **PWM estimator of the GPD shape** (Hosking–Wallis 1987): `ξ̂ = 2 - l₁ / l₂`. -/
noncomputable def gpdPWMShapeEst (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  gpdPWMShape (sampleLMoment1 x n) (sampleLMoment2 x n)

/-- The **PWM estimator of the GPD scale** (Hosking–Wallis 1987): `σ̂ = l₁ (l₁ / l₂ - 1)`. -/
noncomputable def gpdPWMScaleEst (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  gpdPWMScale (sampleLMoment1 x n) (sampleLMoment2 x n)

variable {x : ℕ → ℝ} {n : ℕ}

lemma samplePWM_zero (x : ℕ → ℝ) (n : ℕ) :
    samplePWM x n 0 = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i := by
  simp [samplePWM, pwmWeight]

lemma countLE_le (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : countLE x n t ≤ n :=
  (Finset.card_filter_le _ _).trans (Finset.card_range n).le

lemma one_le_countLE {i : ℕ} (hi : i < n) : 1 ≤ countLE x n (x i) :=
  Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, le_rfl⟩⟩

lemma monotone_empCDF (x : ℕ → ℝ) (n : ℕ) : Monotone (empCDF x n) := by
  intro s t hst
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun j hj ↦ by
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.trans hst⟩

lemma empCDF_nonneg (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : 0 ≤ empCDF x n t := by
  unfold empCDF; positivity

lemma empCDF_le_one (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : empCDF x n t ≤ 1 := by
  unfold empCDF
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast countLE_le x n t

/-- `|∏ aₖ - ∏ bₖ| ≤ ∑ |aₖ - bₖ|` for factors in `[-1, 1]`. -/
lemma abs_prod_sub_prod_le (a b : ℕ → ℝ) (r : ℕ) (ha : ∀ k < r, |a k| ≤ 1)
    (hb : ∀ k < r, |b k| ≤ 1) :
    |∏ k ∈ Finset.range r, a k - ∏ k ∈ Finset.range r, b k| ≤
      ∑ k ∈ Finset.range r, |a k - b k| := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ih := ih (fun k hk ↦ ha k (by omega)) (fun k hk ↦ hb k (by omega))
    have hB : |∏ k ∈ Finset.range r, b k| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _)
        (fun k hk ↦ hb k (by simp at hk; omega))
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
    have e : (∏ k ∈ Finset.range r, a k) * a r - (∏ k ∈ Finset.range r, b k) * b r =
        (∏ k ∈ Finset.range r, a k - ∏ k ∈ Finset.range r, b k) * a r +
          (∏ k ∈ Finset.range r, b k) * (a r - b r) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := ha r (by omega)
    have h2 := abs_nonneg (a r - b r)
    have h3 := abs_nonneg (∏ k ∈ Finset.range r, a k - ∏ k ∈ Finset.range r, b k)
    nlinarith

/-- `|aʳ - bʳ| ≤ r |a - b|` on `[0, 1]`. -/
lemma abs_pow_sub_pow_le_of_mem {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (r : ℕ) : |a ^ r - b ^ r| ≤ r * |a - b| := by
  have := abs_prod_sub_prod_le (fun _ ↦ a) (fun _ ↦ b) r
    (fun _ _ ↦ by rw [abs_of_nonneg ha0]; exact ha1) (fun _ _ ↦ by rw [abs_of_nonneg hb0]; exact hb1)
  simpa using this

/-- The unbiased weight is close to `(R/n)^r`: for `2r ≤ n` and `1 ≤ R ≤ n`,
`|∏_{k<r} (R - 1 - k)/(n - 1 - k) - (R/n)^r| ≤ r · r/(n - r)`. -/
lemma abs_pwmWeight_sub_le {r R : ℕ} (h2r : 2 * r ≤ n) (hR1 : 1 ≤ R) (hRn : R ≤ n) :
    |pwmWeight n r R - ((R : ℝ) / n) ^ r| ≤ r * (r / ((n : ℝ) - r)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hR1.trans hRn
  have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hRn' : (R : ℝ) ≤ n := by exact_mod_cast hRn
  have h2r' : 2 * (r : ℝ) ≤ n := by exact_mod_cast h2r
  have hp0 : 0 ≤ (R : ℝ) / n := by positivity
  have hp1 : (R : ℝ) / n ≤ 1 := (div_le_one (by linarith)).2 hRn'
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [pwmWeight]
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnr : 0 < (n : ℝ) - r := by linarith
  have key : ∀ k < r, 0 < (n : ℝ) - 1 - k ∧ (n : ℝ) - r ≤ (n : ℝ) - 1 - k ∧ (k : ℝ) + 1 ≤ r ∧
      2 * (k : ℝ) + 1 ≤ n := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ r := by exact_mod_cast hk
    refine ⟨by linarith, by linarith, hk', by linarith⟩
  have hpow : ((R : ℝ) / n) ^ r = ∏ k ∈ Finset.range r, ((R : ℝ) / n) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [pwmWeight, hpow]
  refine (abs_prod_sub_prod_le _ _ r (fun k hk ↦ ?_) (fun _ _ ↦ by
    rw [abs_of_nonneg hp0]; exact hp1)).trans ?_
  · obtain ⟨hd, -, -, h2k⟩ := key k hk
    rw [abs_div, abs_of_pos hd, div_le_one hd, abs_le]
    constructor <;> linarith
  · have hle : ∀ k ∈ Finset.range r,
        |((R : ℝ) - 1 - k) / ((n : ℝ) - 1 - k) - (R : ℝ) / n| ≤ r / ((n : ℝ) - r) := by
      intro k hk
      obtain ⟨hd, hdr, hk1, -⟩ := key k (Finset.mem_range.1 hk)
      have hn0 : (0 : ℝ) < n := by linarith
      have e : ((R : ℝ) - 1 - k) / ((n : ℝ) - 1 - k) - (R : ℝ) / n =
          -(((k : ℝ) + 1) * ((n : ℝ) - R)) / (n * ((n : ℝ) - 1 - k)) := by
        field_simp; ring
      rw [e, abs_div, abs_neg, abs_of_nonneg (by nlinarith), abs_of_pos (by positivity),
        div_le_div_iff₀ (by positivity) hnr]
      have h1 : ((k : ℝ) + 1) * ((n : ℝ) - R) ≤ r * n := by nlinarith
      have h2 : ((k : ℝ) + 1) * ((n : ℝ) - R) * ((n : ℝ) - r) ≤ r * n * ((n : ℝ) - r) :=
        mul_le_mul_of_nonneg_right h1 hnr.le
      have h3 : (r : ℝ) * n * ((n : ℝ) - r) ≤ r * n * ((n : ℝ) - 1 - k) :=
        mul_le_mul_of_nonneg_left hdr (by positivity)
      nlinarith
    refine (Finset.sum_le_sum hle).trans ?_
    simp

/-- **Deterministic comparison of `b_r` with the oracle average** `n⁻¹ ∑ xᵢ F(xᵢ)^r`: if
`|Fₙ - F| ≤ D` everywhere and `2r ≤ n`, then
`|b_r - n⁻¹ ∑ xᵢ F(xᵢ)^r| ≤ (n⁻¹ ∑ |xᵢ|)(r · r/(n - r) + r D)`. -/
theorem abs_samplePWM_sub_le {F : ℝ → ℝ} (hF0 : ∀ t, 0 ≤ F t) (hF1 : ∀ t, F t ≤ 1) {r : ℕ}
    (h2r : 2 * r ≤ n) {D : ℝ} (hD : ∀ t, |empCDF x n t - F t| ≤ D) :
    |samplePWM x n r - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, x i * F (x i) ^ r| ≤
      ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |x i|) * (r * (r / ((n : ℝ) - r)) + r * D) := by
  have hw : ∀ i ∈ Finset.range n, |pwmWeight n r (countLE x n (x i)) - F (x i) ^ r| ≤
      r * (r / ((n : ℝ) - r)) + r * D := by
    intro i hi
    have hi := Finset.mem_range.1 hi
    have h1 := abs_pwmWeight_sub_le h2r (one_le_countLE (x := x) hi) (countLE_le x n (x i))
    have h2 := abs_pow_sub_pow_le_of_mem (empCDF_nonneg x n (x i)) (empCDF_le_one x n (x i))
      (hF0 (x i)) (hF1 (x i)) r
    have h3 := mul_le_mul_of_nonneg_left (hD (x i)) (Nat.cast_nonneg r)
    calc _ ≤ |pwmWeight n r (countLE x n (x i)) - ((countLE x n (x i) : ℝ) / n) ^ r| +
          |((countLE x n (x i) : ℝ) / n) ^ r - F (x i) ^ r| := abs_sub_le _ _ _
      _ ≤ _ := by unfold empCDF at h2 h3; linarith
  rw [samplePWM, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (hw i hi) (abs_nonneg _)

/-- **Deterministic core of the Glivenko–Cantelli theorem.** Let `F` be a distribution
function, `p k j` a point with `F (p k j) = j/k` for `0 < j < k`, and `Gₙ` monotone with values
in `[0, 1]`, converging to `F` at every `p k j`. Then `Gₙ → F` uniformly. -/
theorem eventually_abs_sub_le_of_grid {F : ℝ → ℝ} (hFm : Monotone F) (hF0 : ∀ t, 0 ≤ F t)
    (hF1 : ∀ t, F t ≤ 1) {G : ℕ → ℝ → ℝ} (hGm : ∀ n, Monotone (G n))
    (hG0 : ∀ n t, 0 ≤ G n t) (hG1 : ∀ n t, G n t ≤ 1) (p : ℕ → ℕ → ℝ)
    (hp : ∀ k j : ℕ, 0 < j → j < k → F (p k j) = j / k)
    (hconv : ∀ k j, Tendsto (fun n ↦ G n (p k j)) atTop (𝓝 (F (p k j)))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t, |G n t - F t| ≤ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
  have hk1 : 1 / (k : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hk0]; rw [div_lt_iff₀ hε] at hk; linarith
  have hev : ∀ᶠ n in atTop, ∀ j ∈ Finset.range k, |G n (p k j) - F (p k j)| < ε / 2 :=
    (Filter.eventually_all_finset _).2 fun j _ ↦ by
      simpa [Real.dist_eq] using (Metric.tendsto_nhds.1 (hconv k j)) (ε / 2) (half_pos hε)
  filter_upwards [hev] with n hn t
  set y := (k : ℝ) * F t with hy
  have hFt : F t = y / k := by rw [hy]; field_simp
  have hy0 : 0 ≤ y := mul_nonneg hk0.le (hF0 t)
  have hyk : y ≤ k := by rw [hy]; nlinarith [hF1 t]
  have hdiv : ∀ a b : ℝ, a ≤ b → a / k ≤ b / k := fun a b h ↦
    div_le_div_of_nonneg_right h hk0.le
  rw [abs_le]
  constructor
  · -- lower bound
    by_cases hy1 : y ≤ 1
    · have : F t ≤ 1 / k := by rw [hFt]; exact hdiv _ _ hy1
      linarith [hG0 n t]
    · push Not at hy1
      have hc1 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
      have hc2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
      have hc3 : ⌈y⌉₊ ≤ k := Nat.ceil_le.2 hyk
      have hc4 : 2 ≤ ⌈y⌉₊ := by
        have : (1 : ℝ) < ⌈y⌉₊ := lt_of_lt_of_le hy1 hc1
        exact_mod_cast this
      set j := ⌈y⌉₊ - 1 with hj
      have hjr : (j : ℝ) = ⌈y⌉₊ - 1 := by rw [hj, Nat.cast_sub (by omega)]; simp
      have hj0 : 0 < j := by omega
      have hjk : j < k := by omega
      have hpj := hp k j hj0 hjk
      have hlt : F (p k j) < F t := by
        rw [hpj, hFt]; exact div_lt_div_of_pos_right (by linarith) hk0
      have hpt : p k j ≤ t := le_of_lt (lt_of_not_ge fun h ↦ (hFm h).not_gt hlt)
      have h1 := hGm n hpt
      have h2 := (abs_lt.1 (hn j (Finset.mem_range.2 hjk))).1
      have h3 : (y - 1) / k ≤ (j : ℝ) / k := hdiv _ _ (by linarith)
      have h4 : (y - 1) / k = F t - 1 / k := by rw [hFt]; ring
      linarith
  · -- upper bound
    set j := ⌊y⌋₊ + 1 with hj
    have hf1 : y < (j : ℝ) := by rw [hj]; push_cast; exact Nat.lt_floor_add_one y
    have hf2 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
    by_cases hjk : j < k
    · have hpj := hp k j (by omega) hjk
      have hlt : F t < F (p k j) := by
        rw [hpj, hFt]; exact div_lt_div_of_pos_right hf1 hk0
      have htp : t ≤ p k j := le_of_lt (lt_of_not_ge fun h ↦ (hFm h).not_gt hlt)
      have h1 := hGm n htp
      have h2 := (abs_lt.1 (hn j (Finset.mem_range.2 hjk))).2
      have h3 : (j : ℝ) / k ≤ (y + 1) / k := hdiv _ _ (by rw [hj]; push_cast; linarith)
      have h4 : (y + 1) / k = F t + 1 / k := by rw [hFt]; ring
      rw [hpj] at h2
      linarith
    · push Not at hjk
      have : (k : ℝ) ≤ ⌊y⌋₊ + 1 := by exact_mod_cast hjk
      have h4 : (k - 1 : ℝ) / k ≤ F t := by rw [hFt]; exact hdiv _ _ (by linarith)
      have h5 : (k - 1 : ℝ) / k = 1 - 1 / k := by field_simp
      linarith [hG1 n t]

end Deterministic

/-! ### Strong consistency -/

section Consistency

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {μ : Measure ℝ}
  [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}

/-- The empirical distribution function at a fixed point converges almost surely. -/
theorem ae_tendsto_empCDF (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P) (t : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ empCDF (fun i ↦ X i ω) n t) atTop (𝓝 (cdf μ t)) := by
  have hg : Measurable ((Iic t).indicator fun _ : ℝ ↦ (1 : ℝ)) :=
    measurable_const.indicator measurableSet_Iic
  have hgi : Integrable ((Iic t).indicator fun _ : ℝ ↦ (1 : ℝ)) μ :=
    (integrable_const 1).indicator measurableSet_Iic
  filter_upwards [ae_tendsto_avg_comp hX hind hg hgi] with ω hω
  rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one, ← cdf_eq_real] at hω
  refine hω.congr fun n ↦ ?_
  simp only [Set.indicator_apply, mem_Iic, empCDF, countLE]
  rw [Finset.sum_boole, div_eq_inv_mul]

/-- **Glivenko–Cantelli theorem** for a continuous distribution function: almost surely,
`sup_t |Fₙ(t) - F(t)| → 0`. -/
theorem ae_glivenkoCantelli (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (hcont : Continuous (cdf μ)) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop, ∀ t, |empCDF (fun i ↦ X i ω) n t - cdf μ t| ≤ ε := by
  have hex : ∀ k j : ℕ, 0 < j → j < k → ∃ t, cdf μ t = (j : ℝ) / k := by
    intro k j hj hjk
    have hk : (0 : ℝ) < k := by exact_mod_cast hj.trans hjk
    have hq0 : (0 : ℝ) < (j : ℝ) / k := by
      have : (0 : ℝ) < j := by exact_mod_cast hj
      positivity
    have hq1 : (j : ℝ) / k < 1 := (div_lt_one hk).2 (by exact_mod_cast hjk)
    obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds hq0)).exists
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hq1)).exists
    obtain ⟨t, ht⟩ := mem_range_of_exists_le_of_exists_ge hcont ⟨a, ha.le⟩ ⟨b, hb.le⟩
    exact ⟨t, ht⟩
  classical
  let p : ℕ → ℕ → ℝ := fun k j ↦
    if h : 0 < j ∧ j < k then (hex k j h.1 h.2).choose else 0
  have hp : ∀ k j : ℕ, 0 < j → j < k → cdf μ (p k j) = (j : ℝ) / k := by
    intro k j hj hjk
    simp only [p, hj, hjk, and_self, ↓reduceDIte]
    exact (hex k j hj hjk).choose_spec
  have hall : ∀ᵐ ω ∂P, ∀ k j, Tendsto (fun n ↦ empCDF (fun i ↦ X i ω) n (p k j)) atTop
      (𝓝 (cdf μ (p k j))) :=
    ae_all_iff.2 fun k ↦ ae_all_iff.2 fun j ↦ ae_tendsto_empCDF hX hind (p k j)
  filter_upwards [hall] with ω hω ε hε
  exact eventually_abs_sub_le_of_grid (cdf μ).mono (cdf_nonneg μ) (cdf_le_one μ)
    (fun n ↦ monotone_empCDF _ n) (fun n t ↦ empCDF_nonneg _ n t) (fun n t ↦ empCDF_le_one _ n t)
    p hp hω hε

private lemma tendsto_r_div_sub (r : ℕ) :
    Tendsto (fun n : ℕ ↦ (r : ℝ) * (r / ((n : ℝ) - r))) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ) + -(r : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have := (tendsto_const_nhds (x := (r : ℝ))).div_atTop h
  simpa [sub_eq_add_neg] using this.const_mul (r : ℝ)

/-- **Strong consistency of the sample PWMs.** For iid observations with a continuous
distribution function `F` and `E|X| < ∞`, `b_r → β_r = E[X F(X)^r]` almost surely. -/
theorem ae_tendsto_samplePWM (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (hcont : Continuous (cdf μ)) (hint : Integrable (fun x ↦ x) μ) (r : ℕ) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ samplePWM (fun i ↦ X i ω) n r) atTop (𝓝 (pwm μ r)) := by
  have hmeas : Measurable fun x ↦ x * cdf μ x ^ r :=
    measurable_id.mul ((measurable_cdf_apply μ).pow_const r)
  filter_upwards [ae_glivenkoCantelli hX hind hcont,
    ae_tendsto_avg_comp hX hind measurable_id.abs hint.abs,
    ae_tendsto_avg_comp hX hind hmeas (integrable_mul_cdf_pow hint r)] with ω hGC hS1 hS2
  set M := ∫ y, |y| ∂μ + 1
  have hM : 0 < M := by positivity
  have hdiff : Tendsto (fun n ↦ samplePWM (fun i ↦ X i ω) n r -
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω * cdf μ (X i ω) ^ r) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set ε := δ / (2 * M * (r + 1)) with hεdef
    have hε : 0 < ε := by positivity
    filter_upwards [hGC ε hε, hS1.eventually (eventually_le_nhds (lt_add_one _)),
      (tendsto_r_div_sub r).eventually (eventually_le_nhds hε), eventually_ge_atTop (2 * r)]
      with n hn hA hR h2r
    rw [Real.dist_eq, sub_zero]
    have hb := abs_samplePWM_sub_le (x := fun i ↦ X i ω) (cdf_nonneg μ) (cdf_le_one μ) h2r hn
    have hA0 : 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |X i ω| := by positivity
    have hR0 : 0 ≤ (r : ℝ) * (r / ((n : ℝ) - r)) := by
      have : (2 * r : ℝ) ≤ n := by exact_mod_cast h2r
      have : (0 : ℝ) ≤ (n : ℝ) - r := by have := Nat.cast_nonneg (α := ℝ) r; linarith
      positivity
    have hle : ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, |X i ω|) *
        ((r : ℝ) * (r / ((n : ℝ) - r)) + r * ε) ≤ M * (ε + r * ε) :=
      mul_le_mul hA (by linarith) (by positivity) hM.le
    have hval : M * (ε + r * ε) = δ / 2 := by
      rw [hεdef]; field_simp; ring
    linarith
  have := hdiff.add hS2
  rw [zero_add] at this
  exact this.congr fun n ↦ by ring

/-- Strong consistency of the first sample L-moment. -/
theorem ae_tendsto_sampleLMoment1 (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (hcont : Continuous (cdf μ)) (hint : Integrable (fun x ↦ x) μ) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ sampleLMoment1 (fun i ↦ X i ω) n) atTop (𝓝 (lMoment1 μ)) :=
  ae_tendsto_samplePWM hX hind hcont hint 0

/-- Strong consistency of the second sample L-moment. -/
theorem ae_tendsto_sampleLMoment2 (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (hcont : Continuous (cdf μ)) (hint : Integrable (fun x ↦ x) μ) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ sampleLMoment2 (fun i ↦ X i ω) n) atTop (𝓝 (lMoment2 μ)) := by
  filter_upwards [ae_tendsto_samplePWM hX hind hcont hint 0,
    ae_tendsto_samplePWM hX hind hcont hint 1] with ω h0 h1
  exact (h1.const_mul 2).sub h0

/-- Strong consistency of the third sample L-moment. -/
theorem ae_tendsto_sampleLMoment3 (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (hcont : Continuous (cdf μ)) (hint : Integrable (fun x ↦ x) μ) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ sampleLMoment3 (fun i ↦ X i ω) n) atTop (𝓝 (lMoment3 μ)) := by
  filter_upwards [ae_tendsto_samplePWM hX hind hcont hint 0,
    ae_tendsto_samplePWM hX hind hcont hint 1, ae_tendsto_samplePWM hX hind hcont hint 2]
    with ω h0 h1 h2
  exact ((h2.const_mul 6).sub (h1.const_mul 6)).add h0

/-- Strong consistency of the sample L-skewness (when `λ₂ ≠ 0`). -/
theorem ae_tendsto_sampleLSkewness (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (hcont : Continuous (cdf μ)) (hint : Integrable (fun x ↦ x) μ) (h2 : lMoment2 μ ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ sampleLSkewness (fun i ↦ X i ω) n) atTop (𝓝 (lSkewness μ)) := by
  filter_upwards [ae_tendsto_sampleLMoment2 hX hind hcont hint,
    ae_tendsto_sampleLMoment3 hX hind hcont hint] with ω h2' h3
  exact h3.div h2' h2

/-! ### The PWM estimator of the generalized Pareto law -/

variable {ξ σ : ℝ}

lemma continuous_cdf_gpdMeasure (hσ : 0 < σ) : Continuous (cdf (gpdMeasure ξ σ)) :=
  (continuous_gpdCDF hσ).congr fun x ↦ (cdf_gpdMeasure hσ x).symm

lemma lMoment2_gpdMeasure_pos (hσ : 0 < σ) (hξ : ξ < 1) : 0 < lMoment2 (gpdMeasure ξ σ) := by
  rw [lMoment2_gpdMeasure hσ hξ]
  have h1 : 0 < 1 - ξ := by linarith
  have h2 : 0 < 2 - ξ := by linarith
  positivity

/-- **Strong consistency of the PWM estimator of the GPD shape** (Hosking and Wallis 1987):
for iid `GPD(ξ, σ)` observations with `ξ < 1`, `ξ̂ₙ = 2 - l₁/l₂ → ξ` almost surely. -/
theorem ae_tendsto_gpdPWMShapeEst (hσ : 0 < σ) (hξ : ξ < 1)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ) P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ gpdPWMShapeEst (fun i ↦ X i ω) n) atTop (𝓝 ξ) := by
  have hc := continuous_cdf_gpdMeasure (ξ := ξ) hσ
  have hi := integrable_id_gpdMeasure hσ hξ
  filter_upwards [ae_tendsto_sampleLMoment1 hX hind hc hi,
    ae_tendsto_sampleLMoment2 hX hind hc hi] with ω h1 h2
  have := tendsto_const_nhds (x := (2 : ℝ)) |>.sub (h1.div h2 (lMoment2_gpdMeasure_pos hσ hξ).ne')
  rw [← gpdPWMShape_lMoment hσ hξ]
  exact this

/-- **Strong consistency of the PWM estimator of the GPD scale**: for iid `GPD(ξ, σ)`
observations with `ξ < 1`, `σ̂ₙ = l₁ (l₁/l₂ - 1) → σ` almost surely. -/
theorem ae_tendsto_gpdPWMScaleEst (hσ : 0 < σ) (hξ : ξ < 1)
    (hX : ∀ i, HasLaw (X i) (gpdMeasure ξ σ) P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ gpdPWMScaleEst (fun i ↦ X i ω) n) atTop (𝓝 σ) := by
  have hc := continuous_cdf_gpdMeasure (ξ := ξ) hσ
  have hi := integrable_id_gpdMeasure hσ hξ
  filter_upwards [ae_tendsto_sampleLMoment1 hX hind hc hi,
    ae_tendsto_sampleLMoment2 hX hind hc hi] with ω h1 h2
  have := h1.mul ((h1.div h2 (lMoment2_gpdMeasure_pos hσ hξ).ne').sub tendsto_const_nhds
    (b := (1 : ℝ)))
  rw [← gpdPWMScale_lMoment hσ hξ]
  exact this

/-- **Consistency of the sample L-skewness for GEV data**: for iid `H_ξ` observations with
`ξ < 1`, `ξ ≠ 0`, `t₃ → (2·3^ξ - 3·2^ξ + 1)/(2^ξ - 1)` almost surely. -/
theorem ae_tendsto_sampleLSkewness_gev (hξ : ξ < 1) (h0 : ξ ≠ 0)
    (hX : ∀ i, HasLaw (X i) (gevCDF ξ).measure P) (hind : iIndepFun X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ sampleLSkewness (fun i ↦ X i ω) n) atTop
      (𝓝 ((2 * 3 ^ ξ - 3 * 2 ^ ξ + 1) / (2 ^ ξ - 1))) := by
  have hc : Continuous (cdf (gevCDF ξ).measure) :=
    (continuous_gevFun ξ).congr fun x ↦ (cdf_gevCDF_measure ξ x).symm
  have h2 : lMoment2 (gevCDF ξ).measure ≠ 0 := by
    rw [lMoment2_gevCDF hξ h0]
    exact div_ne_zero (mul_ne_zero (two_rpow_sub_one_ne_zero h0)
      (Gamma_pos_of_pos (by linarith)).ne') h0
  rw [← lSkewness_gevCDF hξ h0]
  exact ae_tendsto_sampleLSkewness hX hind hc (integrable_id_gevCDF hξ) h2

end Consistency

end ExtremeValueTheory
