/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.Examples

/-!
# The block maxima method

Split an iid sample `X_0, X_1, …` into consecutive blocks of size `n` and record the block
maxima `M_{n,j} = max_{jn ≤ i < (j+1)n} X_i`, `j = 0, 1, …` ([EKM, §6.4.1]; [Coles, §3.3];
[dHF, §1.1.3]). The block maxima are iid with distribution function `F ^ n`, so when `F` is in
the domain of attraction of an extreme value law `H` with norming constants `a_n > 0`, `b_n`,

* the normalized block maxima `(M_{n,j} - b_n) / a_n` converge in law to `H`
  (`tendsto_measureReal_normalized_blockMax_le`), and
* the empirical distribution function of the first `m` normalized block maxima,
  `Ĥ_{m,n}(x) = #{j < m | (M_{n,j} - b_n) / a_n ≤ x} / m`, converges in probability to `H(x)`
  as `m, n → ∞` jointly (`tendstoInMeasure_blockMaxEmpCDF`).

The second statement is the consistency of the block maxima method with known norming
constants. The proof is Chebyshev's inequality: the indicators `1{M_{n,j} ≤ a_n x + b_n}` over
disjoint blocks are independent Bernoulli variables with success probability
`F(a_n x + b_n) ^ n`, so `Ĥ_{m,n}(x)` has that mean and variance at most `1 / (4m)`.

## Main definitions and results

* `ExtremeValueTheory.blockMax X n j`: the maximum of the `j`-th block of size `n`.
* `ExtremeValueTheory.blockMaxEmpCDF X a b m n x`: the empirical c.d.f. `Ĥ_{m,n}(x)`.
* `measureReal_blockMax_le`: `P(M_{n,j} ≤ u) = F(u) ^ n`.
* `measureReal_abs_blockMaxEmpCDF_sub_ge_le`: the Chebyshev bound
  `P(|Ĥ_{m,n}(x) - F(a_n x + b_n) ^ n| ≥ ε) ≤ 1 / (4 m ε²)`.
* `tendsto_measureReal_normalized_blockMax_le`, `tendstoInMeasure_blockMaxEmpCDF`.

## References

* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  §6.4.1 [EKM].
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  §3.3 [Coles].
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  §1.1 [dHF].
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace ExtremeValueTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- The maximum `M_{n,j} = max_{i < n} X_{jn + i}` of the `j`-th block of size `n`
(set to `0` for the degenerate block size `n = 0`). -/
noncomputable def blockMax (X : ℕ → Ω → ℝ) (n j : ℕ) (ω : Ω) : ℝ :=
  if h : 0 < n then (range n).sup' (nonempty_range_iff.2 h.ne') (fun i ↦ X (j * n + i) ω)
  else 0

/-- The empirical distribution function `Ĥ_{m,n}(x)` of the first `m` normalized block maxima
`(M_{n,j} - b_n) / a_n`, `j < m`. -/
noncomputable def blockMaxEmpCDF (X : ℕ → Ω → ℝ) (a b : ℕ → ℝ) (m n : ℕ) (x : ℝ) (ω : Ω) : ℝ :=
  (∑ j ∈ range m, if (blockMax X n j ω - b n) / a n ≤ x then (1 : ℝ) else 0) / m

/-- The index set `{jn, …, jn + n - 1}` of the `j`-th block. -/
private abbrev block (n j : ℕ) : Finset ℕ := Ico (j * n) (j * n + n)

private lemma card_block (n j : ℕ) : #(block n j) = n := by simp

private lemma disjoint_block {n j k : ℕ} (hjk : j ≠ k) : Disjoint (block n j) (block n k) := by
  rw [Finset.disjoint_left]
  intro t ht ht'
  simp only [mem_Ico] at ht ht'
  rcases lt_or_gt_of_ne hjk with h | h
  · have : (j + 1) * n ≤ k * n := Nat.mul_le_mul_right n h
    rw [add_mul, one_mul] at this
    omega
  · have : (k + 1) * n ≤ j * n := Nat.mul_le_mul_right n h
    rw [add_mul, one_mul] at this
    omega

lemma blockMax_le_iff {n : ℕ} (hn : 0 < n) (j : ℕ) (ω : Ω) (u : ℝ) :
    blockMax X n j ω ≤ u ↔ ∀ i < n, X (j * n + i) ω ≤ u := by
  simp [blockMax, hn, Finset.sup'_le_iff]

private lemma setOf_blockMax_le {n : ℕ} (hn : 0 < n) (j : ℕ) (u : ℝ) :
    {ω | blockMax X n j ω ≤ u} = maxLE X (block n j) u := by
  ext ω
  simp only [Set.mem_ofPred_eq, blockMax_le_iff hn, maxLE, mem_Ico]
  constructor
  · intro h t ht
    have := h (t - j * n) (by omega)
    rwa [Nat.add_sub_cancel' ht.1] at this
  · intro h i hi
    exact h _ ⟨by omega, by omega⟩

omit [IsProbabilityMeasure P] in
/-- The block maxima of an iid sample have distribution function `F ^ n`. -/
theorem measureReal_blockMax_le (hind : iIndepFun X P)
    (hid : ∀ t, IdentDistrib (X t) (X 0) P P) {n : ℕ} (hn : 0 < n) (j : ℕ) (u : ℝ) :
    P.real {ω | blockMax X n j ω ≤ u} = P.real {ω | X 0 ω ≤ u} ^ n := by
  rw [setOf_blockMax_le hn, measureReal_maxLE_of_iIndepFun hind hid, card_block]

omit [IsProbabilityMeasure P] in
/-- **Block maxima converge in law**: if `F ^ n (a_n x + b_n) → H(x)`, then for every block
index `j`, `P((M_{n,j} - b_n) / a_n ≤ x) → H(x)`. -/
theorem tendsto_measureReal_normalized_blockMax_le (hind : iIndepFun X P)
    (hid : ∀ t, IdentDistrib (X t) (X 0) P P) {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) {x Hx : ℝ}
    (hMDA : Tendsto (fun n ↦ P.real {ω | X 0 ω ≤ a n * x + b n} ^ n) atTop (𝓝 Hx)) (j : ℕ) :
    Tendsto (fun n ↦ P.real {ω | (blockMax X n j ω - b n) / a n ≤ x}) atTop (𝓝 Hx) := by
  refine hMDA.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : {ω | (blockMax X n j ω - b n) / a n ≤ x} = {ω | blockMax X n j ω ≤ a n * x + b n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, div_le_iff₀ (ha n)]
    constructor <;> intro h <;> linarith
  rw [this, measureReal_blockMax_le hind hid hn]

/-- **Chebyshev bound for the block maxima empirical c.d.f.**: with `p = F(a_n x + b_n) ^ n`,
`P(|Ĥ_{m,n}(x) - p| ≥ ε) ≤ 1 / (4 m ε²)`. -/
theorem measureReal_abs_blockMaxEmpCDF_sub_ge_le (hX : ∀ t, Measurable (X t))
    (hind : iIndepFun X P) (hid : ∀ t, IdentDistrib (X t) (X 0) P P) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) (x : ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |blockMaxEmpCDF X a b m n x ω -
      P.real {ω | X 0 ω ≤ a n * x + b n} ^ n|} ≤ 1 / (4 * m * ε ^ 2) := by
  set u := a n * x + b n with hu
  set p := P.real {ω | X 0 ω ≤ u} ^ n with hp
  set I : ℕ → Ω → ℝ := fun j ↦ (maxLE X (block n j) u).indicator 1 with hI
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  -- The empirical c.d.f. is the average of the block indicators.
  have hG : (fun ω ↦ blockMaxEmpCDF X a b m n x ω) = fun ω ↦ (m : ℝ)⁻¹ * ∑ j ∈ range m, I j ω := by
    funext ω
    rw [blockMaxEmpCDF, div_eq_inv_mul]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    have hiff : (blockMax X n j ω - b n) / a n ≤ x ↔ ω ∈ maxLE X (block n j) u := by
      rw [← setOf_blockMax_le hn, Set.mem_ofPred_eq, div_le_iff₀ (ha n)]
      constructor <;> intro h <;> linarith
    by_cases h : ω ∈ maxLE X (block n j) u
    · simp [hI, h, hiff.2 h]
    · simp [hI, h, mt hiff.1 h]
  have hmeas : ∀ j, Measurable (I j) := fun j ↦
    measurable_const.indicator (measurableSet_maxLE hX _ _)
  have hbound : ∀ j ω, I j ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro j ω
    by_cases h : ω ∈ maxLE X (block n j) u <;> simp [hI, h]
  have hL2 : ∀ j, MemLp (I j) 2 P := fun j ↦
    MemLp.of_bound (hmeas j).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ by
      have := hbound j ω
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2])
  have hmean : ∀ j, ∫ ω, I j ω ∂P = p := by
    intro j
    rw [integral_indicator_one (measurableSet_maxLE hX _ _),
      measureReal_maxLE_of_iIndepFun hind hid, card_block]
  have hvar : ∀ j, variance (I j) P ≤ 1 / 4 := by
    intro j
    have := variance_le_sq_of_bounded (μ := P) (ae_of_all _ (hbound j)) (hmeas j).aemeasurable
    norm_num at this
    linarith
  -- Indicators of disjoint blocks are independent.
  have hindep : Set.Pairwise ↑(range m) fun j k ↦ I j ⟂ᵢ[P] I k := by
    intro j _ k _ hjk
    have h := hind.indepFun_finset (block n j) (block n k) (disjoint_block hjk) hX
    have hg : ∀ S : Finset ℕ, Measurable
        ((⋂ i : S, (fun v : S → ℝ ↦ v i) ⁻¹' Set.Iic u).indicator (1 : (S → ℝ) → ℝ)) :=
      fun S ↦ measurable_const.indicator
        (MeasurableSet.iInter fun i ↦ measurableSet_Iic.preimage (measurable_pi_apply i))
    have hcomp : ∀ S : Finset ℕ, (maxLE X S u).indicator (1 : Ω → ℝ) =
        ((⋂ i : S, (fun v : S → ℝ ↦ v i) ⁻¹' Set.Iic u).indicator (1 : (S → ℝ) → ℝ)) ∘
          (fun ω (i : S) ↦ X i ω) := by
      intro S
      funext ω
      have hiff : ω ∈ maxLE X S u ↔
          (fun i : S ↦ X i ω) ∈ ⋂ i : S, (fun v : S → ℝ ↦ v i) ⁻¹' Set.Iic u := by
        simp [maxLE]
      by_cases h : ω ∈ maxLE X S u
      · simp only [Function.comp_apply, Set.indicator_of_mem h, Set.indicator_of_mem (hiff.1 h),
          Pi.one_apply]
      · simp only [Function.comp_apply, Set.indicator_of_notMem h,
          Set.indicator_of_notMem (mt hiff.2 h)]
    simp only [hI]
    rw [hcomp, hcomp]
    exact h.comp (hg _) (hg _)
  have hsumL2 : MemLp (∑ j ∈ range m, I j) 2 P := memLp_finsetSum' _ fun j _ ↦ hL2 j
  have hvarsum : variance (∑ j ∈ range m, I j) P ≤ m / 4 := by
    rw [IndepFun.variance_sum (fun j _ ↦ hL2 j) hindep]
    calc ∑ j ∈ range m, variance (I j) P ≤ ∑ _j ∈ range m, (1 / 4 : ℝ) :=
          sum_le_sum fun j _ ↦ hvar j
      _ = m / 4 := by simp; ring
  have hsum_eq : (fun ω ↦ ∑ j ∈ range m, I j ω) = ∑ j ∈ range m, I j := by
    funext ω; simp
  have hGL2 : MemLp (fun ω ↦ blockMaxEmpCDF X a b m n x ω) 2 P := by
    have e : (fun ω ↦ (m : ℝ)⁻¹ * ∑ j ∈ range m, I j ω) =
        fun ω ↦ (m : ℝ)⁻¹ * (∑ j ∈ range m, I j) ω := by
      funext ω; simp [Finset.sum_apply]
    rw [hG, e]; exact hsumL2.const_mul _
  have hGmean : ∫ ω, blockMaxEmpCDF X a b m n x ω ∂P = p := by
    rw [show (fun ω ↦ blockMaxEmpCDF X a b m n x ω) = _ from hG, integral_const_mul,
      integral_finsetSum _ fun j _ ↦ (hL2 j).integrable one_le_two]
    simp only [hmean, sum_const, card_range, nsmul_eq_mul]
    field_simp
  have hGvar : variance (fun ω ↦ blockMaxEmpCDF X a b m n x ω) P ≤ 1 / (4 * m) := by
    rw [hG, variance_const_mul, hsum_eq]
    calc (m : ℝ)⁻¹ ^ 2 * variance (∑ j ∈ range m, I j) P ≤ (m : ℝ)⁻¹ ^ 2 * (m / 4) :=
          mul_le_mul_of_nonneg_left hvarsum (by positivity)
      _ = 1 / (4 * m) := by field_simp
  have hcheb := meas_ge_le_variance_div_sq hGL2 hε
  rw [hGmean] at hcheb
  calc P.real {ω | ε ≤ |blockMaxEmpCDF X a b m n x ω - p|}
      ≤ variance (fun ω ↦ blockMaxEmpCDF X a b m n x ω) P / ε ^ 2 :=
        ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (by positivity)) hcheb
    _ ≤ 1 / (4 * m) / ε ^ 2 := div_le_div_of_nonneg_right hGvar (by positivity)
    _ = 1 / (4 * m * ε ^ 2) := by rw [div_div]

/-- **Consistency of the block maxima method** ([EKM, §6.4.1]; [Coles, §3.3]): if
`F ^ n (a_n x + b_n) → H(x)` (e.g. `x` a continuity point of the extreme value law `H` of the
domain of attraction of `F`), then the empirical distribution function of `m_k` normalized
block maxima of size `n_k` converges in probability to `H(x)` as `m_k, n_k → ∞`. -/
theorem tendstoInMeasure_blockMaxEmpCDF (hX : ∀ t, Measurable (X t))
    (hind : iIndepFun X P) (hid : ∀ t, IdentDistrib (X t) (X 0) P P) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 < a n) {x Hx : ℝ}
    (hMDA : Tendsto (fun n ↦ P.real {ω | X 0 ω ≤ a n * x + b n} ^ n) atTop (𝓝 Hx))
    {m n : ℕ → ℕ} (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    TendstoInMeasure P (fun k ω ↦ blockMaxEmpCDF X a b (m k) (n k) x ω) atTop (fun _ ↦ Hx) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hb : Tendsto (fun k ↦ 1 / (4 * (m k : ℝ) * (ε / 2) ^ 2)) atTop (𝓝 0) := by
    have hmR : Tendsto (fun k ↦ (m k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hm
    have := (tendsto_inv_atTop_zero.comp hmR).const_mul (1 / (4 * (ε / 2) ^ 2))
    rw [mul_zero] at this
    refine this.congr fun k ↦ ?_
    simp only [Function.comp_apply]
    field_simp
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_ hb
  have hp := (hMDA.comp hn).eventually (Metric.ball_mem_nhds Hx hε2)
  filter_upwards [hm.eventually_gt_atTop 0, hn.eventually_gt_atTop 0, hp] with k hmk hnk hpk
  refine le_trans (measureReal_mono fun ω hω ↦ ?_)
    (measureReal_abs_blockMaxEmpCDF_sub_ge_le (a := a) (b := b) hX hind hid ha x hmk hnk hε2)
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
  simp only [Function.comp_apply, Real.dist_eq] at hpk
  have := abs_sub_le (blockMaxEmpCDF X a b (m k) (n k) x ω)
    (P.real {ω | X 0 ω ≤ a (n k) * x + b (n k)} ^ n k) Hx
  linarith

end ExtremeValueTheory
