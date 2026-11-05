/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.DomainOfAttraction.GEVDomain

/-!
# Canonical norming constants, and the equivalent forms of `MDA(H_ξ)`

Let `U` be the tail quantile function of `F`. This file gives the norming constants of `F ∈ MDA(H_ξ)`
in terms of `U`, and states the equivalent forms of membership in `MDA(H_ξ)` for every `ξ`, following
de Haan and Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006) [dHF]. Theorem numbers
of [dHF] are as cited in `docs/HIRATA_COMPARISON.md`; the book was not available to check them.

## Main results

* `tendsto_mul_one_sub_norming_tailQuantile`, `tendsto_pow_norming_tailQuantile`: **canonical
  constants** ([dHF, Corollary 1.2.4]): if `U` is extended regularly varying with auxiliary function
  `a`, then `n (1 - F (a_n x + U_n)) → -log H_ξ(x)` and `F (a_n x + U_n) ^ n → H_ξ(x)`.
* `tendsto_pow_tailQuantile_mul_of_pos`: `ξ > 0`, `F (U_n s) ^ n → Φ_{1/ξ}(s)`.
* `exists_tendsto_pow_tailQuantile_of_neg`: `ξ < 0`, `F ((ℓ - U_n) s + ℓ) ^ n → Ψ_{-1/ξ}(s)`, where
  `ℓ = lim U` is the right endpoint.
* `tendsto_pow_spacing_of_zero`: `ξ = 0`, with `a_n = (U(c n) - U n) / log c`, which needs no auxiliary
  function.
* `isInMDAGEV_iff_exists_tendsto_mul_one_sub`: `F ∈ MDA(H_ξ)` iff `n (1 - F (a_n x + b_n)) → -log H_ξ(x)`
  ([dHF, Theorem 1.1.2]).
* `isInMDAGEV_iff_exists_tendsto_div_tail`: `F ∈ MDA(H_ξ)` iff
  `(1 - F (t + x f(t))) / (1 - F t) → -log H_ξ(x)` as `t ↑ x_F` ([dHF, Theorem 1.2.5]).
* `tendsto_pow_of_norming_equiv`: norming constants can be changed by asymptotically negligible
  amounts.

The limit `-log H_ξ(x)`, for `H_ξ(x) > 0`, is written `gpdSurvivalAll ξ 1 x`
(`gevFun_eq_exp_neg_gpdSurvivalAll`).
-/

open Filter Topology Set Real ExtremeValueTheory

namespace CumulativeDistributionFunction

variable {F : CumulativeDistributionFunction}

/-- `H_ξ(x) = exp (-Ḡ_ξ(x))`, wherever `Ḡ_ξ(x) > 0`. -/
theorem gevFun_eq_exp_neg_gpdSurvivalAll {ξ x : ℝ} (hx : 0 < gpdSurvivalAll ξ 1 x) :
    gevFun ξ x = exp (-gpdSurvivalAll ξ 1 x) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [gevFun]
  · have hpos : 0 < 1 + ξ * x := by
      by_contra hcon
      have : max (1 + ξ * x / 1) 0 = 0 := by
        rw [div_one]
        exact max_eq_right (not_lt.1 hcon)
      simp only [gpdSurvivalAll, hξ, ↓reduceIte, this] at hx
      rw [zero_rpow (by simp [hξ])] at hx
      exact lt_irrefl _ hx
    simp only [gevFun, gpdSurvivalAll, hξ, ↓reduceIte, hpos, div_one, max_eq_left hpos.le,
      neg_div, one_div]

/-- `Ḡ_ξ(x) > 0` if `1 + ξ x > 0`. -/
theorem gpdSurvivalAll_pos_of_one_add_pos {ξ x : ℝ} (hx : 0 < 1 + ξ * x) :
    0 < gpdSurvivalAll ξ 1 x := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [exp_pos]
  · simp only [gpdSurvivalAll, hξ, ↓reduceIte, div_one, max_eq_left hx.le]
    exact rpow_pos_of_pos hx _

/-- If `p_n ∈ [0, 1]` and `p_n ^ n → H > 0`, then `n (1 - p_n) → -log H`. -/
private lemma tendsto_mul_one_sub_of_tendsto_pow {p : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (hp0 : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1) (h : Tendsto (fun n ↦ p n ^ n) atTop (𝓝 H)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - p n)) atTop (𝓝 (-log H)) := by
  have hpos : ∀ᶠ n in atTop, 0 < p n := by
    filter_upwards [h.eventually (lt_mem_nhds (half_lt_self hH)), eventually_gt_atTop 0] with n h1 hn
    rcases (hp0 n).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_pow hn.ne'] at h1
      linarith
  have hlog : Tendsto (fun n : ℕ ↦ -((n : ℝ) * log (p n))) atTop (𝓝 (-log H)) := by
    refine ((continuousAt_log hH.ne').tendsto.comp h).neg.congr' ?_
    filter_upwards [hpos] with n hn
    simp only [Function.comp_apply, log_pow]
  have hlogp : Tendsto (fun n : ℕ ↦ log (p n)) atTop (𝓝 0) := by
    have := hlog.div_atTop tendsto_natCast_atTop_atTop
    have h2 := this.neg
    rw [neg_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hp : Tendsto p atTop (𝓝 1) := by
    have := (continuous_exp.tendsto 0).comp hlogp
    rw [exp_zero] at this
    refine this.congr' ?_
    filter_upwards [hpos] with n hn
    simp only [Function.comp_apply, exp_log hn]
  have hlow : Tendsto (fun n : ℕ ↦ p n * -((n : ℝ) * log (p n))) atTop (𝓝 (-log H)) := by
    simpa using hp.mul hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hlog ?_ ?_
  · filter_upwards [hpos] with n hn
    have h1 : -log (p n) ≤ (p n)⁻¹ - 1 := by
      have := log_le_sub_one_of_pos (inv_pos.2 hn)
      rwa [log_inv] at this
    have h2 : p n * -log (p n) ≤ 1 - p n := by
      have := mul_le_mul_of_nonneg_left h1 hn.le
      rwa [mul_sub, mul_one, mul_inv_cancel₀ hn.ne'] at this
    have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) n)
    nlinarith
  · filter_upwards [hpos] with n hn
    have h1 : 1 - p n ≤ -log (p n) := by linarith [log_le_sub_one_of_pos hn]
    have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) n)
    linarith

/-- If `n (1 - p_n) → τ`, then `p_n ^ n → e^{-τ}`. -/
theorem tendsto_pow_of_tendsto_mul_one_sub {p : ℕ → ℝ} {τ : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - p n)) atTop (𝓝 τ)) :
    Tendsto (fun n ↦ p n ^ n) atTop (𝓝 (exp (-τ))) := by
  have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) * -(1 - p n)) atTop (𝓝 (-τ)) := by
    simpa only [mul_neg] using h.neg
  refine (Real.tendsto_one_add_pow_exp_of_tendsto h1).congr fun n ↦ ?_
  congr 1
  ring

/-- The extension from the support to all `x`: if `F (a_n x + b_n) ^ n → H_ξ(x)` wherever
`1 + ξ x > 0`, then it holds for every `x`, by monotonicity in `x` and the continuity of `H_ξ`. -/
private lemma tendsto_pow_of_tendsto_pow_of_one_add_pos {ξ : ℝ} {a b : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (h : ∀ x, 0 < 1 + ξ * x → Tendsto (fun n ↦ F (a n * x + b n) ^ n) atTop (𝓝 (gevFun ξ x))) (x : ℝ) :
    Tendsto (fun n ↦ F (a n * x + b n) ^ n) atTop (𝓝 (gevFun ξ x)) := by
  by_cases hx : 0 < 1 + ξ * x
  · exact h x hx
  have hξ : ξ ≠ 0 := by
    rintro rfl
    simp at hx
  have hmono : ∀ᶠ n in atTop, ∀ s t : ℝ, s ≤ t → F (a n * s + b n) ^ n ≤ F (a n * t + b n) ^ n := by
    filter_upwards [ha] with n hn s t hst
    refine pow_le_pow_left₀ (F.apply_nonneg _) (F.mono' ?_) n
    have := mul_le_mul_of_nonneg_left hst hn.le
    linarith
  have hc := continuous_gevFun ξ
  set z := -1 / ξ with hz
  have hzξ : 1 + ξ * z = 0 := by
    rw [hz]
    field_simp
    ring
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · -- bounded side: `H_ξ x = 1`
    have hHx : gevFun ξ x = 1 := by simp [gevFun, hξ, hx, not_lt.2 hneg.le]
    have hHz : gevFun ξ z = 1 := by simp [gevFun, hξ, hzξ, not_lt.2 hneg.le]
    have hxz : z ≤ x := by nlinarith
    rw [hHx, tendsto_order]
    refine ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩
    · have hcz : ∀ᶠ y in 𝓝[<] z, m < gevFun ξ y :=
        (hc.tendsto z).mono_left nhdsWithin_le_nhds |>.eventually (lt_mem_nhds (by rwa [hHz]))
      obtain ⟨y, hy1, hy2⟩ := (hcz.and self_mem_nhdsWithin).exists
      have hy2' : y < z := hy2
      have hsupp : 0 < 1 + ξ * y := by nlinarith
      filter_upwards [(h y hsupp).eventually (lt_mem_nhds hy1), hmono] with n h1 h2
      exact h1.trans_le (h2 y x (hy2'.le.trans hxz))
    · exact Eventually.of_forall fun n ↦
        (pow_le_one₀ (F.apply_nonneg _) (F.apply_le_one _)).trans_lt hm
  · -- heavy side: `H_ξ x = 0`
    have hHx : gevFun ξ x = 0 := by simp [gevFun, hξ, hx, hpos]
    have hHz : gevFun ξ z = 0 := by simp [gevFun, hξ, hzξ, hpos]
    have hxz : x ≤ z := by
      have : ξ * x ≤ ξ * z := by linarith
      exact le_of_mul_le_mul_left this hpos
    rw [hHx, tendsto_order]
    refine ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩
    · filter_upwards [eventually_gt_atTop 0] with n _
      exact hm.trans_le (pow_nonneg (F.apply_nonneg _) n)
    · have hcz : ∀ᶠ y in 𝓝[>] z, gevFun ξ y < m :=
        (hc.tendsto z).mono_left nhdsWithin_le_nhds |>.eventually (gt_mem_nhds (by rwa [hHz]))
      obtain ⟨y, hy1, hy2⟩ := (hcz.and self_mem_nhdsWithin).exists
      have hy2' : z < y := hy2
      have hsupp : 0 < 1 + ξ * y := by nlinarith
      filter_upwards [(h y hsupp).eventually (gt_mem_nhds hy1), hmono] with n h1 h2
      exact (h2 x y (hxz.trans hy2'.le)).trans_lt h1

/-- **The canonical levels, tail form** ([dHF, Corollary 1.2.4]): if the tail quantile function `U` is
extended regularly varying with auxiliary function `a`, then for `v > 0`,
`n (1 - F (a_n x + U_n)) → v` at `x = gevTransform γ v`. Here `a_n`, `U_n` are the values of `a`, `U`
at the integer `n`. -/
theorem tendsto_mul_one_sub_gevTransform_tailQuantile {γ : ℝ} {a : ℝ → ℝ}
    (hU : IsExtendedRegularlyVarying F.tailQuantile γ a) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
        (1 - F (a n * gevTransform γ v + F.tailQuantile n))) atTop (𝓝 v) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  set x := gevTransform γ v with hx
  -- the relation at the quantile `w`
  have hlim : ∀ w : ℝ, 0 < w → Tendsto (fun n : ℕ ↦ (F.tailQuantile (w⁻¹ * n) - F.tailQuantile n) /
      a n) atTop (𝓝 (gevTransform γ w)) := fun w hw ↦ by
    have := (hU.2 w⁻¹ (inv_pos.2 hw)).comp hn
    rwa [← gevTransform_inv (inv_pos.2 hw), inv_inv] at this
  have hev : ∀ w : ℝ, 0 < w → ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ∧ 0 < a n ∧ 1 < w⁻¹ * n := fun w hw ↦ by
    filter_upwards [hn.eventually (eventually_gt_atTop 0), hn.eventually hU.1,
      hn.eventually ((tendsto_id.const_mul_atTop (inv_pos.2 hw)).eventually
        (eventually_gt_atTop 1))] with n h0 h1 h2
    exact ⟨h0, h1, h2⟩
  rw [tendsto_order]
  refine ⟨fun m hm ↦ ?_, fun M hM ↦ ?_⟩
  · -- lower bound
    obtain ⟨w, hmw, hwv⟩ := exists_between (max_lt hm hv)
    have hw0 : 0 < w := (le_max_right m 0).trans_lt hmw
    have hmw' : m < w := (le_max_left m 0).trans_lt hmw
    have hlt := gevTransform_lt_gevTransform (ξ := γ) hw0 hwv
    filter_upwards [hev w hw0, (hlim w hw0).eventually (lt_mem_nhds hlt)] with n hb h1
    obtain ⟨hn0, han, ht⟩ := hb
    rw [lt_div_iff₀ han] at h1
    have hy : a n * x + F.tailQuantile n < F.tailQuantile (w⁻¹ * n) := by linarith
    have h2 := (F.tailQuantile_spec ht).2 _ hy
    have h5 : (n : ℝ) * (1 / (w⁻¹ * n)) = w := by
      field_simp
    have := mul_lt_mul_of_pos_left h2 hn0
    linarith
  · -- upper bound
    obtain ⟨w, hvw, hwM⟩ := exists_between hM
    have hw0 : 0 < w := hv.trans hvw
    have hlt := gevTransform_lt_gevTransform (ξ := γ) hv hvw
    filter_upwards [hev w hw0, (hlim w hw0).eventually (gt_mem_nhds hlt)] with n hb h1
    obtain ⟨hn0, han, ht⟩ := hb
    rw [div_lt_iff₀ han] at h1
    have hUle : F.tailQuantile (w⁻¹ * n) ≤ a n * x + F.tailQuantile n := by linarith
    have h2 := (F.tailQuantile_spec ht).1
    have h3 := F.mono' hUle
    change F (F.tailQuantile (w⁻¹ * n)) ≤ F (a n * x + F.tailQuantile n) at h3
    have h4 : 1 - F (a n * x + F.tailQuantile n) ≤ 1 / (w⁻¹ * n) := by linarith
    have h5 : (n : ℝ) * (1 / (w⁻¹ * n)) = w := by
      field_simp
    have := mul_le_mul_of_nonneg_left h4 hn0.le
    linarith

/-- **The canonical levels, tail form** ([dHF, Corollary 1.2.4]): if `U` is extended regularly
varying with auxiliary function `a`, then `n (1 - F (a_n x + U_n)) → -log H_γ(x)` wherever
`1 + γ x > 0`, that is, wherever `gpdSurvivalAll γ 1 x > 0`. -/
theorem tendsto_mul_one_sub_norming_tailQuantile {γ : ℝ} {a : ℝ → ℝ}
    (hU : IsExtendedRegularlyVarying F.tailQuantile γ a) {x : ℝ} (hx : 0 < gpdSurvivalAll γ 1 x) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - F (a n * x + F.tailQuantile n))) atTop
      (𝓝 (gpdSurvivalAll γ 1 x)) := by
  have := tendsto_mul_one_sub_gevTransform_tailQuantile hU hx
  rwa [gevTransform_gpdSurvivalAll hx] at this

/-- **Canonical norming constants** ([dHF, Corollary 1.2.4]): if the tail quantile function `U` is
extended regularly varying with index `γ` and auxiliary function `a`, then
`F (a_n x + U_n) ^ n → H_γ(x)` for every `x`. So `U_n` and `a_n` are norming constants. -/
theorem tendsto_pow_norming_tailQuantile {γ : ℝ} {a : ℝ → ℝ}
    (hU : IsExtendedRegularlyVarying F.tailQuantile γ a) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ F (a n * x + F.tailQuantile n) ^ n) atTop (𝓝 (gevCDF γ x)) := by
  rw [gevCDF_apply]
  refine tendsto_pow_of_tendsto_pow_of_one_add_pos (a := fun n : ℕ ↦ a n)
    (b := fun n : ℕ ↦ F.tailQuantile n)
    (tendsto_natCast_atTop_atTop.eventually hU.1) (fun y hy ↦ ?_) x
  have hpos := gpdSurvivalAll_pos_of_one_add_pos hy
  rw [gevFun_eq_exp_neg_gpdSurvivalAll hpos]
  exact tendsto_pow_of_tendsto_mul_one_sub (tendsto_mul_one_sub_norming_tailQuantile hU hpos)

/-- **Canonical norming constants exist** ([dHF, Corollary 1.2.4]): if `F ∈ MDA(H_γ)`, there is `a > 0`
near `∞` with `(U (t x) - U t) / a t → (x ^ γ - 1) / γ`, and `F (a_n x + U_n) ^ n → H_γ(x)` for every
`x`. -/
theorem exists_tendsto_pow_norming_tailQuantile {γ : ℝ} (hF : F.IsInMDAGEV γ) :
    ∃ a : ℝ → ℝ, IsExtendedRegularlyVarying F.tailQuantile γ a ∧ ∀ x,
      Tendsto (fun n : ℕ ↦ F (a n * x + F.tailQuantile n) ^ n) atTop (𝓝 (gevCDF γ x)) := by
  obtain ⟨a, ha⟩ := F.isExtendedRegularlyVarying_tailQuantile hF
  exact ⟨a, ha, tendsto_pow_norming_tailQuantile ha⟩

/-- **Norming constants may be changed by negligible amounts** (the easy half of the convergence of
types theorem): if `F (a_n x + b_n) ^ n → H x` for every `x`, with `H` continuous and `a_n > 0`
eventually, and `a'_n / a_n → 1`, `(b'_n - b_n) / a_n → 0`, then `F (a'_n x + b'_n) ^ n → H x`. -/
theorem tendsto_pow_of_norming_equiv {H : ℝ → ℝ} (hH : Continuous H) {a b a' b' : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (h : ∀ x, Tendsto (fun n ↦ F (a n * x + b n) ^ n) atTop (𝓝 (H x)))
    (hr : Tendsto (fun n ↦ a' n / a n) atTop (𝓝 1))
    (hs : Tendsto (fun n ↦ (b' n - b n) / a n) atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n ↦ F (a' n * x + b' n) ^ n) atTop (𝓝 (H x)) := by
  have hlim : Tendsto (fun n ↦ a' n / a n * x + (b' n - b n) / a n) atTop (𝓝 x) := by
    simpa using (hr.mul_const x).add hs
  have hmono : ∀ᶠ n in atTop, ∀ y, y ≤ a' n / a n * x + (b' n - b n) / a n →
      F (a n * y + b n) ^ n ≤ F (a' n * x + b' n) ^ n := by
    filter_upwards [ha] with n hn y hy
    refine pow_le_pow_left₀ (F.apply_nonneg _) (F.mono' ?_) n
    have h1 := mul_le_mul_of_nonneg_left hy hn.le
    have h2 : a n * (a' n / a n * x + (b' n - b n) / a n) = a' n * x + (b' n - b n) := by
      field_simp
    linarith
  have hmono' : ∀ᶠ n in atTop, ∀ y, a' n / a n * x + (b' n - b n) / a n ≤ y →
      F (a' n * x + b' n) ^ n ≤ F (a n * y + b n) ^ n := by
    filter_upwards [ha] with n hn y hy
    refine pow_le_pow_left₀ (F.apply_nonneg _) (F.mono' ?_) n
    have h1 := mul_le_mul_of_nonneg_left hy hn.le
    have h2 : a n * (a' n / a n * x + (b' n - b n) / a n) = a' n * x + (b' n - b n) := by
      field_simp
    linarith
  rw [tendsto_order]
  refine ⟨fun m hm ↦ ?_, fun M hM ↦ ?_⟩
  · have hc : ∀ᶠ y in 𝓝[<] x, m < H y :=
      (hH.tendsto x).mono_left nhdsWithin_le_nhds |>.eventually (lt_mem_nhds hm)
    obtain ⟨y, hy1, hy2⟩ := (hc.and self_mem_nhdsWithin).exists
    filter_upwards [(h y).eventually (lt_mem_nhds hy1), hmono,
      hlim.eventually (lt_mem_nhds hy2)] with n h1 h2 h3
    exact h1.trans_le (h2 y h3.le)
  · have hc : ∀ᶠ y in 𝓝[>] x, H y < M :=
      (hH.tendsto x).mono_left nhdsWithin_le_nhds |>.eventually (gt_mem_nhds hM)
    obtain ⟨y, hy1, hy2⟩ := (hc.and self_mem_nhdsWithin).exists
    filter_upwards [(h y).eventually (gt_mem_nhds hy1), hmono',
      hlim.eventually (gt_mem_nhds hy2)] with n h1 h2 h3
    exact (h2 y h3.le).trans_lt h1

/-- The inverse of the affine map `x ↦ a x + b`. -/
private lemma inv_mkOfCoefs_apply {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    (AffineIncrEquiv.mkOfCoefs ha b)⁻¹ x = (x - b) / a := by
  have h1 : AffineIncrEquiv.mkOfCoefs ha b ((AffineIncrEquiv.mkOfCoefs ha b)⁻¹ x) = x := by
    rw [← AffineIncrEquiv.mul_apply_eq_comp_apply, mul_inv_cancel, AffineIncrEquiv.one_apply]
  rw [AffineIncrEquiv.apply_eq, AffineIncrEquiv.coefs_fst_mkOfCoefs,
    AffineIncrEquiv.coefs_snd_mkOfCoefs] at h1
  rw [eq_div_iff ha.ne']
  linarith

/-- **Norming constants for `ξ > 0`** (compare [dHF, Corollary 1.2.4]): if `F ∈ MDA(H_ξ)` with `ξ > 0`,
then `F (U_n s) ^ n → Φ_{1/ξ}(s)` for every `s`: no location is needed, and the scale is `U_n`. -/
theorem tendsto_pow_tailQuantile_mul_of_pos {ξ : ℝ} (hF : F.IsInMDAGEV ξ) (hξ : 0 < ξ) (s : ℝ) :
    Tendsto (fun n : ℕ ↦ F (F.tailQuantile n * s) ^ n) atTop
      (𝓝 (standardFrechetCDF (one_div_pos.2 hξ) s)) := by
  obtain ⟨a, ha, -, hdiv⟩ := F.isRegularlyVarying_tailQuantile_of_pos hF hξ
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ ↦ ξ * F.tailQuantile n / a n) atTop (𝓝 1) := by
    have h1 := ((hdiv.comp hn).inv₀ hξ.ne').const_mul ξ
    rw [mul_inv_cancel₀ hξ.ne'] at h1
    refine h1.congr fun n ↦ ?_
    simp only [Function.comp_apply, inv_div]
    ring
  have hs : Tendsto (fun n : ℕ ↦ (F.tailQuantile n - F.tailQuantile n) / a n) atTop (𝓝 0) := by
    simp
  have h := tendsto_pow_of_norming_equiv (F := F) (H := gevCDF ξ) (continuous_gevCDF ξ)
    (a := fun n : ℕ ↦ a n) (b := fun n : ℕ ↦ F.tailQuantile n)
    (hn.eventually ha.1) (tendsto_pow_norming_tailQuantile ha) hr hs ((s - 1) / ξ)
  rw [← mkOfCoefs_smul_gevCDF_of_pos hξ, mulAction_apply_eq, inv_mkOfCoefs_apply]
  refine h.congr fun n ↦ ?_
  congr 2
  field_simp
  ring

/-- **Norming constants for `ξ < 0`** (compare [dHF, Corollary 1.2.4]): if `F ∈ MDA(H_ξ)` with `ξ < 0`,
then `U` has a finite limit `ℓ`, the right endpoint, and `F ((ℓ - U_n) s + ℓ) ^ n → Ψ_{-1/ξ}(s)` for
every `s`. -/
theorem exists_tendsto_pow_tailQuantile_of_neg {ξ : ℝ} (hF : F.IsInMDAGEV ξ) (hξ : ξ < 0) :
    ∃ ℓ : ℝ, Tendsto F.tailQuantile atTop (𝓝 ℓ) ∧ ∀ s,
      Tendsto (fun n : ℕ ↦ F ((ℓ - F.tailQuantile n) * s + ℓ) ^ n) atTop
        (𝓝 (standardWeibullCDF (show 0 < -1 / ξ from div_pos_of_neg_of_neg (by norm_num) hξ) s)) := by
  obtain ⟨a, ℓ, ha, hℓ, -, hdiv⟩ := F.exists_isRegularlyVarying_tailQuantile_of_neg hF hξ
  refine ⟨ℓ, hℓ, fun s ↦ ?_⟩
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hξ0 : ξ ≠ 0 := hξ.ne
  have hr : Tendsto (fun n : ℕ ↦ (-ξ * (ℓ - F.tailQuantile n)) / a n) atTop (𝓝 1) := by
    have h1 := (hdiv.comp hn).const_mul (-ξ)
    rw [show -ξ * -ξ⁻¹ = 1 by field_simp] at h1
    refine h1.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    ring
  have hs : Tendsto (fun n : ℕ ↦ (F.tailQuantile n - F.tailQuantile n) / a n) atTop (𝓝 0) := by
    simp
  have h := tendsto_pow_of_norming_equiv (F := F) (H := gevCDF ξ) (continuous_gevCDF ξ)
    (a := fun n : ℕ ↦ a n) (b := fun n : ℕ ↦ F.tailQuantile n)
    (hn.eventually ha.1) (tendsto_pow_norming_tailQuantile ha) hr hs ((s + 1) / -ξ)
  rw [← mkOfCoefs_smul_gevCDF_of_neg hξ, mulAction_apply_eq, inv_mkOfCoefs_apply,
    show s - -1 = s + 1 by ring]
  refine h.congr fun n ↦ ?_
  congr 2
  field_simp
  ring

/-- **Norming constants for `ξ = 0`, with no auxiliary function** (compare [dHF, Corollary 1.2.4]): if
`F ∈ MDA(H_0)` and `c > 1`, then `F (a_n x + U_n) ^ n → Λ(x)` for every `x`, with the spacing
`a_n = (U (c n) - U n) / log c`. -/
theorem tendsto_pow_spacing_of_zero (hF : F.IsInMDAGEV 0) {c : ℝ} (hc : 1 < c) (x : ℝ) :
    Tendsto (fun n : ℕ ↦
      F ((F.tailQuantile (c * n) - F.tailQuantile n) / log c * x + F.tailQuantile n) ^ n) atTop
      (𝓝 (standardGumbelCDF x)) := by
  obtain ⟨a, ha⟩ := F.isExtendedRegularlyVarying_tailQuantile hF
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlogc : 0 < log c := log_pos hc
  have hr : Tendsto (fun n : ℕ ↦
      ((F.tailQuantile (c * n) - F.tailQuantile n) / log c) / a n) atTop (𝓝 1) := by
    have h1 := ((ha.2 c (by linarith)).comp hn).div_const (log c)
    rw [boxCox_zero, div_self hlogc.ne'] at h1
    refine h1.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    rw [div_right_comm]
  have hs : Tendsto (fun n : ℕ ↦ (F.tailQuantile n - F.tailQuantile n) / a n) atTop (𝓝 0) := by
    simp
  have h := tendsto_pow_of_norming_equiv (F := F) (H := gevCDF 0) (continuous_gevCDF 0)
    (a := fun n : ℕ ↦ a n) (b := fun n : ℕ ↦ F.tailQuantile n)
    (hn.eventually ha.1) (tendsto_pow_norming_tailQuantile ha) hr hs x
  rwa [gevCDF_zero] at h

/-- **The tail form of the domain of attraction** ([dHF, Theorem 1.1.2]): `F ∈ MDA(H_ξ)` if and only if
there are `a_n > 0` and `b_n` with `n (1 - F (a_n x + b_n)) → -log H_ξ(x)` wherever `1 + ξ x > 0`
(`gevFun_eq_exp_neg_gpdSurvivalAll`). -/
theorem isInMDAGEV_iff_exists_tendsto_mul_one_sub (ξ : ℝ) :
    F.IsInMDAGEV ξ ↔ ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∀ x, 0 < gpdSurvivalAll ξ 1 x →
      Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - F (a n * x + b n))) atTop (𝓝 (gpdSurvivalAll ξ 1 x)) := by
  rw [isInMDAGEV_iff_exists_tendsto_gevCDF]
  constructor
  · rintro ⟨As, hAs⟩
    refine ⟨fun n ↦ (As n)⁻¹.coefs.1, fun n ↦ (As n)⁻¹.coefs.2, fun n ↦ (As n)⁻¹.coefs_fst_pos,
      fun x hx ↦ ?_⟩
    have hval : gevCDF ξ x = exp (-gpdSurvivalAll ξ 1 x) := by
      rw [gevCDF_apply, gevFun_eq_exp_neg_gpdSurvivalAll hx]
    have hlim := hAs x
    rw [hval] at hlim
    have h := tendsto_mul_one_sub_of_tendsto_pow (p := fun n ↦ (As n • F) x) (exp_pos _)
      (fun n ↦ (As n • F).apply_nonneg x) (fun n ↦ (As n • F).apply_le_one x) hlim
    rw [log_exp, neg_neg] at h
    refine h.congr fun n ↦ ?_
    rw [mulAction_apply_eq, AffineIncrEquiv.apply_eq]
  · rintro ⟨a, b, ha, h⟩
    refine ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs (ha n) (b n))⁻¹, fun x ↦ ?_⟩
    have hval : Tendsto (fun n ↦ F (a n * x + b n) ^ n) atTop (𝓝 (gevFun ξ x)) :=
      tendsto_pow_of_tendsto_pow_of_one_add_pos (Eventually.of_forall ha) (fun y hy ↦ by
        have hpos := gpdSurvivalAll_pos_of_one_add_pos hy
        rw [gevFun_eq_exp_neg_gpdSurvivalAll hpos]
        exact tendsto_pow_of_tendsto_mul_one_sub (h y hpos)) x
    rw [gevCDF_apply]
    refine hval.congr fun n ↦ ?_
    rw [mulAction_apply_eq, inv_inv]
    simp

/-- **The excess form of the domain of attraction** ([dHF, Theorem 1.2.5]): `F ∈ MDA(H_ξ)` if and only
if there is `f`, positive near the right endpoint `x_F`, with
`(1 - F (t + x f(t))) / (1 - F t) → -log H_ξ(x)` as `t ↑ x_F`, wherever `1 + ξ x > 0`. This includes
negative `x`. Compare the Gumbel case `isInMDAGumbel_iff`, and the uniform form
`isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival`. -/
theorem isInMDAGEV_iff_exists_tendsto_div_tail (ξ : ℝ) :
    F.IsInMDAGEV ξ ↔ ∃ f : ℝ → ℝ, (∀ᶠ t in F.upperEndpointFilter, 0 < f t) ∧
      ∀ x, 0 < gpdSurvivalAll ξ 1 x →
        Tendsto (fun t ↦ (1 - F (t + f t * x)) / (1 - F t)) F.upperEndpointFilter
          (𝓝 (gpdSurvivalAll ξ 1 x)) := by
  rw [F.isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival ξ]
  refine exists_congr fun β ↦ and_congr_right fun hβ ↦ ⟨fun hU x hx ↦ ?_, fun h ↦ ?_⟩
  · rcases le_or_gt 0 x with h0 | h0
    · exact hU.tendsto_at (mem_Ici.2 h0)
    · have hinv := gevTransform_gpdSurvivalAll hx
      refine tendsto_div_tail_of_tendstoUniformlyOn_excessSurvival hβ hU ?_ hinv
      by_contra hcon
      have hle : gpdSurvivalAll ξ 1 x ≤ 1 := not_lt.1 hcon
      rcases hle.lt_or_eq with hlt | heq
      · have := gevTransform_lt_gevTransform (ξ := ξ) hx hlt
        rw [hinv, gevTransform_one] at this
        linarith
      · rw [heq, gevTransform_one] at hinv
        linarith
  · have hanti : ∀ᶠ u in F.upperEndpointFilter,
        AntitoneOn (fun x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x)) (Ici 0) := by
      filter_upwards [hβ] with u hu x _ y _ hxy
      refine div_le_div_of_nonneg_right ?_ (by linarith [F.apply_le_one u])
      have : F (u + β u * x) ≤ F (u + β u * y) :=
        F.mono' (by linarith [mul_le_mul_of_nonneg_left hxy hu.le])
      linarith
    have hnn : ∀ᶠ u in F.upperEndpointFilter, ∀ x ∈ Ici (0 : ℝ),
        0 ≤ excessSurvival (fun y ↦ 1 - F y) u (β u * x) :=
      Eventually.of_forall fun u x _ ↦
        div_nonneg (by linarith [F.apply_le_one (u + β u * x)]) (by linarith [F.apply_le_one u])
    refine tendstoUniformlyOn_Ici_of_antitoneOn (c := 0) hanti hnn
      (gpdSurvivalAll_antitoneOn one_pos) (gpdSurvivalAll_continuousOn one_pos)
      (gpdSurvivalAll_tendsto_atTop one_pos) fun x hx ↦ ?_
    by_cases hx0 : 0 < gpdSurvivalAll ξ 1 x
    · exact h x hx0
    -- past the endpoint of the limit: squeeze with a point where the limit is small
    have hval : gpdSurvivalAll ξ 1 x = 0 :=
      le_antisymm (not_lt.1 hx0) (gpdSurvivalAll_nonneg _ _ _)
    rw [hval, tendsto_order]
    have hc := (gpdSurvivalAll_continuousOn (ξ := ξ) one_pos)
    have hx' : (0 : ℝ) ≤ x := hx
    refine ⟨fun m hm ↦ ?_, fun M hM ↦ ?_⟩
    · filter_upwards [hβ] with u hu
      exact hm.trans_le (div_nonneg (by linarith [F.apply_le_one (u + β u * x)])
        (by linarith [F.apply_le_one u]))
    · -- `s₀`, the infimum of the zeros of the limit on `[0, x]`
      have hne : (Icc 0 x ∩ {s | gpdSurvivalAll ξ 1 s = 0}).Nonempty := ⟨x, ⟨hx', le_rfl⟩, hval⟩
      have hcl : IsClosed (Icc 0 x ∩ {s | gpdSurvivalAll ξ 1 s = 0}) := by
        have : Icc 0 x ∩ {s | gpdSurvivalAll ξ 1 s = 0} = Icc 0 x ∩ gpdSurvivalAll ξ 1 ⁻¹' {0} := rfl
        rw [this]
        exact (hc.mono (fun t ht ↦ ht.1)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
      obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc.of_isClosed_subset hcl inter_subset_left).exists_isLeast hne
      have hs₀0 : 0 < s₀ := by
        rcases (hs₀.1.1).lt_or_eq with h' | h'
        · exact h'
        · have h1 := hs₀.2
          rw [← h', mem_ofPred_eq, gpdSurvivalAll_zero_right] at h1
          norm_num at h1
      have hcs : ContinuousWithinAt (gpdSurvivalAll ξ 1) (Ici 0) s₀ := hc s₀ hs₀.1.1
      have hev : ∀ᶠ y in 𝓝[<] s₀, gpdSurvivalAll ξ 1 y < M := by
        have h1 : Tendsto (gpdSurvivalAll ξ 1) (𝓝[<] s₀) (𝓝 (gpdSurvivalAll ξ 1 s₀)) := by
          refine hcs.tendsto.mono_left (nhdsWithin_le_iff.2 ?_)
          filter_upwards [Ioo_mem_nhdsLT hs₀0] with y hy
          exact hy.1.le
        have h2 : gpdSurvivalAll ξ 1 s₀ < M := by
          rw [show gpdSurvivalAll ξ 1 s₀ = 0 from hs₀.2]
          exact hM
        exact h1.eventually (gt_mem_nhds h2)
      have hIoo : ∀ᶠ y in 𝓝[<] s₀, y ∈ Ioo 0 s₀ := Ioo_mem_nhdsLT hs₀0
      obtain ⟨y, hy1, hy2⟩ := (hev.and hIoo).exists
      have hy3' : y < s₀ := hy2.2
      have hypos : 0 < gpdSurvivalAll ξ 1 y := by
        refine lt_of_le_of_ne (gpdSurvivalAll_nonneg _ _ _) fun h0 ↦ ?_
        have : s₀ ≤ y := hmin ⟨⟨hy2.1.le, hy3'.le.trans hs₀.1.2⟩, h0.symm⟩
        linarith
      filter_upwards [(h y hypos).eventually (gt_mem_nhds hy1), hβ] with u h1 hu
      refine lt_of_le_of_lt ?_ h1
      refine div_le_div_of_nonneg_right ?_ (by linarith [F.apply_le_one u])
      have : y ≤ x := hy3'.le.trans hs₀.1.2
      have : F (u + β u * y) ≤ F (u + β u * x) :=
        F.mono' (by linarith [mul_le_mul_of_nonneg_left this hu.le])
      linarith

end CumulativeDistributionFunction
