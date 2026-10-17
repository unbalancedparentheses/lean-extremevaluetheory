/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Basic

/-!
# Extended regular variation

A function `f : ℝ → ℝ` is *extended regularly varying* with index `γ ∈ ℝ` and auxiliary function
`a > 0` if

  `(f (x t) - f t) / a t → D_γ(x) = (x ^ γ - 1) / γ`   (`log x` if `γ = 0`)

as `t → ∞`, for every `x > 0` (de Haan and Ferreira, *Extreme Value Theory: An Introduction*,
Springer 2006, §1.1 and Appendix B.2 [dHF]; Bingham, Goldie and Teugels, *Regular Variation*,
Chapter 3 [BGT], where this is de Haan's class `Π` for `γ = 0`). By [dHF, Theorem 1.1.6] the
tail quantile function `U = F^←(1 - 1/·)` of a distribution in the domain of attraction of
`H_γ` is extended regularly varying with index `γ` (see
`ExtremeValueTheory.DomainOfAttraction.Quantile`).

## Main definitions

* `ExtremeValueTheory.extRVLimit γ x`: the limit function `D_γ(x)`.
* `ExtremeValueTheory.IsExtendedRegularlyVarying f γ a`: `f` is extended regularly varying with
  index `γ` and auxiliary function `a`.

## Main results

* `IsExtendedRegularlyVarying.of_one_lt`: it suffices to check the limit relation for `x > 1`.
* `IsExtendedRegularlyVarying.isRegularlyVarying`: the auxiliary function is regularly varying
  with index `γ` ([dHF, Theorem B.2.1]).
* `IsExtendedRegularlyVarying.tendsto_div_of_pos`, `.isRegularlyVarying_of_pos`: for `γ > 0`
  and monotone `f`, `f t / a t → 1 / γ`, so `f` is regularly varying with index `γ` and
  `a t ~ γ f t` ([dHF, Lemma 1.2.9], [BGT, §3.1]).
* `IsExtendedRegularlyVarying.exists_tendsto_of_neg`, `.isRegularlyVarying_sub_of_neg`: for
  `γ < 0` and monotone `f`, `f(∞) = lim f` exists, `(f(∞) - f t) / a t → -1 / γ`, and
  `f(∞) - f` is regularly varying with index `γ` ([dHF, Lemma 1.2.9]).

The monotonicity assumption (satisfied by tail quantile functions) replaces the measurability
assumption of [dHF, Appendix B]; some regularity is needed, since `f t = t ^ γ + H (log t)` with
`H` a discontinuous additive function is extended regularly varying with `a t = γ t ^ γ` but is
not regularly varying.
-/

open Filter Topology Set Real

namespace ExtremeValueTheory

/-! ### The limit function -/

/-- The limit function of extended regular variation, `D_γ(x) = (x ^ γ - 1) / γ` for `γ ≠ 0`
and `D_0(x) = log x`. -/
noncomputable def extRVLimit (γ x : ℝ) : ℝ :=
  if γ = 0 then Real.log x else (x ^ γ - 1) / γ

section Limit

variable {γ : ℝ}

theorem extRVLimit_zero_left (x : ℝ) : extRVLimit 0 x = Real.log x := by
  simp [extRVLimit]

theorem extRVLimit_of_ne (hγ : γ ≠ 0) (x : ℝ) : extRVLimit γ x = (x ^ γ - 1) / γ := by
  simp [extRVLimit, hγ]

theorem extRVLimit_one (γ : ℝ) : extRVLimit γ 1 = 0 := by
  unfold extRVLimit
  split_ifs <;> simp

/-- The cocycle identity `D_γ(x y) = D_γ(x) + x ^ γ D_γ(y)`. -/
theorem extRVLimit_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    extRVLimit γ (x * y) = extRVLimit γ x + x ^ γ * extRVLimit γ y := by
  by_cases hγ : γ = 0
  · subst hγ
    simp [extRVLimit, Real.log_mul hx.ne' hy.ne']
  · simp only [extRVLimit, hγ, ↓reduceIte]
    rw [mul_rpow hx.le hy.le]
    field_simp
    ring

theorem extRVLimit_pos {x : ℝ} (hx : 1 < x) : 0 < extRVLimit γ x := by
  rcases lt_trichotomy γ 0 with hγ | hγ | hγ
  · rw [extRVLimit_of_ne hγ.ne]
    exact div_pos_of_neg_of_neg (by linarith [rpow_lt_one_of_one_lt_of_neg hx hγ]) hγ
  · subst hγ
    simp [extRVLimit, Real.log_pos hx]
  · rw [extRVLimit_of_ne hγ.ne']
    exact div_pos (by linarith [one_lt_rpow hx hγ]) hγ

end Limit

/-! ### Definition and basic properties -/

/-- A function `f` is **extended regularly varying** with index `γ` and auxiliary function `a`
([dHF, Definition B.2.1], [BGT, §3.0]): `a` is eventually positive and for every `x > 0`,
`(f (x t) - f t) / a t → D_γ(x)` as `t → ∞`. -/
def IsExtendedRegularlyVarying (f : ℝ → ℝ) (γ : ℝ) (a : ℝ → ℝ) : Prop :=
  (∀ᶠ t in atTop, 0 < a t) ∧
    ∀ x : ℝ, 0 < x → Tendsto (fun t => (f (x * t) - f t) / a t) atTop (𝓝 (extRVLimit γ x))

variable {f a : ℝ → ℝ} {γ : ℝ}

/-- From the limit relation for `x > 1`, the ratio `a (y t) / a t` tends to `y ^ γ` for `y > 1`:
`a (y t) / a t = (D_t(2y) - D_t(y)) / D_{yt}(2)` with `D_t(x) = (f (x t) - f t) / a t`. -/
private lemma tendsto_aux_ratio (ha : ∀ᶠ t in atTop, 0 < a t)
    (h : ∀ x : ℝ, 1 < x → Tendsto (fun t => (f (x * t) - f t) / a t) atTop
      (𝓝 (extRVLimit γ x)))
    {y : ℝ} (hy : 1 < y) : Tendsto (fun t => a (y * t) / a t) atTop (𝓝 (y ^ γ)) := by
  have hy0 : 0 < y := by linarith
  have hs := tendsto_id.const_mul_atTop hy0
  have hA := h (2 * y) (by linarith)
  have hB := h y hy
  have hC := (h 2 one_lt_two).comp hs
  have hD2 : extRVLimit γ 2 ≠ 0 := (extRVLimit_pos one_lt_two).ne'
  have hlim := (hA.sub hB).div hC hD2
  have hval : (extRVLimit γ (2 * y) - extRVLimit γ y) / extRVLimit γ 2 = y ^ γ := by
    rw [mul_comm 2 y, extRVLimit_mul hy0 two_pos]
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [ha, hs.eventually ha, hC.eventually_ne hD2] with t h1 h2 h3
  simp only [Function.comp_apply, id, Pi.div_apply] at h2 h3 ⊢
  rw [show 2 * y * t = 2 * (y * t) by ring]
  have h3' : f (2 * (y * t)) - f (y * t) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at h3
    exact h3 rfl
  generalize f (2 * (y * t)) = A at *
  generalize f (y * t) = B at *
  generalize a (y * t) = q at *
  rw [div_sub_div_same, show A - f t - (B - f t) = A - B by ring]
  field_simp

/-- To check extended regular variation it suffices to consider `x > 1`. -/
theorem IsExtendedRegularlyVarying.of_one_lt (ha : ∀ᶠ t in atTop, 0 < a t)
    (h : ∀ x : ℝ, 1 < x → Tendsto (fun t => (f (x * t) - f t) / a t) atTop
      (𝓝 (extRVLimit γ x))) :
    IsExtendedRegularlyVarying f γ a := by
  refine ⟨ha, fun x hx => ?_⟩
  rcases lt_trichotomy x 1 with hx1 | rfl | hx1
  · have hxi : 1 < x⁻¹ := (one_lt_inv₀ hx).2 hx1
    have hs := tendsto_id.const_mul_atTop hx
    have h1 := (h x⁻¹ hxi).comp hs
    have h2 := ((tendsto_aux_ratio ha h hxi).comp hs).inv₀ (rpow_pos_of_pos (inv_pos.2 hx) γ).ne'
    have hlim := (h1.mul h2).neg
    have hval : -(extRVLimit γ x⁻¹ * (x⁻¹ ^ γ)⁻¹) = extRVLimit γ x := by
      have := extRVLimit_mul (γ := γ) hx (inv_pos.2 hx)
      rw [mul_inv_cancel₀ hx.ne', extRVLimit_one] at this
      rw [inv_rpow hx.le, inv_inv]
      linarith
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [ha, hs.eventually ha] with t h3 h4
    simp only [Function.comp_apply, id] at h4 ⊢
    rw [← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul]
    field_simp
    ring
  · simp only [one_mul, sub_self, zero_div, extRVLimit_one]
    exact tendsto_const_nhds
  · exact h x hx1

namespace IsExtendedRegularlyVarying

theorem eventually_pos (hf : IsExtendedRegularlyVarying f γ a) : ∀ᶠ t in atTop, 0 < a t := hf.1

theorem tendsto (hf : IsExtendedRegularlyVarying f γ a) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t => (f (x * t) - f t) / a t) atTop (𝓝 (extRVLimit γ x)) := hf.2 x hx

/-- **The auxiliary function is regularly varying** with index `γ` ([dHF, Theorem B.2.1]). -/
theorem isRegularlyVarying (hf : IsExtendedRegularlyVarying f γ a) : IsRegularlyVarying a γ := by
  have hr : ∀ c : ℝ, 1 < c → Tendsto (fun t => a (c * t) / a t) atTop (𝓝 (c ^ γ)) :=
    fun c hc => tendsto_aux_ratio hf.1 (fun x hx => hf.2 x (by linarith)) hc
  refine ⟨hf.1, fun c hc => ?_⟩
  rcases lt_trichotomy c 1 with h1 | rfl | h1
  · have hci : 1 < c⁻¹ := (one_lt_inv₀ hc).2 h1
    have h2 := ((hr c⁻¹ hci).comp (tendsto_id.const_mul_atTop hc)).inv₀
      (rpow_pos_of_pos (inv_pos.2 hc) γ).ne'
    rw [Real.inv_rpow hc.le, inv_inv] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp_apply, id]
    rw [inv_div, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  · simp only [one_mul, one_rpow]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hf.1] with t ht
    exact (div_self ht.ne').symm
  · exact hr c h1

end IsExtendedRegularlyVarying

/-- If `g / a → c > 0` and `a` is regularly varying with index `ρ`, so is `g`. -/
theorem IsRegularlyVarying.of_tendsto_div {g : ℝ → ℝ} {ρ c : ℝ} (hc : 0 < c)
    (ha : IsRegularlyVarying a ρ) (h : Tendsto (fun t => g t / a t) atTop (𝓝 c)) :
    IsRegularlyVarying g ρ := by
  have hg : ∀ᶠ t in atTop, 0 < g t := by
    filter_upwards [ha.1, h.eventually (lt_mem_nhds hc)] with t h1 h2
    have := mul_pos h2 h1
    rwa [div_mul_cancel₀ _ h1.ne'] at this
  refine ⟨hg, fun x hx => ?_⟩
  have hs := tendsto_id.const_mul_atTop hx
  have hlim := ((h.comp hs).mul (ha.2 x hx)).div h hc.ne'
  rw [mul_div_right_comm, div_self hc.ne', one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [ha.1, hs.eventually ha.1, hg] with t h1 h2 h3
  simp only [Function.comp_apply, id, Pi.div_apply] at h2 ⊢
  field_simp

/-! ### Positive index -/

/-- An iteration lemma: if `h (x t) = ρ t h t + ε t` with `ρ t → r ∈ [0, 1)` and `ε t → 0`, and
`h` is bounded on intervals `[T, x T]` with `T` arbitrarily large, then `h t → 0`. -/
private lemma tendsto_zero_of_recursion {h ρ ε : ℝ → ℝ} {x r : ℝ} (hx : 1 < x) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hrec : ∀ᶠ t in atTop, h (x * t) = ρ t * h t + ε t)
    (hρ : Tendsto ρ atTop (𝓝 r)) (hε : Tendsto ε atTop (𝓝 0))
    (hB : ∀ T₀, ∃ T, T₀ ≤ T ∧ 0 < T ∧ ∃ B, ∀ t ∈ Icc T (x * T), |h t| ≤ B) :
    Tendsto h atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set q := (1 + r) / 2 with hq
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hrq : r < q := by rw [hq]; linarith
  have hx0 : 0 < x := by linarith
  set c := η * (1 - q) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; have : 0 < 1 - q := by linarith
                         positivity
  have hρ' : ∀ᶠ t in atTop, |ρ t| ≤ q := by
    filter_upwards [hρ.eventually (Ioo_mem_nhds (show -q < r by linarith) hrq)] with t ht
    exact abs_le.2 ⟨ht.1.le, ht.2.le⟩
  have hε' : ∀ᶠ t in atTop, |ε t| ≤ c := by
    filter_upwards [hε.eventually (Ioo_mem_nhds (show -c < 0 by linarith) hc0)] with t ht
    exact abs_le.2 ⟨ht.1.le, ht.2.le⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hrec.and (hρ'.and hε'))
  obtain ⟨T, hT, hTpos, B, hB⟩ := hB T₀
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have key : ∀ n : ℕ, ∀ t ∈ Icc (x ^ n * T) (x ^ (n + 1) * T), |h t| ≤ q ^ n * B' + η / 2 := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simp only [pow_zero, one_mul, zero_add, pow_one] at ht ⊢
      linarith [hB t ht, le_max_left B 0]
    | succ n ih =>
      intro t ht
      set s := t / x with hs
      have hts : t = x * s := by rw [hs]; field_simp
      have hsI : s ∈ Icc (x ^ n * T) (x ^ (n + 1) * T) := by
        rw [hts] at ht
        constructor
        · have := ht.1
          rw [pow_succ] at this
          nlinarith
        · have := ht.2
          rw [pow_succ] at this
          nlinarith
      have hsT : T₀ ≤ s := by
        have : T ≤ x ^ n * T := le_mul_of_one_le_left hTpos.le (one_le_pow₀ hx.le)
        linarith [hsI.1]
      obtain ⟨e1, e2, e3⟩ := hT₀ s hsT
      have ihs := ih s hsI
      rw [hts, e1]
      calc |ρ s * h s + ε s| ≤ |ρ s| * |h s| + |ε s| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ q * (q ^ n * B' + η / 2) + c := by
            gcongr
        _ = q ^ (n + 1) * B' + η / 2 := by rw [hc]; ring
  have hlim : Tendsto (fun N : ℕ => q ^ N * B') atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const B'
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds (half_pos hη))).exists
  filter_upwards [eventually_ge_atTop (x ^ N * T)] with s hs
  have hsT : 1 ≤ s / T := by
    rw [le_div_iff₀ hTpos, one_mul]
    exact le_trans (le_mul_of_one_le_left hTpos.le (one_le_pow₀ hx.le)) hs
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hsT hx
  have hNn : N ≤ n := by
    have h1 : x ^ N < x ^ (n + 1) := by
      have : x ^ N ≤ s / T := by rw [le_div_iff₀ hTpos]; exact hs
      linarith
    have := (pow_lt_pow_iff_right₀ hx).1 h1
    omega
  have hmem : s ∈ Icc (x ^ n * T) (x ^ (n + 1) * T) := by
    constructor
    · rwa [le_div_iff₀ hTpos] at hn1
    · rw [div_lt_iff₀ hTpos] at hn2; exact hn2.le
  have := key n s hmem
  have hqn : q ^ n * B' ≤ q ^ N * B' :=
    mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1.le hNn) hB'0
  rw [Real.dist_eq, sub_zero]
  linarith

/-- **Positive index** ([dHF, Lemma 1.2.9], [BGT, §3.1]): if `f` is monotone and extended
regularly varying with index `γ > 0` and auxiliary function `a`, then `f t / a t → 1 / γ`. -/
theorem IsExtendedRegularlyVarying.tendsto_div_of_pos (hf : IsExtendedRegularlyVarying f γ a)
    (hmono : Monotone f) (hγ : 0 < γ) : Tendsto (fun t => f t / a t) atTop (𝓝 γ⁻¹) := by
  set u : ℝ := (2 : ℝ) ^ γ with hu
  have hu1 : 1 < u := one_lt_rpow one_lt_two hγ
  have hu0 : 0 < u := by linarith
  have h4 : (4 : ℝ) ^ γ = u ^ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_rpow (by norm_num) (by norm_num), hu, sq]
  have hD4 : extRVLimit γ 4 = (u ^ 2 - 1) / γ := by rw [extRVLimit_of_ne hγ.ne', h4]
  have hD2 : extRVLimit γ 2 = (u - 1) / γ := by rw [extRVLimit_of_ne hγ.ne']
  have hu2 : 0 < u ^ 2 - 1 := by nlinarith
  have hD4pos : 0 < extRVLimit γ 4 := extRVLimit_pos (by norm_num)
  have hD2pos : 0 < extRVLimit γ 2 := extRVLimit_pos one_lt_two
  have hs2 : Tendsto (fun t : ℝ => 2 * t) atTop atTop := tendsto_id.const_mul_atTop two_pos
  set L : ℝ → ℝ := fun t => f (4 * t) - f t with hL_def
  have hL : Tendsto (fun t => L t / a t) atTop (𝓝 (extRVLimit γ 4)) := hf.2 4 (by norm_num)
  have hF2 : Tendsto (fun t => (f (2 * t) - f t) / a t) atTop (𝓝 (extRVLimit γ 2)) :=
    hf.2 2 two_pos
  have hR2 : Tendsto (fun t => a (2 * t) / a t) atTop (𝓝 u) := hf.isRegularlyVarying.2 2 two_pos
  have hLpos : ∀ᶠ t in atTop, 0 < L t := by
    filter_upwards [hf.1, hL.eventually (lt_mem_nhds hD4pos)] with t h1 h2
    have := mul_pos h2 h1
    rwa [div_mul_cancel₀ _ h1.ne'] at this
  have hev : ∀ᶠ t in atTop, 0 < a t ∧ 0 < a (2 * t) ∧ 0 < L t ∧ 0 < L (2 * t) := by
    filter_upwards [hf.1, hs2.eventually hf.1, hLpos, hs2.eventually hLpos] with t h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  set c : ℝ := (u ^ 2 - 1)⁻¹ with hc
  set ρ : ℝ → ℝ := fun t => L t / L (2 * t) with hρ_def
  set δ : ℝ → ℝ := fun t => (f (2 * t) - f t) / L t with hδ_def
  set h : ℝ → ℝ := fun t => f t / L t - c with hh_def
  set ε : ℝ → ℝ := fun t => ρ t * (c + δ t) - c with hε_def
  have hρlim : Tendsto ρ atTop (𝓝 u⁻¹) := by
    have := hL.div ((hL.comp hs2).mul hR2) (mul_pos hD4pos hu0).ne'
    rw [show extRVLimit γ 4 / (extRVLimit γ 4 * u) = u⁻¹ by field_simp] at this
    refine this.congr' ?_
    filter_upwards [hev] with t ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    simp only [Function.comp_apply, Pi.div_apply, Pi.mul_apply]
    generalize L t = A at *
    generalize L (2 * t) = B at *
    generalize a t = p at *
    generalize a (2 * t) = q at *
    field_simp
  have hδlim : Tendsto δ atTop (𝓝 (extRVLimit γ 2 / extRVLimit γ 4)) := by
    refine (hF2.div hL hD4pos.ne').congr' ?_
    filter_upwards [hev] with t ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    simp only [Pi.div_apply, hδ_def]
    generalize L t = A at *
    generalize a t = p at *
    field_simp
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (hρlim.mul (hδlim.const_add c)).sub_const c
    convert this using 2
    rw [hD2, hD4, hc]
    have h1 : u ^ 2 - 1 ≠ 0 := hu2.ne'
    have h2 : u + 1 ≠ 0 := by linarith
    have h3 : u - 1 ≠ 0 := by linarith
    have h5 : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
    rw [h5]
    field_simp
    ring
  have hrec : ∀ᶠ t in atTop, h (2 * t) = ρ t * h t + ε t := by
    filter_upwards [hev] with t ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    simp only [hh_def, hρ_def, hε_def, hδ_def]
    generalize L t = A at *
    generalize L (2 * t) = B at *
    generalize f (2 * t) = C at *
    generalize f t = D at *
    field_simp
    ring
  have hF2pos : ∀ᶠ t in atTop, 0 < f (2 * t) - f t := by
    filter_upwards [hf.1, hF2.eventually (lt_mem_nhds hD2pos)] with t h1 h2
    have := mul_pos h2 h1
    rwa [div_mul_cancel₀ _ h1.ne'] at this
  have hbdd : ∀ T₀, ∃ T, T₀ ≤ T ∧ 0 < T ∧ ∃ B, ∀ t ∈ Icc T (2 * T), |h t| ≤ B := by
    intro T₀
    have hgap : ∀ᶠ T in atTop, 0 < T ∧ 0 < f (4 * T) - f (2 * T) := by
      filter_upwards [hs2.eventually hF2pos, eventually_gt_atTop 0] with T h1 h2
      refine ⟨h2, ?_⟩
      rwa [show 2 * (2 * T) = 4 * T by ring] at h1
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hgap
    set T := max T₀ T₁
    obtain ⟨hT0, hm⟩ := hT₁ T (le_max_right _ _)
    refine ⟨T, le_max_left _ _, hT0, (|f T| + |f (2 * T)|) / (f (4 * T) - f (2 * T)) + |c|,
      fun t ht => ?_⟩
    have hft : |f t| ≤ |f T| + |f (2 * T)| := by
      have h1 := hmono ht.1
      have h2 := hmono ht.2
      rw [abs_le]
      constructor <;> cases abs_cases (f T) <;> cases abs_cases (f (2 * T)) <;> linarith
    have hLt : f (4 * T) - f (2 * T) ≤ L t := by
      simp only [hL_def]
      have h1 := hmono (show 4 * T ≤ 4 * t by linarith [ht.1])
      have h2 := hmono ht.2
      linarith
    have hLt0 : 0 < L t := hm.trans_le hLt
    simp only [hh_def]
    calc |f t / L t - c| ≤ |f t / L t| + |c| := abs_sub _ _
      _ ≤ (|f T| + |f (2 * T)|) / (f (4 * T) - f (2 * T)) + |c| := by
          gcongr
          rw [abs_div, abs_of_pos hLt0]
          exact div_le_div₀ (by positivity) hft hm hLt
  have hu1' : u⁻¹ < 1 := inv_lt_one_of_one_lt₀ hu1
  have hh := tendsto_zero_of_recursion one_lt_two (inv_pos.2 hu0).le hu1' hrec hρlim hεlim hbdd
  have hfL : Tendsto (fun t => f t / L t) atTop (𝓝 c) := by
    have := hh.const_add c
    rw [add_zero] at this
    refine this.congr fun t => ?_
    simp only [hh_def]
    ring
  have := hfL.mul hL
  rw [hD4, hc, show (u ^ 2 - 1)⁻¹ * ((u ^ 2 - 1) / γ) = γ⁻¹ by field_simp] at this
  refine this.congr' ?_
  filter_upwards [hev] with t ht
  obtain ⟨h1, -, h3, -⟩ := ht
  field_simp

/-- **Positive index**: a monotone extended regularly varying function with index `γ > 0` is
regularly varying with index `γ`. -/
theorem IsExtendedRegularlyVarying.isRegularlyVarying_of_pos
    (hf : IsExtendedRegularlyVarying f γ a) (hmono : Monotone f) (hγ : 0 < γ) :
    IsRegularlyVarying f γ :=
  hf.isRegularlyVarying.of_tendsto_div (inv_pos.2 hγ) (hf.tendsto_div_of_pos hmono hγ)

/-- **Positive index**: `a t / f t → γ`, i.e. `a t ~ γ f t`. -/
theorem IsExtendedRegularlyVarying.tendsto_aux_div_of_pos
    (hf : IsExtendedRegularlyVarying f γ a) (hmono : Monotone f) (hγ : 0 < γ) :
    Tendsto (fun t => a t / f t) atTop (𝓝 γ) := by
  have := (hf.tendsto_div_of_pos hmono hγ).inv₀ (inv_pos.2 hγ).ne'
  rw [inv_inv] at this
  exact this.congr fun t => inv_div _ _

end ExtremeValueTheory
