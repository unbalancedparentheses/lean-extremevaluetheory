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

/-- Extended regular variation only depends on the germ of the function at `+∞`. -/
theorem congr {g : ℝ → ℝ} (hf : IsExtendedRegularlyVarying f γ a) (hfg : f =ᶠ[atTop] g) :
    IsExtendedRegularlyVarying g γ a := by
  refine ⟨hf.1, fun x hx => (hf.2 x hx).congr' ?_⟩
  filter_upwards [hfg, (tendsto_id.const_mul_atTop hx).eventually hfg] with t h1 h2
  simp only [id] at h2
  rw [h1, h2]

/-- A function monotone on `[c, ∞)` agrees eventually with the monotone function
`t ↦ f (max t c)`. -/
theorem monotone_comp_max {c : ℝ} (hmono : MonotoneOn f (Ici c)) :
    Monotone (fun t => f (max t c)) ∧ (fun t => f (max t c)) =ᶠ[atTop] f := by
  refine ⟨fun s t hst => hmono (mem_Ici.2 (le_max_right _ _)) (mem_Ici.2 (le_max_right _ _))
    (max_le_max hst le_rfl), ?_⟩
  filter_upwards [eventually_ge_atTop c] with t ht
  rw [max_eq_left ht]

end IsExtendedRegularlyVarying

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
    simp only [Pi.div_apply, Function.comp_apply, hρ_def]
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
  hf.isRegularlyVarying.of_tendsto_div (hf.tendsto_div_of_pos hmono hγ) (inv_pos.2 hγ)

/-- **Positive index**: `a t / f t → γ`, i.e. `a t ~ γ f t`. -/
theorem IsExtendedRegularlyVarying.tendsto_aux_div_of_pos
    (hf : IsExtendedRegularlyVarying f γ a) (hmono : Monotone f) (hγ : 0 < γ) :
    Tendsto (fun t => a t / f t) atTop (𝓝 γ) := by
  have := (hf.tendsto_div_of_pos hmono hγ).inv₀ (inv_pos.2 hγ).ne'
  rw [inv_inv] at this
  exact this.congr fun t => inv_div _ _

/-! ### Negative index -/

/-- If for every small `ε > 0` eventually `lo ε ≤ g t ≤ hi ε`, and `lo ε, hi ε → L` as
`ε → 0+`, then `g t → L`. -/
private lemma tendsto_of_eventually_bounds {g lo hi : ℝ → ℝ} {L ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hb : ∀ ε, 0 < ε → ε < ε₁ → ∀ᶠ t in atTop, lo ε ≤ g t ∧ g t ≤ hi ε)
    (hlo : Tendsto lo (𝓝 0) (𝓝 L)) (hhi : Tendsto hi (𝓝 0) (𝓝 L)) :
    Tendsto g atTop (𝓝 L) := by
  rw [tendsto_order]
  have hI : Ioo 0 ε₁ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hε₁
  refine ⟨fun b hb' => ?_, fun b hb' => ?_⟩
  · obtain ⟨ε, h1, h2⟩ :=
      (((hlo.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hb')).and hI).exists
    filter_upwards [hb ε h2.1 h2.2] with t ht
    exact h1.trans_le ht.1
  · obtain ⟨ε, h1, h2⟩ :=
      (((hhi.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hb')).and hI).exists
    filter_upwards [hb ε h2.1 h2.2] with t ht
    exact ht.2.trans_lt h1

/-- Upper geometric bound: if `f (2t) - f t ≤ C a t` and `a (2t) ≤ q a t` for `t ≥ T₀`, with
`q < 1`, then `f (2 ^ n t) - f t ≤ C a t / (1 - q)`. -/
private lemma geom_upper {C q T₀ : ℝ} (hT₀ : 0 < T₀) (hC : 0 ≤ C) (hq : q < 1)
    (h : ∀ t ≥ T₀, 0 < a t ∧ f (2 * t) - f t ≤ C * a t ∧ a (2 * t) ≤ q * a t) :
    ∀ n : ℕ, ∀ t ≥ T₀, f (2 ^ n * t) - f t ≤ C * a t / (1 - q) := by
  have hq' : 0 < 1 - q := by linarith
  intro n
  induction n with
  | zero =>
    intro t ht
    simp only [pow_zero, one_mul, sub_self]
    have := (h t ht).1
    positivity
  | succ n ih =>
    intro t ht
    obtain ⟨h1, h2, h3⟩ := h t ht
    have ht2 : 2 * t ≥ T₀ := by linarith
    have ih2 := ih (2 * t) ht2
    rw [show 2 ^ (n + 1) * t = 2 ^ n * (2 * t) by ring]
    have h4 : C * a (2 * t) / (1 - q) ≤ C * (q * a t) / (1 - q) := by gcongr
    have e : C * (q * a t) / (1 - q) + C * a t = C * a t / (1 - q) := by
      field_simp
      ring
    linarith

/-- Lower geometric bound: if `f (2t) - f t ≥ C a t` and `a (2t) ≥ q a t` for `t ≥ T₀`, with
`0 ≤ q < 1`, then `f (2 ^ n t) - f t ≥ C a t (1 - q ^ n) / (1 - q)`. -/
private lemma geom_lower {C q T₀ : ℝ} (hT₀ : 0 < T₀) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq : q < 1)
    (h : ∀ t ≥ T₀, 0 < a t ∧ C * a t ≤ f (2 * t) - f t ∧ q * a t ≤ a (2 * t)) :
    ∀ n : ℕ, ∀ t ≥ T₀, C * a t * (1 - q ^ n) / (1 - q) ≤ f (2 ^ n * t) - f t := by
  have hq' : 0 < 1 - q := by linarith
  intro n
  induction n with
  | zero =>
    intro t ht
    simp
  | succ n ih =>
    intro t ht
    obtain ⟨h1, h2, h3⟩ := h t ht
    have ht2 : 2 * t ≥ T₀ := by linarith
    have ih2 := ih (2 * t) ht2
    rw [show 2 ^ (n + 1) * t = 2 ^ n * (2 * t) by ring]
    have hqn : 0 ≤ 1 - q ^ n := by linarith [pow_le_one₀ hq0 hq.le (n := n)]
    have h4 : C * (q * a t) * (1 - q ^ n) / (1 - q) ≤ C * a (2 * t) * (1 - q ^ n) / (1 - q) := by
      gcongr
    have e : C * (q * a t) * (1 - q ^ n) / (1 - q) + C * a t =
        C * a t * (1 - q ^ (n + 1)) / (1 - q) := by
      field_simp
      ring
    linarith

/-- **Negative index** ([dHF, Lemma 1.2.9], [BGT, §3.1]): if `f` is monotone and extended
regularly varying with index `γ < 0` and auxiliary function `a`, then `f` has a finite limit
`f(∞) = ℓ`, `f ≤ ℓ`, and `(ℓ - f t) / a t → -1 / γ`. -/
theorem IsExtendedRegularlyVarying.exists_tendsto_of_neg (hf : IsExtendedRegularlyVarying f γ a)
    (hmono : Monotone f) (hγ : γ < 0) :
    ∃ ℓ, Tendsto f atTop (𝓝 ℓ) ∧ (∀ t, f t ≤ ℓ) ∧
      Tendsto (fun t => (ℓ - f t) / a t) atTop (𝓝 (-γ⁻¹)) := by
  set p : ℝ := (2 : ℝ) ^ γ with hp
  have hp0 : 0 < p := rpow_pos_of_pos two_pos γ
  have hp1 : p < 1 := rpow_lt_one_of_one_lt_of_neg one_lt_two hγ
  set D := extRVLimit γ 2 with hD
  have hDpos : 0 < D := extRVLimit_pos one_lt_two
  have hF2 : Tendsto (fun t => (f (2 * t) - f t) / a t) atTop (𝓝 D) := hf.2 2 two_pos
  have hR2 : Tendsto (fun t => a (2 * t) / a t) atTop (𝓝 p) := hf.isRegularlyVarying.2 2 two_pos
  have hev : ∀ ε, 0 < ε → ∃ T₀, 0 < T₀ ∧ ∀ t ≥ T₀, 0 < a t ∧
      (D - ε) * a t ≤ f (2 * t) - f t ∧ f (2 * t) - f t ≤ (D + ε) * a t ∧
      (p - ε) * a t ≤ a (2 * t) ∧ a (2 * t) ≤ (p + ε) * a t := by
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hf.1.and
      ((hF2.eventually (Ioo_mem_nhds (show D - ε < D by linarith) (show D < D + ε by linarith))).and
      (hR2.eventually (Ioo_mem_nhds (show p - ε < p by linarith) (show p < p + ε by linarith)))))
    refine ⟨max T₀ 1, by positivity, fun t ht => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hT₀ t (le_of_max_le_left ht)
    obtain ⟨h21, h22⟩ := h2
    obtain ⟨h31, h32⟩ := h3
    rw [lt_div_iff₀ h1] at h21 h31
    rw [div_lt_iff₀ h1] at h22 h32
    exact ⟨h1, h21.le, h22.le, h31.le, h32.le⟩
  set ε₁ := min p (min (1 - p) D) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hp0 (lt_min (by linarith) hDpos)
  have hε₁p : ε₁ ≤ p := min_le_left _ _
  have hε₁q : ε₁ ≤ 1 - p := (min_le_right _ _).trans (min_le_left _ _)
  have hε₁D : ε₁ ≤ D := (min_le_right _ _).trans (min_le_right _ _)
  -- the upper bound `f s ≤ f t + (D + ε) a t / (1 - (p + ε))` for every `s`
  have hsup : ∀ ε, 0 < ε → ε < ε₁ → ∃ T₀, 0 < T₀ ∧ ∀ t ≥ T₀,
      ∀ s, f s ≤ f t + (D + ε) * a t / (1 - (p + ε)) := by
    intro ε hε hε'
    obtain ⟨T₀, hT₀, hb⟩ := hev ε hε
    refine ⟨T₀, hT₀, fun t ht s => ?_⟩
    have hU := geom_upper (f := f) (a := a) hT₀ (by linarith) (by linarith)
      (fun t ht => ⟨(hb t ht).1, (hb t ht).2.2.1, (hb t ht).2.2.2.2⟩)
    have ht0 : 0 < t := hT₀.trans_le ht
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / t) one_lt_two
    rw [div_lt_iff₀ ht0] at hn
    have := hU n t ht
    have := hmono hn.le
    linarith
  obtain ⟨T₁, hT₁, hT₁b⟩ := hsup (ε₁ / 2) (half_pos hε₁0) (half_lt_self hε₁0)
  have hbdd : BddAbove (range f) := ⟨_, by rintro _ ⟨s, rfl⟩; exact hT₁b T₁ le_rfl s⟩
  refine ⟨⨆ s, f s, tendsto_atTop_ciSup hmono hbdd, fun t => le_ciSup hbdd t, ?_⟩
  set ℓ := ⨆ s, f s with hℓ_def
  have hℓ : Tendsto f atTop (𝓝 ℓ) := tendsto_atTop_ciSup hmono hbdd
  have hval : D / (1 - p) = -γ⁻¹ := by
    rw [hD, extRVLimit_of_ne hγ.ne, ← hp]
    have : 1 - p ≠ 0 := by linarith
    field_simp
    ring
  rw [← hval]
  refine tendsto_of_eventually_bounds (lo := fun ε => (D - ε) / (1 - (p - ε)))
    (hi := fun ε => (D + ε) / (1 - (p + ε))) hε₁0 (fun ε hε hε' => ?_) ?_ ?_
  · obtain ⟨T₀, hT₀, hb⟩ := hev ε hε
    obtain ⟨T₂, hT₂, hT₂b⟩ := hsup ε hε hε'
    filter_upwards [eventually_ge_atTop (max T₀ T₂)] with t ht
    have ht0 : T₀ ≤ t := le_of_max_le_left ht
    have ht2 : T₂ ≤ t := le_of_max_le_right ht
    have hat := (hb t ht0).1
    have htpos : 0 < t := hT₀.trans_le ht0
    constructor
    · -- lower bound: let `n → ∞` in the lower geometric bound
      have hL := geom_lower (f := f) (a := a) hT₀ (C := D - ε) (q := p - ε) (by linarith)
        (by linarith) (by linarith)
        (fun t ht => ⟨(hb t ht).1, (hb t ht).2.1, (hb t ht).2.2.2.1⟩)
      have hq1 : p - ε < 1 := by linarith
      have hq0 : 0 ≤ p - ε := by linarith
      have hlim1 : Tendsto (fun n : ℕ => (D - ε) * a t * (1 - (p - ε) ^ n) / (1 - (p - ε)))
          atTop (𝓝 ((D - ε) * a t * (1 - 0) / (1 - (p - ε)))) :=
        (((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_sub 1).const_mul _).div_const _
      have hlim2 : Tendsto (fun n : ℕ => f (2 ^ n * t) - f t) atTop (𝓝 (ℓ - f t)) :=
        (hℓ.comp ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const htpos)).sub_const _
      have := le_of_tendsto_of_tendsto' hlim1 hlim2 fun n => hL n t ht0
      rw [sub_zero, mul_one] at this
      rw [le_div_iff₀ hat]
      calc (D - ε) / (1 - (p - ε)) * a t = (D - ε) * a t / (1 - (p - ε)) := by ring
        _ ≤ ℓ - f t := this
    · have : ℓ ≤ f t + (D + ε) * a t / (1 - (p + ε)) := ciSup_le fun s => hT₂b t ht2 s
      rw [div_le_iff₀ hat]
      calc ℓ - f t ≤ (D + ε) * a t / (1 - (p + ε)) := by linarith
        _ = (D + ε) / (1 - (p + ε)) * a t := by ring
  · have h1 : Tendsto (fun ε : ℝ => D - ε) (𝓝 0) (𝓝 D) :=
      (continuous_const.sub continuous_id).tendsto' 0 D (sub_zero D)
    have h2 : Tendsto (fun ε : ℝ => 1 - (p - ε)) (𝓝 0) (𝓝 (1 - p)) :=
      (continuous_const.sub (continuous_const.sub continuous_id)).tendsto' 0 (1 - p)
        (by show (1 : ℝ) - (p - 0) = 1 - p; rw [sub_zero])
    exact h1.div h2 (by linarith)
  · have h1 : Tendsto (fun ε : ℝ => D + ε) (𝓝 0) (𝓝 D) :=
      (continuous_const.add continuous_id).tendsto' 0 D (add_zero D)
    have h2 : Tendsto (fun ε : ℝ => 1 - (p + ε)) (𝓝 0) (𝓝 (1 - p)) :=
      (continuous_const.sub (continuous_const.add continuous_id)).tendsto' 0 (1 - p)
        (by show (1 : ℝ) - (p + 0) = 1 - p; rw [add_zero])
    exact h1.div h2 (by linarith)

/-- **Negative index**: if `f` is monotone and extended regularly varying with index `γ < 0`,
then `f(∞) = lim f` exists and `f(∞) - f` is regularly varying with index `γ`. -/
theorem IsExtendedRegularlyVarying.isRegularlyVarying_sub_of_neg
    (hf : IsExtendedRegularlyVarying f γ a) (hmono : Monotone f) (hγ : γ < 0) :
    ∃ ℓ, Tendsto f atTop (𝓝 ℓ) ∧ IsRegularlyVarying (fun t => ℓ - f t) γ := by
  obtain ⟨ℓ, h1, -, h3⟩ := hf.exists_tendsto_of_neg hmono hγ
  exact ⟨ℓ, h1, hf.isRegularlyVarying.of_tendsto_div h3 (neg_pos.2 (inv_lt_zero.2 hγ))⟩

/-! ### Non-positive index -/

/-- **Non-positive index** ([dHF, Lemma 1.2.9]): if `f` is eventually positive and extended
regularly varying with index `γ ≤ 0`, then `a t / f t → 0`. -/
theorem IsExtendedRegularlyVarying.tendsto_aux_div_zero_of_nonpos
    (hf : IsExtendedRegularlyVarying f γ a) (hγ : γ ≤ 0) (hpos : ∀ᶠ t in atTop, 0 < f t) :
    Tendsto (fun t => a t / f t) atTop (𝓝 0) := by
  set D := extRVLimit γ 2 with hD
  have hDpos : 0 < D := extRVLimit_pos one_lt_two
  set p : ℝ := (2 : ℝ) ^ γ with hp
  have hp1 : p ≤ 1 := rpow_le_one_of_one_le_of_nonpos one_le_two hγ
  have hF2 : Tendsto (fun t => (f (2 * t) - f t) / a t) atTop (𝓝 D) := hf.2 2 two_pos
  have hR2 : Tendsto (fun t => a (2 * t) / a t) atTop (𝓝 p) := hf.isRegularlyVarying.2 2 two_pos
  suffices h : Tendsto (fun t => f t / a t) atTop atTop by
    refine h.inv_tendsto_atTop.congr fun t => ?_
    simp only [Pi.inv_apply, inv_div]
  rw [tendsto_atTop]
  intro M
  set M' := max M 1 with hM'
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε := min (D / 2) (D / (4 * M')) with hε
  have hε0 : 0 < ε := lt_min (half_pos hDpos) (by positivity)
  have hεD : ε ≤ D / 2 := min_le_left _ _
  have hεM : ε ≤ D / (4 * M') := min_le_right _ _
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hf.1.and (hpos.and
    ((hF2.eventually (lt_mem_nhds (show D - ε < D by linarith))).and
    (hR2.eventually (gt_mem_nhds (show p < 1 + ε by linarith))))))
  set T₀ := max T₁ 1 with hT₀_def
  have hT₀ : 0 < T₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb : ∀ t ≥ T₀, 0 < a t ∧ 0 < f t ∧ (D - ε) * a t ≤ f (2 * t) - f t ∧
      a (2 * t) ≤ (1 + ε) * a t := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hT₁ t (le_of_max_le_left ht)
    rw [lt_div_iff₀ h1] at h3
    rw [div_lt_iff₀ h1] at h4
    exact ⟨h1, h2, h3.le, h4.le⟩
  set w := (1 + ε)⁻¹ with hw
  have hw0 : 0 < w := by positivity
  have hw1 : w < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hwε : w * ε = 1 - w := by rw [hw]; field_simp; ring
  -- `f (2 ^ n t) - f t ≥ (D - ε) a (2 ^ n t) (1 - w ^ n) / ε`
  have key : ∀ n : ℕ, ∀ t ≥ T₀,
      (D - ε) * a (2 ^ n * t) * (1 - w ^ n) / ε ≤ f (2 ^ n * t) - f t := by
    intro n
    induction n with
    | zero => intro t ht; simp
    | succ n ih =>
      intro t ht
      have ht' : 2 ^ n * t ≥ T₀ := le_trans ht (le_mul_of_one_le_left (hT₀.trans_le ht).le
        (one_le_pow₀ one_le_two))
      obtain ⟨h1, -, h3, h4⟩ := hb _ ht'
      have ih' := ih t ht
      rw [show 2 ^ (n + 1) * t = 2 * (2 ^ n * t) by ring]
      have hwn : 0 ≤ 1 - w ^ n := by linarith [pow_le_one₀ hw0.le hw1.le (n := n)]
      have h5 : w * a (2 * (2 ^ n * t)) ≤ a (2 ^ n * t) := by
        rw [hw, inv_mul_le_iff₀ (by linarith)]
        exact h4
      have hc : 0 ≤ (D - ε) * (1 + (1 - w ^ n) / ε) := by
        have : 0 ≤ (1 - w ^ n) / ε := div_nonneg hwn hε0.le
        nlinarith
      have h6 : (D - ε) * (1 + (1 - w ^ n) / ε) * (w * a (2 * (2 ^ n * t))) ≤
          (D - ε) * (1 + (1 - w ^ n) / ε) * a (2 ^ n * t) :=
        mul_le_mul_of_nonneg_left h5 hc
      have e : (D - ε) * a (2 * (2 ^ n * t)) * (1 - w ^ (n + 1)) / ε =
          (D - ε) * (1 + (1 - w ^ n) / ε) * (w * a (2 * (2 ^ n * t))) := by
        have hW : (1 + (1 - w ^ n) / ε) * ε = ε + 1 - w ^ n := by field_simp; ring
        rw [div_eq_iff hε0.ne']
        calc (D - ε) * a (2 * (2 ^ n * t)) * (1 - w ^ (n + 1))
            = (D - ε) * a (2 * (2 ^ n * t)) * (w * ε + w - w * w ^ n) := by rw [hwε]; ring
          _ = (D - ε) * a (2 * (2 ^ n * t)) * w * ((1 + (1 - w ^ n) / ε) * ε) := by
            rw [hW]; ring
          _ = _ := by ring
      have e2 : (D - ε) * (1 + (1 - w ^ n) / ε) * a (2 ^ n * t) =
          (D - ε) * a (2 ^ n * t) + (D - ε) * a (2 ^ n * t) * (1 - w ^ n) / ε := by
        field_simp
      linarith
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hw0.le hw1).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  refine eventually_atTop.2 ⟨2 ^ N * T₀, fun s hs => ?_⟩
  have hsT : 1 ≤ s / T₀ := by
    rw [le_div_iff₀ hT₀, one_mul]
    exact le_trans (le_mul_of_one_le_left hT₀.le (one_le_pow₀ one_le_two)) hs
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hsT one_lt_two
  have hNn : N ≤ n := by
    have h1 : (2 : ℝ) ^ N < 2 ^ (n + 1) := by
      have : (2 : ℝ) ^ N ≤ s / T₀ := by rw [le_div_iff₀ hT₀]; exact hs
      linarith
    have := (pow_lt_pow_iff_right₀ one_lt_two).1 h1
    omega
  set t := s / 2 ^ n with ht_def
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hst : s = 2 ^ n * t := by rw [ht_def]; field_simp
  have htT : T₀ ≤ t := by
    rw [ht_def, le_div_iff₀ h2n, mul_comm]
    rwa [le_div_iff₀ hT₀] at hn1
  have hk := key n t htT
  rw [← hst] at hk
  have hft := (hb t htT).2.1
  have has : 0 < a s := (hb s (by rw [hst]; exact le_trans htT (le_mul_of_one_le_left
      (hT₀.trans_le htT).le (one_le_pow₀ one_le_two)))).1
  have hwn : w ^ n ≤ 1 / 2 := (pow_le_pow_of_le_one hw0.le hw1.le hNn).trans hN.le
  rw [le_div_iff₀ has]
  have h1 : (D - ε) * a s * (1 / 2) / ε ≤ (D - ε) * a s * (1 - w ^ n) / ε := by
    have : 0 ≤ D - ε := by linarith
    gcongr
    linarith
  have h2 : M' * a s ≤ (D - ε) * a s * (1 / 2) / ε := by
    rw [le_div_iff₀ hε0]
    have h3 : ε * (4 * M') ≤ D := by
      have := mul_le_mul_of_nonneg_right hεM (by positivity : (0 : ℝ) ≤ 4 * M')
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    nlinarith
  have h3 : M * a s ≤ M' * a s := mul_le_mul_of_nonneg_right (le_max_left _ _) has.le
  linarith

/-- **Potter-type bound for non-positive index** ([dHF, Theorem B.2.18]): if `f` is monotone on
`[c, ∞)` and extended regularly varying with index `γ ≤ 0`, then for every `δ > 0` there are
`C` and `T₀ > 0` with `f (y t) - f t ≤ C a(t) y ^ δ` for all `t ≥ T₀` and `y ≥ 1`. -/
theorem IsExtendedRegularlyVarying.exists_sub_le_of_nonpos
    (hf : IsExtendedRegularlyVarying f γ a) (hγ : γ ≤ 0) {c : ℝ} (hmono : MonotoneOn f (Ici c))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C T₀ : ℝ, 0 < T₀ ∧ ∀ t ≥ T₀, ∀ y ≥ 1, f (y * t) - f t ≤ C * a t * y ^ δ := by
  set D := extRVLimit γ 2 with hD
  have hDpos : 0 < D := extRVLimit_pos one_lt_two
  set p : ℝ := (2 : ℝ) ^ γ with hp
  have hp1 : p ≤ 1 := rpow_le_one_of_one_le_of_nonpos one_le_two hγ
  set Q : ℝ := (2 : ℝ) ^ δ with hQ
  have hQ1 : 1 < Q := one_lt_rpow one_lt_two hδ
  have hF2 : Tendsto (fun t => (f (2 * t) - f t) / a t) atTop (𝓝 D) := hf.2 2 two_pos
  have hR2 : Tendsto (fun t => a (2 * t) / a t) atTop (𝓝 p) := hf.isRegularlyVarying.2 2 two_pos
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hf.1.and
    ((hF2.eventually (gt_mem_nhds (show D < D + 1 by linarith))).and
    (hR2.eventually (gt_mem_nhds (show p < Q by linarith)))))
  set T₀ := max (max T₁ c) 1 with hT₀_def
  have hT₀ : 0 < T₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hT₀c : c ≤ T₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hb : ∀ t ≥ T₀, 0 < a t ∧ f (2 * t) - f t ≤ (D + 1) * a t ∧ a (2 * t) ≤ Q * a t := by
    intro t ht
    obtain ⟨h1, h3, h4⟩ := hT₁ t (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht)
    rw [div_lt_iff₀ h1] at h3 h4
    exact ⟨h1, h3.le, h4.le⟩
  -- `f (2 ^ n t) - f t ≤ (D + 1) a t (Q ^ n - 1) / (Q - 1)`
  have key : ∀ n : ℕ, ∀ t ≥ T₀,
      f (2 ^ n * t) - f t ≤ (D + 1) * a t * (Q ^ n - 1) / (Q - 1) := by
    intro n
    induction n with
    | zero => intro t ht; simp
    | succ n ih =>
      intro t ht
      obtain ⟨h1, h2, h3⟩ := hb t ht
      have ht2 : 2 * t ≥ T₀ := by linarith
      have ih2 := ih (2 * t) ht2
      rw [show 2 ^ (n + 1) * t = 2 ^ n * (2 * t) by ring]
      have hQn : 0 ≤ Q ^ n - 1 := by linarith [one_le_pow₀ hQ1.le (n := n)]
      have hQ' : 0 < Q - 1 := by linarith
      have h4 : (D + 1) * a (2 * t) * (Q ^ n - 1) / (Q - 1) ≤
          (D + 1) * (Q * a t) * (Q ^ n - 1) / (Q - 1) := by gcongr
      have e : (D + 1) * (Q * a t) * (Q ^ n - 1) / (Q - 1) + (D + 1) * a t =
          (D + 1) * a t * (Q ^ (n + 1) - 1) / (Q - 1) := by
        field_simp
        ring
      linarith
  refine ⟨(D + 1) * Q / (Q - 1), T₀, hT₀, fun t ht y hy => ?_⟩
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hy one_lt_two
  have htpos : 0 < t := hT₀.trans_le ht
  have hat := (hb t ht).1
  have hmon : f (y * t) ≤ f (2 ^ (n + 1) * t) := by
    refine hmono (mem_Ici.2 ?_) (mem_Ici.2 ?_) ?_
    · exact hT₀c.trans (ht.trans (le_mul_of_one_le_left htpos.le hy))
    · exact hT₀c.trans (ht.trans (le_mul_of_one_le_left htpos.le (one_le_pow₀ one_le_two)))
    · exact mul_le_mul_of_nonneg_right hn2.le htpos.le
  have hk := key (n + 1) t ht
  have hQpow : Q ^ (n + 1) ≤ Q * y ^ δ := by
    have e : Q ^ (n + 1) = ((2 : ℝ) ^ (n + 1)) ^ δ := by
      rw [hQ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), mul_comm]
    rw [e, hQ, ← Real.mul_rpow (by norm_num) (by linarith)]
    refine Real.rpow_le_rpow (by positivity) ?_ hδ.le
    rw [pow_succ]
    linarith
  have hQ' : 0 < Q - 1 := by linarith
  have h5 : (D + 1) * a t * (Q ^ (n + 1) - 1) / (Q - 1) ≤
      (D + 1) * a t * (Q * y ^ δ) / (Q - 1) := by
    gcongr
    linarith
  have e : (D + 1) * a t * (Q * y ^ δ) / (Q - 1) = (D + 1) * Q / (Q - 1) * a t * y ^ δ := by
    ring
  linarith

/-- **The logarithm of an extended regularly varying function** ([dHF, Lemma 3.5.1]): if `f` is
eventually positive, monotone on `[c, ∞)`, and extended regularly varying with index `γ` and
auxiliary function `a`, then `log f` is extended regularly varying with index `γ₋ = min γ 0` and
auxiliary function `a / f`. -/
theorem IsExtendedRegularlyVarying.log (hf : IsExtendedRegularlyVarying f γ a) {c : ℝ}
    (hmono : MonotoneOn f (Ici c)) (hpos : ∀ᶠ t in atTop, 0 < f t) :
    IsExtendedRegularlyVarying (fun t => Real.log (f t)) (min γ 0) (fun t => a t / f t) := by
  refine ⟨?_, fun x hx => ?_⟩
  · filter_upwards [hf.1, hpos] with t h1 h2
    exact div_pos h1 h2
  have hs := tendsto_id.const_mul_atTop hx
  set r : ℝ → ℝ := fun t => a t / f t with hr
  set d : ℝ → ℝ := fun t => (f (x * t) - f t) / a t with hd
  have hdlim : Tendsto d atTop (𝓝 (extRVLimit γ x)) := hf.2 x hx
  have hev : ∀ᶠ t in atTop, 0 < a t ∧ 0 < f t ∧ 0 < f (x * t) := by
    filter_upwards [hf.1, hpos, hs.eventually hpos] with t h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hid : ∀ᶠ t in atTop, (Real.log (f (x * t)) - Real.log (f t)) / (a t / f t) =
      Real.log (1 + r t * d t) / r t := by
    filter_upwards [hev] with t ht
    obtain ⟨h1, h2, h3⟩ := ht
    rw [← Real.log_div h3.ne' h2.ne']
    simp only [hr, hd]
    congr 2
    field_simp
    ring
  have hpos' : ∀ᶠ t in atTop, 0 < r t ∧ 0 < 1 + r t * d t := by
    filter_upwards [hev] with t ht
    obtain ⟨h1, h2, h3⟩ := ht
    refine ⟨div_pos h1 h2, ?_⟩
    simp only [hr, hd]
    have : 1 + a t / f t * ((f (x * t) - f t) / a t) = f (x * t) / f t := by
      field_simp
      ring
    rw [this]
    exact div_pos h3 h2
  rcases le_or_gt γ 0 with hγ | hγ
  · rw [min_eq_left hγ]
    have hr0 : Tendsto r atTop (𝓝 0) := hf.tendsto_aux_div_zero_of_nonpos hγ hpos
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun t => d t / (1 + r t * d t))
      ?_ hdlim ?_ ?_
    · have h2 : Tendsto (fun t => 1 + r t * d t) atTop (𝓝 (1 + 0 * extRVLimit γ x)) :=
        tendsto_const_nhds.add (hr0.mul hdlim)
      have := hdlim.div h2 (by norm_num)
      rw [zero_mul, add_zero, div_one] at this
      exact this
    · filter_upwards [hid, hpos'] with t h1 h2
      rw [h1, le_div_iff₀ h2.1]
      have := Real.one_sub_inv_le_log_of_pos h2.2
      have hne := h2.2.ne'
      have e : 1 - (1 + r t * d t)⁻¹ = d t / (1 + r t * d t) * r t := by
        field_simp
        ring
      linarith
    · filter_upwards [hid, hpos'] with t h1 h2
      rw [h1, div_le_iff₀ h2.1]
      have := Real.log_le_sub_one_of_pos h2.2
      linarith
  · rw [min_eq_right hγ.le, extRVLimit_zero_left]
    obtain ⟨hgm, hge⟩ := IsExtendedRegularlyVarying.monotone_comp_max hmono
    have hg := hf.congr hge.symm
    have hrlim : Tendsto r atTop (𝓝 γ) := by
      refine (hg.tendsto_aux_div_of_pos hgm hγ).congr' ?_
      filter_upwards [hge] with t ht
      simp only [hr]
      rw [ht]
    have hxγ : 1 + γ * extRVLimit γ x = x ^ γ := by
      rw [extRVLimit_of_ne hγ.ne']
      field_simp
      ring
    have hval : Real.log (1 + γ * extRVLimit γ x) / γ = Real.log x := by
      rw [hxγ, Real.log_rpow hx]
      field_simp
    rw [← hval]
    have h1 : Tendsto (fun t => 1 + r t * d t) atTop (𝓝 (1 + γ * extRVLimit γ x)) :=
      tendsto_const_nhds.add (hrlim.mul hdlim)
    have hne : 1 + γ * extRVLimit γ x ≠ 0 := by
      rw [hxγ]
      exact (rpow_pos_of_pos hx γ).ne'
    refine (((Real.continuousAt_log hne).tendsto.comp h1).div hrlim hγ.ne').congr' ?_
    filter_upwards [hid] with t ht
    rw [ht]
    rfl

end ExtremeValueTheory
