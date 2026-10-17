/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ExtremeValueDistribution
import ExtremeValueTheory.LimitRelationManipulation

/-!
# The Gumbel maximum domain of attraction

A c.d.f. `F` is in the maximum domain of attraction of the standard Gumbel distribution
`Λ(x) = exp (-exp (-x))` if there are orientation preserving affine maps `A n` with
`((A n • F) x) ^ n → Λ x` for every `x`.

We prove the classical sufficient condition via an *auxiliary function*: if `x_F` is the right
endpoint of `F` and there is a positive function `f` with
`(1 - F (t + x * f t)) / (1 - F t) → exp (-x)` as `t ↑ x_F`, for every real `x`, then `F` is in
the Gumbel domain of attraction, with normalizing constants `b n = F^← (1 - 1 / n)`
(here `sInf {y | 1 - F y ≤ 1 / n}`) and `a n = f (b n)`. Both the case `x_F = +∞` and the case of
a finite right endpoint are treated. We then derive the von Mises condition
`(1 - F) F'' / (F') ^ 2 → -1` (as `t → ∞`, or as `t ↑ x_F` for a finite right endpoint at which
`F` is continuous), which yields the auxiliary function `f = (1 - F) / F'`, and deduce that the
standard exponential distribution, the Gumbel distribution itself and the finite-endpoint
distribution `1 - exp (-x / (1 - x))` on `[0, 1)` are in the Gumbel domain of attraction.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorems 1.1.8 and 1.2.5 [dHF].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Theorems 3.3.26 and 3.3.27 [EKM].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Propositions 1.1 and 1.4 [Resnick].

## Main definitions and results

* `CumulativeDistributionFunction.IsInMDAGumbel F`: `F` is in the maximum domain of attraction
  of `standardGumbelCDF`.
* `CumulativeDistributionFunction.isInMDAGumbel_of_tendsto_mul`: the tail limit relation
  `n (1 - F (a n * x + b n)) → exp (-x)` gives membership.
* `CumulativeDistributionFunction.isInMDAGumbel_of_auxiliary_atTop`,
  `CumulativeDistributionFunction.isInMDAGumbel_of_auxiliary_nhdsLT`: sufficiency via an
  auxiliary function, for infinite and finite right endpoint.
* `CumulativeDistributionFunction.tendsto_auxiliary_of_vonMises`,
  `CumulativeDistributionFunction.isInMDAGumbel_of_vonMises`: the von Mises condition, `x_F = ∞`.
* `CumulativeDistributionFunction.tendsto_auxiliary_of_vonMises_nhdsLT`,
  `CumulativeDistributionFunction.isInMDAGumbel_of_vonMises_nhdsLT`: the von Mises condition for
  a finite right endpoint `x_F`.
* `CumulativeDistributionFunction.isInMDAGumbel_standardExponentialCDF`,
  `CumulativeDistributionFunction.isInMDAGumbel_standardGumbelCDF`,
  `CumulativeDistributionFunction.isInMDAGumbel_expNegInvCDF`: examples.

The converse (de Haan's theorem: every `F` in the Gumbel domain of attraction admits such an
auxiliary function) is in `ExtremeValueTheory.DomainOfAttraction.GumbelNecessity`, which also
states the full characterization `isInMDAGumbel_iff`.
-/

open Filter Topology Set

namespace ExtremeValueTheory

namespace Gumbel

/-- The analytic core of the sufficiency direction: if `g (t + x f t) / g t → exp (-x)` along a
filter `L` and the levels `b n → L` satisfy `g (b n) ≤ 1 / n < g y` for `y < b n`, then
`n * g (b n + x * f (b n)) → exp (-x)`. -/
theorem tendsto_mul_of_auxiliary {g f : ℝ → ℝ} {L : Filter ℝ}
    (h : ∀ x, Tendsto (fun t ↦ g (t + x * f t) / g t) L (𝓝 (Real.exp (-x))))
    (hf : ∀ᶠ t in L, 0 < f t) (hg : ∀ᶠ t in L, 0 < g t) {b : ℕ → ℝ} (hb : Tendsto b atTop L)
    (hq : ∀ᶠ n : ℕ in atTop, g (b n) ≤ 1 / n ∧ ∀ y < b n, 1 / (n : ℝ) < g y) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * g (b n + x * f (b n))) atTop (𝓝 (Real.exp (-x))) := by
  have hfb := hb.eventually hf
  have hgb := hb.eventually hg
  have hkey : Tendsto (fun n : ℕ ↦ (n : ℝ) * g (b n)) atTop (𝓝 1) := by
    rw [tendsto_order]
    constructor
    · intro l hl
      have hcont : Tendsto (fun δ : ℝ ↦ Real.exp (-δ)) (𝓝[>] 0) (𝓝 1) := by
        have : Tendsto (fun δ : ℝ ↦ Real.exp (-δ)) (𝓝 0) (𝓝 (Real.exp (-0))) :=
          (Real.continuous_exp.comp continuous_neg).tendsto 0
        rw [neg_zero, Real.exp_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      obtain ⟨δ, hδl, hδ⟩ := ((hcont.eventually (lt_mem_nhds hl)).and
        self_mem_nhdsWithin).exists
      have hδ' : (0 : ℝ) < δ := hδ
      have hr : Tendsto (fun n ↦ (g (b n + (-δ) * f (b n)) / g (b n))⁻¹) atTop
          (𝓝 (Real.exp (-δ))) := by
        have := ((h (-δ)).comp hb).inv₀ (Real.exp_pos _).ne'
        rw [neg_neg, ← Real.exp_neg] at this
        exact this
      filter_upwards [hr.eventually (lt_mem_nhds hδl), hq, hfb, hgb, eventually_ge_atTop 1]
        with n h1 h2 h3 h4 hn1
      have hy : b n + (-δ) * f (b n) < b n := by
        have : 0 < δ * f (b n) := mul_pos hδ' h3
        linarith
      have h5 := h2.2 _ hy
      have hn : (0 : ℝ) < n := by exact_mod_cast hn1
      have hgy : 0 < g (b n + (-δ) * f (b n)) := lt_trans (by positivity) h5
      rw [inv_div] at h1
      have hX : 1 < (n : ℝ) * g (b n + (-δ) * f (b n)) := by
        rw [div_lt_iff₀ hn] at h5; linarith
      have e : (n : ℝ) * g (b n) =
          (n * g (b n + (-δ) * f (b n))) * (g (b n) / g (b n + (-δ) * f (b n))) := by
        rw [mul_assoc, mul_div_cancel₀ _ hgy.ne']
      rw [e]
      have : 0 < g (b n) / g (b n + (-δ) * f (b n)) := div_pos h4 hgy
      nlinarith
    · intro u hu
      filter_upwards [hq, eventually_ge_atTop 1] with n hn hn1
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
      have : (n : ℝ) * g (b n) ≤ 1 := by
        have := hn.1
        rw [le_div_iff₀ hn'] at this; linarith
      linarith
  have := hkey.mul ((h x).comp hb)
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [hgb] with n hn
  simp only [Function.comp_apply]
  field_simp

/-- Basic properties of the generalized quantile `sInf {x | g x ≤ c}` of an antitone,
right-continuous function `g`. -/
theorem quantile_spec {g : ℝ → ℝ} (hg : Antitone g)
    (hgr : ∀ x, ContinuousWithinAt g (Ici x) x) {c : ℝ} (hne : ∃ x, g x ≤ c)
    (hbdd : ∃ y, c < g y) :
    g (sInf {x | g x ≤ c}) ≤ c ∧ ∀ y < sInf {x | g x ≤ c}, c < g y := by
  obtain ⟨y₀, hy₀⟩ := hbdd
  have hlb : ∀ x ∈ {x | g x ≤ c}, y₀ ≤ x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have := hg hcon.le
    simp only [mem_ofPred_eq] at hx
    linarith
  have hB : BddBelow {x | g x ≤ c} := ⟨y₀, hlb⟩
  have hne' : ({x | g x ≤ c} : Set ℝ).Nonempty := hne
  set s := sInf {x | g x ≤ c} with hs
  constructor
  · have hlim : Tendsto g (𝓝[>] s) (𝓝 (g s)) :=
      (hgr s).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun x hx ↦ ?_)
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne' (show s < x from hx)
    exact (hg hyx.le).trans hy
  · intro y hy
    by_contra hcon
    push Not at hcon
    exact absurd (csInf_le hB hcon) (not_le.2 hy)

end Gumbel

end ExtremeValueTheory

namespace CumulativeDistributionFunction

open ExtremeValueTheory

/-- A c.d.f. `F` is in the maximum domain of attraction of the standard Gumbel distribution
`Λ(x) = exp (-exp (-x))` if there are orientation preserving affine maps `A n` with
`((A n • F) x) ^ n → Λ x` for every `x`. (Since `Λ` is continuous, this is the same as
convergence at all continuity points.) -/
def IsInMDAGumbel (F : CumulativeDistributionFunction) : Prop :=
  ∃ As : ℕ → AffineIncrEquiv,
    ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (standardGumbelCDF x))

private lemma standardGumbelCDF_mem_Ioo (x : ℝ) : standardGumbelCDF x ∈ Ioo 0 1 := by
  rw [standardGumbelCDF_apply_eq]
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith [Real.exp_pos (-x)])⟩

private lemma neg_log_standardGumbelCDF (x : ℝ) :
    -Real.log (standardGumbelCDF x) = Real.exp (-x) := by
  rw [standardGumbelCDF_apply_eq, Real.log_exp, neg_neg]

private lemma antitone_one_sub (F : CumulativeDistributionFunction) :
    Antitone (fun x ↦ 1 - F x) :=
  fun _ _ h ↦ sub_le_sub_left (F.mono' h) 1

private lemma rightContinuous_one_sub (F : CumulativeDistributionFunction) :
    ∀ x, ContinuousWithinAt (fun x ↦ 1 - F x) (Ici x) x :=
  fun x ↦ continuousWithinAt_const.sub (F.right_continuous x)

/-- The tail limit relation `n * (1 - F (a n * x + b n)) → exp (-x)` for all `x` (with `a n > 0`)
implies that `F` is in the Gumbel domain of attraction. -/
theorem isInMDAGumbel_of_tendsto_mul (F : CumulativeDistributionFunction) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 < a n)
    (h : ∀ x, Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - F (a n * x + b n))) atTop
      (𝓝 (Real.exp (-x)))) :
    F.IsInMDAGumbel := by
  refine ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs (ha n) (b n))⁻¹, fun x ↦ ?_⟩
  have happ : ∀ n, ((AffineIncrEquiv.mkOfCoefs (ha n) (b n))⁻¹ • F) x = F (a n * x + b n) := by
    intro n; simp
  refine ((tfae_ev_limit_relation (F := F) _ (standardGumbelCDF_mem_Ioo x)).out 1 3).2 ?_
  rw [neg_log_standardGumbelCDF]
  simpa only [happ] using h x

/-- From the quantile levels to the domain of attraction, along an arbitrary filter. -/
private lemma isInMDAGumbel_of_quantile (F : CumulativeDistributionFunction) {L : Filter ℝ}
    {f : ℝ → ℝ} (hf : ∀ᶠ t in L, 0 < f t) (hF : ∀ᶠ t in L, F t < 1)
    (h : ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) L (𝓝 (Real.exp (-x))))
    (hb : Tendsto (fun n : ℕ ↦ sInf {y | 1 - F y ≤ 1 / (n : ℝ)}) atTop L)
    (hq : ∀ᶠ n : ℕ in atTop, 1 - F (sInf {y | 1 - F y ≤ 1 / (n : ℝ)}) ≤ 1 / n ∧
      ∀ y < sInf {y | 1 - F y ≤ 1 / (n : ℝ)}, 1 / (n : ℝ) < 1 - F y) :
    F.IsInMDAGumbel := by
  set b : ℕ → ℝ := fun n ↦ sInf {y | 1 - F y ≤ 1 / (n : ℝ)} with hbdef
  have hg : ∀ᶠ t in L, 0 < 1 - F t := hF.mono fun t ht ↦ by linarith
  have key := Gumbel.tendsto_mul_of_auxiliary (g := fun y ↦ 1 - F y) h hf hg hb hq
  set a : ℕ → ℝ := fun n ↦ if 0 < f (b n) then f (b n) else 1 with ha
  have hapos : ∀ n, 0 < a n := by
    intro n
    simp only [ha]
    split_ifs with h' <;> [exact h'; exact one_pos]
  refine F.isInMDAGumbel_of_tendsto_mul (b := b) hapos fun x ↦ (key x).congr' ?_
  filter_upwards [hb.eventually hf] with n hn
  simp only [ha, hn, ↓reduceIte]
  ring_nf

/-- The explicit normalization in the auxiliary-function criterion for `x_F = +∞`: with
`b n = F^← (1 - 1 / n) = sInf {y | 1 - F y ≤ 1 / n}` one has `b n → ∞` and
`n * (1 - F (b n + x * f (b n))) → exp (-x)` for every `x`, i.e. one may take `a n = f (b n)`. -/
theorem tendsto_mul_one_sub_of_auxiliary_atTop (F : CumulativeDistributionFunction)
    (hF : ∀ x, F x < 1) {f : ℝ → ℝ} (hf : ∀ᶠ t in atTop, 0 < f t)
    (h : ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) atTop
      (𝓝 (Real.exp (-x)))) :
    Tendsto (fun n : ℕ ↦ sInf {y | 1 - F y ≤ 1 / (n : ℝ)}) atTop atTop ∧
    ∀ x, Tendsto (fun n : ℕ ↦ (n : ℝ) *
      (1 - F (sInf {y | 1 - F y ≤ 1 / (n : ℝ)} +
        x * f (sInf {y | 1 - F y ≤ 1 / (n : ℝ)})))) atTop (𝓝 (Real.exp (-x))) := by
  have gpos : ∀ x, 0 < 1 - F x := fun x ↦ by linarith [hF x]
  have hg0 : Tendsto (fun x ↦ 1 - F x) atTop (𝓝 0) := by
    simpa using (F.tendsto_atTop).const_sub 1
  have hsmall : ∀ M, ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < 1 - F M := fun M ↦
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds (gpos M))
  have hq : ∀ᶠ n : ℕ in atTop, 1 - F (sInf {y | 1 - F y ≤ 1 / (n : ℝ)}) ≤ 1 / n ∧
      ∀ y < sInf {y | 1 - F y ≤ 1 / (n : ℝ)}, 1 / (n : ℝ) < 1 - F y := by
    filter_upwards [hsmall 0, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < 1 / n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      positivity
    exact Gumbel.quantile_spec F.antitone_one_sub F.rightContinuous_one_sub
      ((hg0.eventually (gt_mem_nhds hn0)).exists.imp fun x hx ↦ hx.le) ⟨0, hn⟩
  have hb : Tendsto (fun n : ℕ ↦ sInf {y | 1 - F y ≤ 1 / (n : ℝ)}) atTop atTop := by
    refine Filter.tendsto_atTop.2 fun M ↦ ?_
    filter_upwards [hsmall M, hq] with n hn hqn
    by_contra hcon
    push Not at hcon
    have := F.antitone_one_sub hcon.le
    simp only at this
    linarith [hqn.1]
  exact ⟨hb, Gumbel.tendsto_mul_of_auxiliary (g := fun y ↦ 1 - F y) h hf
    (Eventually.of_forall gpos) hb hq⟩

/-- **Sufficiency via an auxiliary function, infinite right endpoint** ([dHF, Theorem 1.1.8],
[EKM, Theorem 3.3.26], [Resnick, Proposition 1.1]): if `F < 1` everywhere (i.e. `x_F = +∞`)
and there is an eventually positive function `f` with
`(1 - F (t + x * f t)) / (1 - F t) → exp (-x)` as `t → ∞` for every `x`, then `F` is in the
Gumbel domain of attraction. -/
theorem isInMDAGumbel_of_auxiliary_atTop (F : CumulativeDistributionFunction)
    (hF : ∀ x, F x < 1) {f : ℝ → ℝ} (hf : ∀ᶠ t in atTop, 0 < f t)
    (h : ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) atTop
      (𝓝 (Real.exp (-x)))) :
    F.IsInMDAGumbel := by
  have gpos : ∀ x, 0 < 1 - F x := fun x ↦ by linarith [hF x]
  have hg0 : Tendsto (fun x ↦ 1 - F x) atTop (𝓝 0) := by
    simpa using (F.tendsto_atTop).const_sub 1
  have hq : ∀ᶠ n : ℕ in atTop, 1 - F (sInf {y | 1 - F y ≤ 1 / (n : ℝ)}) ≤ 1 / n ∧
      ∀ y < sInf {y | 1 - F y ≤ 1 / (n : ℝ)}, 1 / (n : ℝ) < 1 - F y := by
    filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (gpos 0)), eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < 1 / n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      positivity
    exact Gumbel.quantile_spec F.antitone_one_sub F.rightContinuous_one_sub
      ((hg0.eventually (gt_mem_nhds hn0)).exists.imp fun x hx ↦ hx.le) ⟨0, hn⟩
  exact F.isInMDAGumbel_of_quantile hf (Eventually.of_forall hF) h
    (F.tendsto_mul_one_sub_of_auxiliary_atTop hF hf h).1 hq

/-- If `F < 1` on `(-∞, x_F)`, `F x_F = 1` and the auxiliary relation holds (at `x = 1`) as
`t ↑ x_F`, then `1 - F` is arbitrarily small to the left of `x_F` (i.e. `F` has no atom at
`x_F`). -/
private lemma exists_one_sub_lt_of_auxiliary_nhdsLT (F : CumulativeDistributionFunction)
    {xF : ℝ} (hlt : ∀ x < xF, F x < 1) (heq : F xF = 1) {f : ℝ → ℝ}
    (hf : ∀ᶠ t in 𝓝[<] xF, 0 < f t)
    (h1 : Tendsto (fun t ↦ (1 - F (t + 1 * f t)) / (1 - F t)) (𝓝[<] xF)
      (𝓝 (Real.exp (-1)))) {ε : ℝ} (hε : 0 < ε) :
    ∃ y < xF, 1 - F y < ε := by
  by_contra hcon
  push Not at hcon
  set S := (fun y ↦ 1 - F y) '' Iio xF with hS
  have hne : S.Nonempty := ⟨_, mem_image_of_mem _ (show xF - 1 < xF by linarith)⟩
  have hB : BddBelow S :=
    ⟨0, by rintro _ ⟨y, -, rfl⟩; simp only; linarith [F.apply_le_one y]⟩
  have hcε : ε ≤ sInf S := le_csInf hne (by rintro _ ⟨y, hy, rfl⟩; exact hcon y hy)
  have hcpos : 0 < sInf S := hε.trans_le hcε
  obtain ⟨_, ⟨y₀, hy₀, rfl⟩, hy₀c⟩ :=
    exists_lt_of_csInf_lt hne (show sInf S < 4 / 3 * sInf S by linarith)
  have hexp : Real.exp (-1) < 1 / 2 := by
    have h2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
      linarith
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    norm_num
    exact h2
  obtain ⟨t, ⟨ht1, ht2⟩, ht3, ht4⟩ := ((show ∀ᶠ t in 𝓝[<] xF, t ∈ Ioo y₀ xF from Ioo_mem_nhdsLT hy₀).and
    ((h1.eventually (Ioo_mem_nhds (Real.exp_pos (-1)) hexp)).and hf)).exists
  have hgt : 0 < 1 - F t := by linarith [hlt t ht2]
  obtain ⟨r1, r2⟩ := ht3
  rw [div_pos_iff_of_pos_right hgt] at r1
  rw [div_lt_iff₀ hgt] at r2
  have hlt' : t + 1 * f t < xF := by
    by_contra hcon'
    push Not at hcon'
    have h3 : F xF ≤ F (t + 1 * f t) := F.mono' hcon'
    rw [heq] at h3
    linarith [F.apply_le_one (t + 1 * f t)]
  have hc1 : sInf S ≤ 1 - F (t + 1 * f t) := csInf_le hB (mem_image_of_mem _ hlt')
  have hc2 : 1 - F t ≤ 1 - F y₀ := F.antitone_one_sub ht1.le
  simp only at hy₀c
  nlinarith

/-- **Sufficiency via an auxiliary function, finite right endpoint** ([dHF, Theorem 1.1.8],
[EKM, Theorem 3.3.26], [Resnick, Proposition 1.1]): if `x_F < ∞` is the right endpoint of `F`
(`F < 1` on `(-∞, x_F)` and `F x_F = 1`) and there is a function `f`, positive near `x_F`, with
`(1 - F (t + x * f t)) / (1 - F t) → exp (-x)` as `t ↑ x_F` for every `x`, then `F` is in the
Gumbel domain of attraction (with `b n = F^← (1 - 1 / n)` and `a n = f (b n)`). -/
theorem isInMDAGumbel_of_auxiliary_nhdsLT (F : CumulativeDistributionFunction) {xF : ℝ}
    (hlt : ∀ x < xF, F x < 1) (heq : F xF = 1) {f : ℝ → ℝ}
    (hf : ∀ᶠ t in 𝓝[<] xF, 0 < f t)
    (h : ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) (𝓝[<] xF)
      (𝓝 (Real.exp (-x)))) :
    F.IsInMDAGumbel := by
  have gpos : ∀ x < xF, 0 < 1 - F x := fun x hx ↦ by linarith [hlt x hx]
  have hq : ∀ᶠ n : ℕ in atTop, 1 - F (sInf {y | 1 - F y ≤ 1 / (n : ℝ)}) ≤ 1 / n ∧
      ∀ y < sInf {y | 1 - F y ≤ 1 / (n : ℝ)}, 1 / (n : ℝ) < 1 - F y := by
    filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (gpos (xF - 1) (by linarith)))] with n hn
    exact Gumbel.quantile_spec F.antitone_one_sub F.rightContinuous_one_sub
      ⟨xF, by rw [heq, sub_self]; positivity⟩ ⟨xF - 1, hn⟩
  have hlt' : ∀ᶠ n : ℕ in atTop, sInf {y | 1 - F y ≤ 1 / (n : ℝ)} < xF := by
    filter_upwards [hq, eventually_ge_atTop 1] with n hqn hn1
    have hn0 : (0 : ℝ) < 1 / n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      positivity
    obtain ⟨y, hy, hgy⟩ := F.exists_one_sub_lt_of_auxiliary_nhdsLT hlt heq hf (h 1) hn0
    by_contra hcon
    push Not at hcon
    have := hqn.2 y (hy.trans_le hcon)
    linarith
  have hb : Tendsto (fun n : ℕ ↦ sInf {y | 1 - F y ≤ 1 / (n : ℝ)}) atTop (𝓝[<] xF) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hlt'⟩
    rw [tendsto_order]
    refine ⟨fun l hl ↦ ?_, fun u hu ↦ ?_⟩
    · filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (gt_mem_nhds (gpos l hl)), hq] with n hn hqn
      by_contra hcon
      push Not at hcon
      have := F.antitone_one_sub hcon
      simp only at this
      linarith [hqn.1]
    · filter_upwards [hlt'] with n hn
      exact hn.trans hu
  exact F.isInMDAGumbel_of_quantile hf (eventually_nhdsWithin_of_forall fun t ht ↦ hlt t ht) h
    hb hq

/-! ### The von Mises condition -/

/-- A mean value theorem with an unordered pair of points of an order-connected set. -/
private lemma exists_eq_mul_sub_of_hasDerivAt {φ φ' : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hd : ∀ s ∈ S, HasDerivAt φ (φ' s) s) {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    ∃ ξ ∈ S, |ξ - a| ≤ |b - a| ∧ φ b - φ a = φ' ξ * (b - a) := by
  have hmem : ∀ u v, u ∈ S → v ∈ S → ∀ s ∈ Icc u v, s ∈ S := fun u v hu hv s hs ↦
    hS.out hu hv hs
  have hcont : ∀ u v, u ∈ S → v ∈ S → ContinuousOn φ (Icc u v) := fun u v hu hv s hs ↦
    (hd s (hmem u v hu hv s hs)).continuousAt.continuousWithinAt
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope φ φ' hab (hcont a b ha hb)
      fun s hs ↦ hd s (hmem a b ha hb s (Ioo_subset_Icc_self hs))
    refine ⟨ξ, hmem a b ha hb ξ (Ioo_subset_Icc_self hξ), ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hξ.1] : 0 < ξ - a), abs_of_pos (by linarith : 0 < b - a)]
      linarith [hξ.2]
    · rw [e, div_mul_cancel₀ _ (sub_ne_zero.2 hab.ne')]
  · exact ⟨a, ha, by simp, by simp⟩
  · obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope φ φ' hab (hcont b a hb ha)
      fun s hs ↦ hd s (hmem b a hb ha s (Ioo_subset_Icc_self hs))
    refine ⟨ξ, hmem b a hb ha ξ (Ioo_subset_Icc_self hξ), ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hξ.2] : ξ - a < 0), abs_of_neg (by linarith : b - a < 0)]
      linarith [hξ.1]
    · have : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
      rw [e]
      field_simp
      ring

/-- A Lipschitz bound from a bounded derivative on an order-connected set. -/
private lemma abs_sub_le_of_hasDerivAt {φ φ' : ℝ → ℝ} {S : Set ℝ} {ε : ℝ} (hS : S.OrdConnected)
    (hd : ∀ s ∈ S, HasDerivAt φ (φ' s) s) (hbd : ∀ s ∈ S, |φ' s| ≤ ε) {a b : ℝ} (ha : a ∈ S)
    (hb : b ∈ S) : |φ b - φ a| ≤ ε * |b - a| := by
  obtain ⟨ξ, hξ, -, e⟩ := exists_eq_mul_sub_of_hasDerivAt hS hd ha hb
  rw [e, abs_mul]
  exact mul_le_mul_of_nonneg_right (hbd ξ hξ) (abs_nonneg _)

/-- The tolerance used in the von Mises argument: for `η > 0` there is `ε > 0` with
`ε |x| ≤ 1 / 2` and `2 ε x ^ 2 < η`. -/
private lemma exists_vonMises_tolerance (x : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε * |x| ≤ 1 / 2 ∧ 2 * ε * x ^ 2 < η := by
  set ε := min (1 / (2 * (|x| + 1))) (η / (2 * (x ^ 2 + 1))) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε, hεpos, ?_, ?_⟩
  · have h1' : ε ≤ 1 / (2 * (|x| + 1)) := min_le_left _ _
    have : 1 / (2 * (|x| + 1)) * |x| ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) two_pos]
      linarith [abs_nonneg x]
    nlinarith [abs_nonneg x]
  · have h1' : ε ≤ η / (2 * (x ^ 2 + 1)) := min_le_right _ _
    have : 2 * (η / (2 * (x ^ 2 + 1))) * x ^ 2 < η := by
      rw [show 2 * (η / (2 * (x ^ 2 + 1))) * x ^ 2 = η * (x ^ 2 / (x ^ 2 + 1)) by
        field_simp]
      have : x ^ 2 / (x ^ 2 + 1) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      nlinarith
    nlinarith [sq_nonneg x]

/-- The common core of the von Mises argument: on an order-connected set `S` where
`(log g)' = -1 / f`, `f > 0` and `|f'| ≤ ε`, the increment `log g (t + x f t) - log g t` is
within `η` of `-x` whenever both `t` and `t + x f t` lie in `S`. -/
private lemma dist_log_sub_lt_of_vonMises {g f fd : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hφ : ∀ s ∈ S, HasDerivAt (fun t ↦ Real.log (g t)) (-1 / f s) s)
    (hfd : ∀ s ∈ S, HasDerivAt f (fd s) s) (hfpos : ∀ s ∈ S, 0 < f s) {ε x η : ℝ}
    (hεpos : 0 < ε) (hbd : ∀ s ∈ S, |fd s| ≤ ε) (hη : 0 < η) (hεx : ε * |x| ≤ 1 / 2)
    (hεη : 2 * ε * x ^ 2 < η) {t : ℝ} (ht : t ∈ S) (htx : t + x * f t ∈ S) :
    dist (Real.log (g (t + x * f t)) - Real.log (g t)) (-x) < η := by
  have hft := hfpos t ht
  obtain ⟨ξ, hξ, hξt, e⟩ := exists_eq_mul_sub_of_hasDerivAt hS hφ ht htx
  rw [add_sub_cancel_left] at e hξt
  rw [abs_mul, abs_of_pos hft] at hξt
  have hfξ_close : |f ξ - f t| ≤ ε * |x| * f t := by
    have := abs_sub_le_of_hasDerivAt hS hfd hbd ht hξ
    calc |f ξ - f t| ≤ ε * |ξ - t| := this
      _ ≤ ε * (|x| * f t) := mul_le_mul_of_nonneg_left hξt hεpos.le
      _ = ε * |x| * f t := by ring
  have hfξ : f t / 2 ≤ f ξ := by
    have : ε * |x| * f t ≤ 1 / 2 * f t := mul_le_mul_of_nonneg_right hεx hft.le
    linarith [neg_abs_le (f ξ - f t)]
  have hfξpos : 0 < f ξ := by linarith
  rw [Real.dist_eq, e, sub_neg_eq_add]
  have key : -1 / f ξ * (x * f t) + x = x * (f ξ - f t) / f ξ := by
    field_simp
    ring
  rw [key, abs_div, abs_mul, abs_of_pos hfξpos, div_lt_iff₀ hfξpos]
  calc |x| * |f ξ - f t| ≤ |x| * (ε * |x| * f t) :=
        mul_le_mul_of_nonneg_left hfξ_close (abs_nonneg x)
    _ = ε * x ^ 2 * f t := by rw [← sq_abs x]; ring
    _ < η * (f t / 2) := by nlinarith
    _ ≤ η * f ξ := mul_le_mul_of_nonneg_left hfξ hη.le

/-- **The von Mises condition** ([dHF, Theorem 1.1.8], [EKM, Theorem 3.3.27],
[Resnick, Proposition 1.1]): if `F` is twice differentiable on `(z, ∞)` with `F' = F₁ > 0`,
`F'' = F₂` and `(1 - F) F'' / (F') ^ 2 → -1` at `+∞`, then `F < 1` everywhere and
`f = (1 - F) / F'` is an auxiliary function:
`(1 - F (t + x * f t)) / (1 - F t) → exp (-x)` as `t → ∞`, for every `x`. -/
theorem tendsto_auxiliary_of_vonMises (F : CumulativeDistributionFunction) {z : ℝ}
    {F₁ F₂ : ℝ → ℝ} (h1 : ∀ x > z, HasDerivAt F (F₁ x) x)
    (h2 : ∀ x > z, HasDerivAt F₁ (F₂ x) x) (hpos : ∀ x > z, 0 < F₁ x)
    (hvm : Tendsto (fun t ↦ (1 - F t) * F₂ t / F₁ t ^ 2) atTop (𝓝 (-1))) :
    (∀ x, F x < 1) ∧ ∀ x, Tendsto (fun t ↦ (1 - F (t + x * ((1 - F t) / F₁ t))) / (1 - F t))
      atTop (𝓝 (Real.exp (-x))) := by
  have hF : ∀ x, F x < 1 := by
    intro x
    set y := max x (z + 1) with hy
    have hzy : z < y := lt_max_of_lt_right (by linarith)
    obtain ⟨ξ, hξ, -, e⟩ := exists_eq_mul_sub_of_hasDerivAt ordConnected_Ioi h1 hzy
      (show z < y + 1 by linarith)
    rw [show y + 1 - y = 1 by ring, mul_one] at e
    have := hpos ξ hξ
    have := F.mono' (le_max_left x (z + 1))
    have := F.apply_le_one (y + 1)
    linarith
  refine ⟨hF, fun x ↦ ?_⟩
  set g : ℝ → ℝ := fun t ↦ 1 - F t with hgdef
  have gpos : ∀ t, 0 < g t := fun t ↦ by simp only [hgdef]; linarith [hF t]
  set f : ℝ → ℝ := fun t ↦ g t / F₁ t with hfdef
  set fd : ℝ → ℝ := fun t ↦ ((0 - F₁ t) * F₁ t - g t * F₂ t) / F₁ t ^ 2 with hfd
  have hfderiv : ∀ s > z, HasDerivAt f (fd s) s := fun s hs ↦
    ((hasDerivAt_const s 1).sub (h1 s hs)).fun_div (h2 s hs) (hpos s hs).ne'
  have hfd0 : Tendsto fd atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (-1 : ℝ))).sub hvm
    rw [sub_neg_eq_add, neg_add_cancel] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop z] with s hs
    have := (hpos s hs).ne'
    simp only [hfd, hgdef]
    field_simp
    ring
  have hφ : ∀ s > z, HasDerivAt (fun t ↦ Real.log (g t)) (-1 / f s) s := by
    intro s hs
    have := ((hasDerivAt_const s (1 : ℝ)).sub (h1 s hs)).log (gpos s).ne'
    convert this using 1
    have := (hpos s hs).ne'
    have := (gpos s).ne'
    simp only [hfdef, hgdef, Pi.sub_apply]
    field_simp
    ring
  have hfpos : ∀ s > z, 0 < f s := fun s hs ↦ div_pos (gpos s) (hpos s hs)
  have hD : Tendsto (fun t ↦ Real.log (g (t + x * f t)) - Real.log (g t)) atTop (𝓝 (-x)) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨ε, hεpos, hεx, hεη⟩ := exists_vonMises_tolerance x hη
    obtain ⟨T, hT⟩ := eventually_atTop.1
      (hfd0.eventually (Icc_mem_nhds (neg_lt_zero.2 hεpos) hεpos))
    set T₀ := max T z with hT₀
    have hT₀z : ∀ s > T₀, z < s := fun s hs ↦ lt_of_le_of_lt (le_max_right _ _) hs
    have hbd : ∀ s ∈ Ioi T₀, |fd s| ≤ ε := fun s hs ↦
      abs_le.2 (hT s (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs)))
    have hd₀ : ∀ s ∈ Ioi T₀, HasDerivAt f (fd s) s := fun s hs ↦ hfderiv s (hT₀z s hs)
    have hlip : ∀ a b, T₀ < a → T₀ < b → |f b - f a| ≤ ε * |b - a| :=
      fun a b ha hb ↦ abs_sub_le_of_hasDerivAt ordConnected_Ioi hd₀ hbd ha hb
    set T₁ := T₀ + 1 with hT₁
    have hfT₁ : 0 < f T₁ := hfpos T₁ (hT₀z T₁ (by linarith))
    filter_upwards [eventually_gt_atTop (T₁ + 2 * |x| * f T₁)] with t ht
    have htT : T₁ < t := by nlinarith [abs_nonneg x]
    have hft : 0 < f t := hfpos t (hT₀z t (by linarith))
    have hgrow : f t ≤ f T₁ + ε * (t - T₁) := by
      have := hlip T₁ t (by linarith) (by linarith)
      rw [abs_of_pos (by linarith : 0 < t - T₁)] at this
      linarith [le_abs_self (f t - f T₁)]
    have hxf : -(|x| * f t) ≤ x * f t := by nlinarith [neg_abs_le x]
    have hTx : T₀ < t + x * f t := by
      have e1 : |x| * f t ≤ |x| * (f T₁ + ε * (t - T₁)) :=
        mul_le_mul_of_nonneg_left hgrow (abs_nonneg x)
      have e2 : ε * |x| * (t - T₁) ≤ 1 / 2 * (t - T₁) :=
        mul_le_mul_of_nonneg_right hεx (by linarith)
      nlinarith
    exact dist_log_sub_lt_of_vonMises ordConnected_Ioi (fun s hs ↦ hφ s (hT₀z s hs)) hd₀
      (fun s hs ↦ hfpos s (hT₀z s hs)) hεpos hbd hη hεx hεη (show T₀ < t by linarith) hTx
  have := (Real.continuous_exp.tendsto _).comp hD
  refine this.congr fun t ↦ ?_
  simp only [Function.comp_apply]
  rw [Real.exp_sub, Real.exp_log (gpos _), Real.exp_log (gpos _)]

/-- **The von Mises condition implies the Gumbel domain of attraction** ([EKM, Theorem 3.3.27],
[dHF, Theorem 1.1.8]): if `F` is twice differentiable on `(z, ∞)` with `F' > 0` there and
`(1 - F) F'' / (F') ^ 2 → -1` at `+∞`, then `F` is in the Gumbel domain of attraction. -/
theorem isInMDAGumbel_of_vonMises (F : CumulativeDistributionFunction) {z : ℝ}
    {F₁ F₂ : ℝ → ℝ} (h1 : ∀ x > z, HasDerivAt F (F₁ x) x)
    (h2 : ∀ x > z, HasDerivAt F₁ (F₂ x) x) (hpos : ∀ x > z, 0 < F₁ x)
    (hvm : Tendsto (fun t ↦ (1 - F t) * F₂ t / F₁ t ^ 2) atTop (𝓝 (-1))) :
    F.IsInMDAGumbel := by
  obtain ⟨hF, h⟩ := F.tendsto_auxiliary_of_vonMises h1 h2 hpos hvm
  refine F.isInMDAGumbel_of_auxiliary_atTop hF (f := fun t ↦ (1 - F t) / F₁ t) ?_ h
  filter_upwards [eventually_gt_atTop z] with t ht
  exact div_pos (by linarith [hF t]) (hpos t ht)

/-- **The von Mises condition, finite right endpoint** ([dHF, Theorem 1.1.8],
[EKM, Theorem 3.3.27], [Resnick, Proposition 1.1]): let `z < x_F`, and suppose `F` is twice
differentiable on `(z, x_F)` with `F' = F₁ > 0` and `F'' = F₂` there, `F (t) → 1` as `t ↑ x_F`
(so `F` has no atom at `x_F`), and `(1 - F) F'' / (F') ^ 2 → -1` as `t ↑ x_F`. Then `x_F` is the
right endpoint of `F` (`F < 1` on `(-∞, x_F)` and `F x_F = 1`) and `f = (1 - F) / F'` is an
auxiliary function: `(1 - F (t + x * f t)) / (1 - F t) → exp (-x)` as `t ↑ x_F`, for every `x`.

The key extra step compared with `x_F = ∞` is that `f (t) = o(x_F - t)`, which keeps
`t + x * f t` to the left of `x_F`. (Without the continuity of `F` at `x_F` the statement fails:
`1 - F (t) = exp (-t)` on `(0, 1)` with an atom at `1` satisfies the other hypotheses.) -/
theorem tendsto_auxiliary_of_vonMises_nhdsLT (F : CumulativeDistributionFunction) {z xF : ℝ}
    (hz : z < xF) {F₁ F₂ : ℝ → ℝ} (h1 : ∀ x ∈ Ioo z xF, HasDerivAt F (F₁ x) x)
    (h2 : ∀ x ∈ Ioo z xF, HasDerivAt F₁ (F₂ x) x) (hpos : ∀ x ∈ Ioo z xF, 0 < F₁ x)
    (hF1 : Tendsto F (𝓝[<] xF) (𝓝 1))
    (hvm : Tendsto (fun t ↦ (1 - F t) * F₂ t / F₁ t ^ 2) (𝓝[<] xF) (𝓝 (-1))) :
    (∀ x < xF, F x < 1) ∧ F xF = 1 ∧
      ∀ x, Tendsto (fun t ↦ (1 - F (t + x * ((1 - F t) / F₁ t))) / (1 - F t)) (𝓝[<] xF)
        (𝓝 (Real.exp (-x))) := by
  have hF : ∀ x < xF, F x < 1 := by
    intro x hx
    set y := max x ((z + xF) / 2) with hy
    have hzy : y ∈ Ioo z xF :=
      ⟨lt_max_of_lt_right (by linarith), max_lt hx (by linarith)⟩
    have hy' : (y + xF) / 2 ∈ Ioo z xF := ⟨by linarith [hzy.1], by linarith [hzy.2]⟩
    obtain ⟨ξ, hξ, -, e⟩ := exists_eq_mul_sub_of_hasDerivAt ordConnected_Ioo h1 hzy hy'
    have := mul_pos (hpos ξ hξ) (show 0 < (y + xF) / 2 - y by linarith [hzy.2])
    have := F.mono' (le_max_left x ((z + xF) / 2))
    have := F.apply_le_one ((y + xF) / 2)
    linarith
  have heq : F xF = 1 :=
    le_antisymm (F.apply_le_one xF) (le_of_tendsto hF1
      (eventually_nhdsWithin_of_forall (s := Iio xF) fun t ht ↦ F.mono' (le_of_lt ht)))
  refine ⟨hF, heq, fun x ↦ ?_⟩
  set S := Ioo z xF with hSdef
  set g : ℝ → ℝ := fun t ↦ 1 - F t with hgdef
  have gpos : ∀ t < xF, 0 < g t := fun t ht ↦ by simp only [hgdef]; linarith [hF t ht]
  have hg0 : Tendsto g (𝓝[<] xF) (𝓝 0) := by
    have := hF1.const_sub 1
    rwa [sub_self] at this
  set f : ℝ → ℝ := fun t ↦ g t / F₁ t with hfdef
  set fd : ℝ → ℝ := fun t ↦ ((0 - F₁ t) * F₁ t - g t * F₂ t) / F₁ t ^ 2 with hfd
  have hfderiv : ∀ s ∈ S, HasDerivAt f (fd s) s := fun s hs ↦
    ((hasDerivAt_const s 1).sub (h1 s hs)).fun_div (h2 s hs) (hpos s hs).ne'
  have hfd0 : Tendsto fd (𝓝[<] xF) (𝓝 0) := by
    have := (tendsto_const_nhds (x := (-1 : ℝ))).sub hvm
    rw [sub_neg_eq_add, neg_add_cancel] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hz] with s hs
    have := (hpos s hs).ne'
    simp only [hfd, hgdef]
    field_simp
    ring
  have hφ : ∀ s ∈ S, HasDerivAt (fun t ↦ Real.log (g t)) (-1 / f s) s := by
    intro s hs
    have := ((hasDerivAt_const s (1 : ℝ)).sub (h1 s hs)).log (gpos s hs.2).ne'
    convert this using 1
    have := (hpos s hs).ne'
    have := (gpos s hs.2).ne'
    simp only [hfdef, hgdef, Pi.sub_apply]
    field_simp
    ring
  have hfpos : ∀ s ∈ S, 0 < f s := fun s hs ↦ div_pos (gpos s hs.2) (hpos s hs)
  -- Near `x_F`, `|f'| ≤ ε` and `f t ≤ ε (x_F - t)`.
  have hloc : ∀ ε > 0, ∃ T₀ < xF, z ≤ T₀ ∧ (∀ s ∈ Ioo T₀ xF, |fd s| ≤ ε) ∧
      ∀ s ∈ Ioo T₀ xF, f s ≤ ε * (xF - s) := by
    intro ε hεpos
    obtain ⟨T, hTx, hT⟩ := (nhdsLT_basis xF).eventually_iff.1
      (hfd0.eventually (Icc_mem_nhds (neg_lt_zero.2 hεpos) hεpos))
    set T₀ := max T z with hT₀
    have hT₀x : T₀ < xF := max_lt hTx hz
    have hsub : ∀ s ∈ Ioo T₀ xF, s ∈ S := fun s hs ↦
      ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, hs.2⟩
    have hbd : ∀ s ∈ Ioo T₀ xF, |fd s| ≤ ε := fun s hs ↦
      abs_le.2 (hT ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩)
    refine ⟨T₀, hT₀x, le_max_right _ _, hbd, fun t ht ↦ ?_⟩
    by_contra hcon
    push Not at hcon
    set δ := f t - ε * (xF - t) with hδ
    have hδpos : 0 < δ := by linarith
    -- `f ≥ δ` on `(t, x_F)`, hence `g` is bounded below there, contradicting `g → 0`.
    have hfδ : ∀ s ∈ Ioo t xF, δ ≤ f s := by
      intro s hs
      have hs' : s ∈ Ioo T₀ xF := ⟨ht.1.trans hs.1, hs.2⟩
      have := abs_sub_le_of_hasDerivAt ordConnected_Ioo (fun u hu ↦ hfderiv u (hsub u hu))
        hbd ht hs'
      rw [abs_of_pos (by linarith [hs.1] : 0 < s - t)] at this
      have := neg_abs_le (f s - f t)
      nlinarith [hs.2]
    have hglow : ∀ s ∈ Ioo t xF, Real.log (g t) - (xF - t) / δ ≤ Real.log (g s) := by
      intro s hs
      have hcont : ContinuousOn (fun u ↦ Real.log (g u)) (Icc t s) := fun u hu ↦
        (hφ u (hsub u ⟨lt_of_lt_of_le ht.1 hu.1, lt_of_le_of_lt hu.2 hs.2⟩)).continuousAt
          |>.continuousWithinAt
      obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope (fun u ↦ Real.log (g u))
        (fun u ↦ -1 / f u) hs.1 hcont fun u hu ↦
          hφ u (hsub u ⟨ht.1.trans hu.1, hu.2.trans hs.2⟩)
      have hfξ : δ ≤ f ξ := hfδ ξ ⟨hξ.1, hξ.2.trans hs.2⟩
      have hst : 0 < s - t := by linarith [hs.1]
      rw [eq_div_iff hst.ne'] at e
      have h1ξ : 1 / f ξ ≤ 1 / δ := one_div_le_one_div_of_le hδpos hfξ
      have : 1 / f ξ * (s - t) ≤ 1 / δ * (xF - t) :=
        mul_le_mul h1ξ (by linarith [hs.2]) hst.le (by positivity)
      rw [div_eq_mul_one_div (xF - t), mul_comm (xF - t)]
      have e' : Real.log (g s) - Real.log (g t) = -(1 / f ξ * (s - t)) := by
        rw [← e]; ring
      linarith
    obtain ⟨s, hs, hgs⟩ := ((show ∀ᶠ s in 𝓝[<] xF, s ∈ Ioo t xF from Ioo_mem_nhdsLT ht.2).and
      (hg0.eventually (gt_mem_nhds (Real.exp_pos (Real.log (g t) - (xF - t) / δ))))).exists
    have := Real.exp_le_exp.2 (hglow s hs)
    rw [Real.exp_log (gpos s hs.2)] at this
    linarith
  -- Eventually `t + x f t < x_F`.
  have hin : ∀ᶠ t in 𝓝[<] xF, t + x * f t < xF := by
    obtain ⟨T₀, hT₀x, hzT₀, -, hsmall⟩ := hloc (1 / (2 * (|x| + 1))) (by positivity)
    filter_upwards [Ioo_mem_nhdsLT hT₀x] with t ht
    have h1 := hsmall t ht
    have hft : 0 < f t := hfpos t ⟨lt_of_le_of_lt hzT₀ ht.1, ht.2⟩
    have : |x| * f t ≤ |x| * (1 / (2 * (|x| + 1)) * (xF - t)) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
    have : |x| * (1 / (2 * (|x| + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]
      linarith [abs_nonneg x]
    have := le_abs_self x
    nlinarith [ht.2, abs_nonneg x]
  have hD : Tendsto (fun t ↦ Real.log (g (t + x * f t)) - Real.log (g t)) (𝓝[<] xF)
      (𝓝 (-x)) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨ε, hεpos, hεx, hεη⟩ := exists_vonMises_tolerance x hη
    obtain ⟨T₀, hT₀x, hzT₀, hbd, hsmall⟩ := hloc ε hεpos
    have hsub : ∀ s ∈ Ioo T₀ xF, s ∈ S := fun s hs ↦ ⟨lt_of_le_of_lt hzT₀ hs.1, hs.2⟩
    filter_upwards [Ioo_mem_nhdsLT (show (2 * T₀ + xF) / 3 < xF by linarith)] with t ht
    have htS : t ∈ Ioo T₀ xF := ⟨by linarith [ht.1], ht.2⟩
    have hft : 0 < f t := hfpos t (hsub t htS)
    have e1 : |x| * f t ≤ |x| * (ε * (xF - t)) :=
      mul_le_mul_of_nonneg_left (hsmall t htS) (abs_nonneg x)
    have e2 : ε * |x| * (xF - t) ≤ 1 / 2 * (xF - t) :=
      mul_le_mul_of_nonneg_right hεx (by linarith [ht.2])
    have hxf : |x * f t| ≤ (xF - t) / 2 := by
      rw [abs_mul, abs_of_pos hft]; nlinarith
    have htx : t + x * f t ∈ Ioo T₀ xF := by
      have := abs_le.1 hxf
      constructor <;> linarith [ht.1, ht.2]
    exact dist_log_sub_lt_of_vonMises ordConnected_Ioo (fun s hs ↦ hφ s (hsub s hs))
      (fun s hs ↦ hfderiv s (hsub s hs)) (fun s hs ↦ hfpos s (hsub s hs)) hεpos hbd hη hεx
      hεη htS htx
  have := (Real.continuous_exp.tendsto _).comp hD
  refine this.congr' ?_
  filter_upwards [hin, self_mem_nhdsWithin] with t ht ht'
  simp only [Function.comp_apply]
  rw [Real.exp_sub, Real.exp_log (gpos _ ht), Real.exp_log (gpos _ ht')]

/-- **The von Mises condition implies the Gumbel domain of attraction, finite right endpoint**
([EKM, Theorem 3.3.27], [dHF, Theorem 1.1.8]): if `z < x_F`, `F` is twice differentiable on
`(z, x_F)` with `F' > 0` there, `F (t) → 1` as `t ↑ x_F` and `(1 - F) F'' / (F') ^ 2 → -1` as
`t ↑ x_F`, then `F` is in the Gumbel domain of attraction. -/
theorem isInMDAGumbel_of_vonMises_nhdsLT (F : CumulativeDistributionFunction) {z xF : ℝ}
    (hz : z < xF) {F₁ F₂ : ℝ → ℝ} (h1 : ∀ x ∈ Ioo z xF, HasDerivAt F (F₁ x) x)
    (h2 : ∀ x ∈ Ioo z xF, HasDerivAt F₁ (F₂ x) x) (hpos : ∀ x ∈ Ioo z xF, 0 < F₁ x)
    (hF1 : Tendsto F (𝓝[<] xF) (𝓝 1))
    (hvm : Tendsto (fun t ↦ (1 - F t) * F₂ t / F₁ t ^ 2) (𝓝[<] xF) (𝓝 (-1))) :
    F.IsInMDAGumbel := by
  obtain ⟨hF, heq, h⟩ := F.tendsto_auxiliary_of_vonMises_nhdsLT hz h1 h2 hpos hF1 hvm
  refine F.isInMDAGumbel_of_auxiliary_nhdsLT hF heq (f := fun t ↦ (1 - F t) / F₁ t) ?_ h
  filter_upwards [Ioo_mem_nhdsLT hz] with t ht
  exact div_pos (by linarith [hF t ht.2]) (hpos t ht)


/-! ### Examples -/

/-- The standard exponential c.d.f. `x ↦ 1 - exp (-x)` for `x ≥ 0` (and `0` for `x < 0`). -/
noncomputable def standardExponentialCDF : CumulativeDistributionFunction where
  toFun x := max 0 (1 - Real.exp (-x))
  mono' := fun x y hxy ↦ max_le_max le_rfl (by gcongr)
  right_continuous' := fun x ↦ (continuous_const.max
    (continuous_const.sub (Real.continuous_exp.comp continuous_neg))).continuousWithinAt
  tendsto_atTop := by
    have h : Tendsto (fun x : ℝ ↦ 1 - Real.exp (-x)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine (max_eq_right ?_).symm
    have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  tendsto_atBot := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot 0] with x hx
    refine (max_eq_left ?_).symm
    have := Real.add_one_le_exp (-x)
    linarith

lemma standardExponentialCDF_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    standardExponentialCDF x = 1 - Real.exp (-x) := by
  refine max_eq_right ?_
  have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

lemma standardExponentialCDF_apply_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    standardExponentialCDF x = 0 := by
  refine max_eq_left ?_
  have := Real.add_one_le_exp (-x)
  linarith

/-- The standard exponential distribution is in the Gumbel domain of attraction (via the von
Mises condition, `(1 - F) F'' / (F') ^ 2 = -1` on `(0, ∞)`). -/
theorem isInMDAGumbel_standardExponentialCDF : standardExponentialCDF.IsInMDAGumbel := by
  have hE : ∀ y, 0 < y → standardExponentialCDF y = 1 - Real.exp (-y) :=
    fun y hy ↦ standardExponentialCDF_apply_of_nonneg hy.le
  refine standardExponentialCDF.isInMDAGumbel_of_vonMises (z := 0)
    (F₁ := fun x ↦ Real.exp (-x)) (F₂ := fun x ↦ -Real.exp (-x)) (fun x hx ↦ ?_)
    (fun x _ ↦ ?_) (fun x _ ↦ Real.exp_pos _) ?_
  · have h : HasDerivAt (fun y ↦ 1 - Real.exp (-y)) (Real.exp (-x)) x := by
      have := ((hasDerivAt_neg x).exp).const_sub 1
      convert this using 1
      ring
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact hE y hy
  · have := (hasDerivAt_neg x).exp
    convert this using 1
    ring
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [hE t ht]
    have := (Real.exp_pos (-t)).ne'
    field_simp
    ring

/-- The standard Gumbel distribution is in its own domain of attraction: with `a n = 1` and
`b n = log n`, `Λ (x + log n) ^ n = Λ x` for `n ≥ 1`. -/
theorem isInMDAGumbel_standardGumbelCDF : standardGumbelCDF.IsInMDAGumbel := by
  refine ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs one_pos (Real.log n))⁻¹, fun x ↦ ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have happ : ((AffineIncrEquiv.mkOfCoefs one_pos (Real.log n))⁻¹ • standardGumbelCDF) x =
      standardGumbelCDF (1 * x + Real.log n) := by simp
  rw [happ, standardGumbelCDF_apply_eq, standardGumbelCDF_apply_eq, ← Real.exp_nat_mul,
    one_mul, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hn']
  congr 1
  field_simp

private lemma exp_one_mul_expNegInvGlue_one_sub {x : ℝ} (hx : x < 1) :
    Real.exp 1 * expNegInvGlue (1 - x) = Real.exp (1 - (1 - x)⁻¹) := by
  simp only [expNegInvGlue, not_le.2 (by linarith : (0 : ℝ) < 1 - x), ↓reduceIte,
    ← Real.exp_add]
  congr 1

/-- A distribution with finite right endpoint `x_F = 1` in the Gumbel domain of attraction:
`F x = 1 - exp (-x / (1 - x)) = 1 - exp (1 - 1 / (1 - x))` for `0 ≤ x < 1`, `F x = 0` for
`x < 0` and `F x = 1` for `x ≥ 1`. -/
noncomputable def expNegInvCDF : CumulativeDistributionFunction where
  toFun x := max 0 (1 - Real.exp 1 * expNegInvGlue (1 - x))
  mono' := fun x y hxy ↦ max_le_max le_rfl (sub_le_sub_left (mul_le_mul_of_nonneg_left
    (expNegInvGlue.monotone (by linarith)) (Real.exp_pos 1).le) 1)
  right_continuous' := fun x ↦ (continuous_const.max (continuous_const.sub (continuous_const.mul
    ((expNegInvGlue.contDiff (n := 0)).continuous.comp
      (continuous_const.sub continuous_id))))).continuousWithinAt
  tendsto_atTop := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [expNegInvGlue.zero_of_nonpos (by linarith), mul_zero, sub_zero, max_eq_right zero_le_one]
  tendsto_atBot := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot 0] with x hx
    refine (max_eq_left ?_).symm
    rw [exp_one_mul_expNegInvGlue_one_sub (by linarith)]
    have : (1 - x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have := Real.add_one_le_exp (1 - (1 - x)⁻¹)
    linarith

lemma expNegInvCDF_apply_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    expNegInvCDF x = 1 - Real.exp (1 - (1 - x)⁻¹) := by
  change max 0 (1 - Real.exp 1 * expNegInvGlue (1 - x)) = _
  rw [exp_one_mul_expNegInvGlue_one_sub hx.2]
  refine max_eq_right ?_
  have : 1 < (1 - x)⁻¹ := one_lt_inv₀ (by linarith [hx.2]) |>.2 (by linarith [hx.1])
  have := Real.exp_lt_one_iff.2 (show 1 - (1 - x)⁻¹ < 0 by linarith)
  linarith

/-- The distribution `F x = 1 - exp (-x / (1 - x))` on `[0, 1)` (right endpoint `x_F = 1`) is in
the Gumbel domain of attraction, via the finite-endpoint von Mises condition:
`(1 - F) F'' / (F') ^ 2 = 2 (1 - x) - 1 → -1` as `x ↑ 1`. -/
theorem isInMDAGumbel_expNegInvCDF : expNegInvCDF.IsInMDAGumbel := by
  set G : ℝ → ℝ := fun x ↦ Real.exp (1 - (1 - x)⁻¹) with hG
  have hGd : ∀ x < 1, HasDerivAt G (-(G x / (1 - x) ^ 2)) x := by
    intro x hx
    have hx' : 1 - x ≠ 0 := by linarith
    have := ((((hasDerivAt_id x).const_sub 1).inv hx').const_sub 1).exp
    convert this using 1
    · rfl
    · show -(G x / (1 - x) ^ 2) = Real.exp (1 - (1 - x)⁻¹) * -(- -1 / (1 - x) ^ 2)
      simp only [hG]
      ring
  have hE : ∀ x ∈ Ioo (0 : ℝ) 1, expNegInvCDF x = 1 - G x :=
    fun x hx ↦ expNegInvCDF_apply_of_mem_Ioo hx
  refine expNegInvCDF.isInMDAGumbel_of_vonMises_nhdsLT (z := 0) (xF := 1) one_pos
    (F₁ := fun x ↦ G x / (1 - x) ^ 2) (F₂ := fun x ↦ G x * (2 * (1 - x) - 1) / (1 - x) ^ 4)
    (fun x hx ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ ?_) ?_ ?_
  · have h : HasDerivAt (fun y ↦ 1 - G y) (G x / (1 - x) ^ 2) x := by
      simpa using (hGd x hx.2).const_sub 1
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hE y hy
  · have hx' : 1 - x ≠ 0 := by linarith [hx.2]
    have := (hGd x hx.2).div (((hasDerivAt_id x).const_sub 1).pow 2) (pow_ne_zero 2 hx')
    convert this using 1
    · rfl
    · simp only [id, Pi.pow_apply]
      field_simp
      ring
  · have : 0 < 1 - x := by linarith [hx.2]
    exact div_pos (Real.exp_pos _) (by positivity)
  · have hc : Continuous (fun x ↦ max 0 (1 - Real.exp 1 * expNegInvGlue (1 - x))) :=
      continuous_const.max (continuous_const.sub (continuous_const.mul
        ((expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_const.sub continuous_id))))
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simp only [sub_self, expNegInvGlue.zero, mul_zero, sub_zero,
      max_eq_right zero_le_one] at this
    exact this
  · have hc : Tendsto (fun t : ℝ ↦ 2 * (1 - t) - 1) (𝓝[<] 1) (𝓝 (2 * (1 - 1) - 1)) :=
      ((continuous_const.mul (continuous_const.sub continuous_id)).sub
        continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [show (2 : ℝ) * (1 - 1) - 1 = -1 by norm_num] at hc
    refine hc.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT one_pos] with t ht
    rw [hE t ht]
    have : 1 - t ≠ 0 := by linarith [ht.2]
    have := (Real.exp_pos (1 - (1 - t)⁻¹)).ne'
    simp only [hG]
    field_simp
    ring

end CumulativeDistributionFunction
