/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ExtremeValueDistribution
import ExtremeValueTheory.LimitRelationManipulation
import ExtremeValueTheory.RegularVariation.Karamata

/-!
# Gnedenko's theorem: the Fréchet maximum domain of attraction

Let `F` be a c.d.f. and `α > 0`. We prove that `F` is in the maximum domain of attraction of the
standard Fréchet distribution `Φ_α(x) = exp (-x ^ (-α))` (`x > 0`), i.e. there are orientation
preserving affine maps `A n` with `((A n • F) x) ^ n → Φ_α x` for all `x`, if and only if the
tail `1 - F` is regularly varying at `+∞` with index `-α`.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 1.2.1 [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Proposition 1.11 [Resnick].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Theorem 3.3.7 [EKM].

## Main definitions and results

* `CumulativeDistributionFunction.IsInMDAFrechet F hα`: `F` is in the maximum domain of
  attraction of `standardFrechetCDF hα` (parametrized by the tail index `α`, i.e.
  `standardFrechetCDF hα x = exp (-x ^ (-α))` for `x > 0`).
* `CumulativeDistributionFunction.isInMDAFrechet_iff`: Gnedenko's characterization.
* `ExtremeValueTheory.Frechet.exists_tendsto_mul_of_isRegularlyVarying` and
  `ExtremeValueTheory.Frechet.isRegularlyVarying_of_tendsto_mul_affine`: the analytic cores
  of the two directions, stated for an antitone function `g` (the tail `1 - F`).

## Proof sketch

Sufficiency: with the quantile-type constants `a n = inf {x | 1 - F x ≤ 1 / n}` one has
`n (1 - F (a n)) → 1` (right continuity gives `≤ 1`, regular variation at `c * a n`, `c < 1`,
gives the lower bound), hence `n (1 - F (a n * x)) → x ^ (-α)`, and the limit relation for
maxima follows from `tfae_ev_limit_relation`. For `x ≤ 0` we use `F (a n * x) ≤ F 0 < 1`.

Necessity: writing `(A n)⁻¹ x = a n * x + b n`, we get `n (1 - F (a n * y + b n)) → y ^ (-α)`
for `y > 0`. Comparing the levels `t` and `2 t` (with `a t = a ⌊t⌋₊`) by monotonicity gives
`a (2 t) ~ 2 ^ (1 / α) a t` and `b (2 t) - b t = o (a t)`; summing along dyadic chains yields
`a → ∞` and `b n / a n → 0`. Hence `n (1 - F (a n * x)) → x ^ (-α)`, and a sandwich with
`a (N t) ≤ t < a (N t + 1)` (`N t = sup {n | a n ≤ t}`) gives regular variation.
-/

open Filter Topology Set

namespace ExtremeValueTheory

namespace Frechet

/-! ### Sufficiency: regular variation gives scaling constants -/

/-- If `g` is antitone, right-continuous, tends to `0` at `+∞` and is regularly varying with
index `-α`, then there are positive constants `a n` with `n * g (a n * x) → x ^ (-α)` for all
`x > 0`. -/
theorem exists_tendsto_mul_of_isRegularlyVarying {g : ℝ → ℝ} (hg : Antitone g)
    (hgr : ∀ x, ContinuousWithinAt g (Ici x) x) (hg0 : Tendsto g atTop (𝓝 0)) {α : ℝ}
    (hRV : IsRegularlyVarying g (-α)) :
    ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧
      ∀ x > 0, Tendsto (fun n : ℕ ↦ (n : ℝ) * g (a n * x)) atTop (𝓝 (x ^ (-α))) := by
  have gpos : ∀ x, 0 < g x := IsRegularlyVarying.pos_of_antitone hg hRV.1
  set S : ℕ → Set ℝ := fun n ↦ {x | g x ≤ 1 / n} with hS
  set s : ℕ → ℝ := fun n ↦ sInf (S n) with hs
  have hE : ∀ M, ∀ᶠ n : ℕ in atTop, (S n).Nonempty ∧ ∀ x ∈ S n, M < x := by
    intro M
    filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (gpos M)), eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < 1 / n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      positivity
    refine ⟨(hg0.eventually (gt_mem_nhds hn0)).exists.imp fun x hx ↦ hx.le, fun x hx ↦ ?_⟩
    by_contra hcon
    push Not at hcon
    have := hg hcon
    simp only [hS, mem_ofPred_eq] at hx
    linarith
  have hsM : ∀ M, ∀ᶠ n : ℕ in atTop, M ≤ s n := by
    intro M
    filter_upwards [hE M] with n hn
    exact le_csInf hn.1 fun x hx ↦ (hn.2 x hx).le
  have hstop : Tendsto s atTop atTop := tendsto_atTop.2 hsM
  -- `g (s n) ≤ 1 / n`
  have hP2 : ∀ᶠ n : ℕ in atTop, g (s n) ≤ 1 / n := by
    filter_upwards [hE 0] with n hn
    have hbdd : BddBelow (S n) := ⟨0, fun x hx ↦ (hn.2 x hx).le⟩
    have hlim : Tendsto g (𝓝[>] (s n)) (𝓝 (g (s n))) :=
      (hgr (s n)).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun x hx ↦ ?_)
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hn.1 (show sInf (S n) < x from hx)
    exact (hg hyx.le).trans hy
  -- `1 / n < g (c * s n)` for `0 < c < 1`
  have hP3 : ∀ c, 0 < c → c < 1 → ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < g (c * s n) := by
    intro c hc0 hc1
    filter_upwards [hE 0, hsM 1] with n hn hs1
    have hbdd : BddBelow (S n) := ⟨0, fun x hx ↦ (hn.2 x hx).le⟩
    by_contra hcon
    push Not at hcon
    have h1 : s n ≤ c * s n := csInf_le hbdd hcon
    nlinarith
  -- `n * g (s n) → 1`
  have hkey : Tendsto (fun n : ℕ ↦ (n : ℝ) * g (s n)) atTop (𝓝 1) := by
    rw [tendsto_order]
    constructor
    · intro l hl
      set l' := max l 0 with hl'
      have hl'1 : l' < 1 := max_lt hl one_pos
      have hcont : Tendsto (fun c : ℝ ↦ c ^ α) (𝓝[<] 1) (𝓝 1) := by
        have := (Real.continuousAt_rpow_const 1 α (Or.inl one_ne_zero)).tendsto
        rw [Real.one_rpow] at this
        exact this.mono_left nhdsWithin_le_nhds
      obtain ⟨c, hcl, hc⟩ := ((hcont.eventually (lt_mem_nhds hl'1)).and
        (Ioo_mem_nhdsLT one_pos)).exists
      have hratio : Tendsto (fun n ↦ g (s n) / g (c * s n)) atTop (𝓝 (c ^ α)) := by
        have := ((hRV.tendsto hc.1).comp hstop).inv₀ (Real.rpow_pos_of_pos hc.1 _).ne'
        rw [Real.rpow_neg hc.1.le, inv_inv] at this
        refine this.congr fun n ↦ ?_
        simp [inv_div]
      filter_upwards [hratio.eventually (lt_mem_nhds hcl), hP3 c hc.1 hc.2,
        eventually_ge_atTop 1] with n h1 h2 hn1
      have hn : (0 : ℝ) < n := by exact_mod_cast hn1
      have hgc := gpos (c * s n)
      have hX : 1 < (n : ℝ) * g (c * s n) := by
        rw [div_lt_iff₀ hn] at h2; linarith
      have e : (n : ℝ) * g (s n) = (n * g (c * s n)) * (g (s n) / g (c * s n)) := by
        field_simp
      have hr : 0 ≤ l' := le_max_right _ _
      rw [e]
      have : l' < (n * g (c * s n)) * (g (s n) / g (c * s n)) := by nlinarith
      exact lt_of_le_of_lt (le_max_left _ _) this
    · intro u hu
      filter_upwards [hP2, eventually_ge_atTop 1] with n hn hn1
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
      have : (n : ℝ) * g (s n) ≤ 1 := by
        rw [le_div_iff₀ hn'] at hn; linarith
      linarith
  refine ⟨fun n ↦ max (s n) 1, fun n ↦ lt_max_of_lt_right one_pos, fun x hx ↦ ?_⟩
  have := hkey.mul ((hRV.tendsto hx).comp hstop)
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [hsM 1] with n hn
  simp only [Function.comp_apply, max_eq_left hn]
  rw [mul_comm (s n) x, mul_assoc, mul_div_cancel₀ _ (gpos _).ne']

/-! ### Necessity: from affine normalization to regular variation -/

/-- The doubling argument on one dyadic chain. -/
private lemma doubling_core {A B : ℝ → ℝ} {ρ ε T m M : ℝ} (hρ : 1 < ρ) (hε : 0 ≤ ε)
    (hT : 0 < T) (hm : 0 < m)
    (hstep : ∀ t ≥ T, ρ * A t ≤ A (2 * t) ∧ |B (2 * t) - B t| ≤ ε * A t)
    (hloc : ∀ t ∈ Icc T (2 * T), m ≤ A t ∧ |B t| ≤ M) {s : ℝ} (hs : T ≤ s) :
    ∃ j : ℕ, s < 2 ^ (j + 1) * T ∧ ρ ^ j * m ≤ A s ∧ |B s| ≤ M + ε / (ρ - 1) * A s := by
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near (x := s / T)
    (by rwa [le_div_iff₀ hT, one_mul]) one_lt_two
  set t := s / 2 ^ j with ht
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have htT : T ≤ t := by
    rw [ht, le_div_iff₀ h2j]; rw [le_div_iff₀ hT] at hj1; linarith
  have ht2T : t ≤ 2 * T := by
    rw [ht, div_le_iff₀ h2j]; rw [div_lt_iff₀ hT, pow_succ] at hj2; linarith
  have hC : 0 < ρ - 1 := by linarith
  have key : ∀ i : ℕ, ρ ^ i * m ≤ A (2 ^ i * t) ∧
      |B (2 ^ i * t)| ≤ M + ε / (ρ - 1) * A (2 ^ i * t) := by
    intro i
    induction i with
    | zero =>
      simp only [pow_zero, one_mul]
      obtain ⟨h1, h2⟩ := hloc t ⟨htT, ht2T⟩
      refine ⟨h1, h2.trans ?_⟩
      have : 0 ≤ ε / (ρ - 1) * A t := mul_nonneg (div_nonneg hε hC.le) (hm.le.trans h1)
      linarith
    | succ i ih =>
      have hge : T ≤ 2 ^ i * t :=
        le_trans htT (le_mul_of_one_le_left (hT.le.trans htT) (one_le_pow₀ one_le_two))
      obtain ⟨s1, s2⟩ := hstep _ hge
      rw [show (2 : ℝ) ^ (i + 1) * t = 2 * (2 ^ i * t) by ring]
      set x := 2 ^ i * t
      constructor
      · calc ρ ^ (i + 1) * m = ρ * (ρ ^ i * m) := by ring
          _ ≤ ρ * A x := mul_le_mul_of_nonneg_left ih.1 (by linarith)
          _ ≤ _ := s1
      · have e1 : |B (2 * x)| ≤ |B x| + ε * A x := by
          have := abs_sub_abs_le_abs_sub (B (2 * x)) (B x); linarith
        have e2 : ε / (ρ - 1) * (ρ * A x) ≤ ε / (ρ - 1) * A (2 * x) :=
          mul_le_mul_of_nonneg_left s1 (div_nonneg hε hC.le)
        have e3 : ε / (ρ - 1) * (ρ * A x) = ε / (ρ - 1) * A x + ε * A x := by
          field_simp; ring
        linarith [ih.2]
  have hs_eq : 2 ^ j * t = s := by rw [ht]; field_simp
  refine ⟨j, by rwa [div_lt_iff₀ hT] at hj2, ?_⟩
  rw [← hs_eq]
  exact key j

/-- The doubling lemma: if `A` grows at least geometrically along doublings and the increments
of `B` along doublings are `o(A)`, then `A → ∞` and `B = o(A)`. -/
private lemma tendsto_of_doubling {A B : ℝ → ℝ} {ρ : ℝ} (hρ : 1 < ρ)
    (h1 : ∀ᶠ t in atTop, ρ * A t ≤ A (2 * t))
    (h2 : ∀ ε > 0, ∀ᶠ t in atTop, |B (2 * t) - B t| ≤ ε * A t)
    (hloc : ∀ T : ℝ, ∃ m > 0, ∃ M, ∀ t ∈ Icc T (2 * T), m ≤ A t ∧ |B t| ≤ M) :
    Tendsto A atTop atTop ∧ Tendsto (fun t ↦ B t / A t) atTop (𝓝 0) := by
  -- a version of the hypotheses with an explicit threshold
  have hthr : ∀ ε > 0, ∃ T > 0, ∀ t ≥ T, ρ * A t ≤ A (2 * t) ∧ |B (2 * t) - B t| ≤ ε * A t := by
    intro ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.1 ((h1.and (h2 ε hε)).and (eventually_ge_atTop 1))
    exact ⟨T, by linarith [(hT T le_rfl).2], fun t ht ↦ (hT t ht).1⟩
  have hAtop : Tendsto A atTop atTop := by
    refine tendsto_atTop.2 fun L ↦ ?_
    obtain ⟨T, hT, hstep⟩ := hthr 1 one_pos
    obtain ⟨m, hm, M, hlocT⟩ := hloc T
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (L / m) hρ
    filter_upwards [eventually_ge_atTop (2 ^ J * T)] with s hs
    have hTs : T ≤ s := le_trans (le_mul_of_one_le_left hT.le (one_le_pow₀ one_le_two)) hs
    obtain ⟨j, hj1, hj2, -⟩ := doubling_core hρ zero_le_one hT hm hstep hlocT hTs
    have hjJ : J ≤ j := by
      by_contra hcon
      push Not at hcon
      have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ J := pow_le_pow_right₀ one_le_two hcon
      nlinarith
    have : ρ ^ J ≤ ρ ^ j := pow_le_pow_right₀ hρ.le hjJ
    rw [div_lt_iff₀ hm] at hJ
    nlinarith
  refine ⟨hAtop, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hC : 0 < ρ - 1 := by linarith
  set ε₀ := ε / (2 * (1 / (ρ - 1) + 1)) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hCε : ε₀ / (ρ - 1) < ε / 2 := by
    rw [hε₀, div_div, div_lt_div_iff₀ (by positivity) two_pos]
    have : ε * 2 < ε * (2 * (1 / (ρ - 1) + 1) * (ρ - 1)) := by
      have : 2 * (1 / (ρ - 1) + 1) * (ρ - 1) = 2 + 2 * (ρ - 1) := by field_simp
      rw [this]; nlinarith
    linarith
  obtain ⟨T, hT, hstep⟩ := hthr ε₀ hε₀pos
  obtain ⟨m, hm, M, hlocT⟩ := hloc T
  filter_upwards [eventually_ge_atTop T, hAtop.eventually_gt_atTop (2 * (|M| + 1) / ε)]
    with s hs hAs
  obtain ⟨j, -, hj2, hj3⟩ := doubling_core hρ hε₀pos.le hT hm hstep hlocT hs
  have hApos : 0 < A s := lt_trans (by positivity : (0 : ℝ) < 2 * (|M| + 1) / ε) hAs
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hApos, div_lt_iff₀ hApos]
  rw [div_lt_iff₀ hε] at hAs
  have : M ≤ |M| := le_abs_self M
  nlinarith

/-- If `t * g (p t) → μ` and `t * g (q t) → ν` with `ν < μ` and `g` antitone, then
eventually `p t < q t`. -/
private lemma eventually_lt_of_tendsto_mul {g : ℝ → ℝ} (hg : Antitone g) {p q : ℝ → ℝ}
    {μ ν : ℝ} (hp : Tendsto (fun t ↦ t * g (p t)) atTop (𝓝 μ))
    (hq : Tendsto (fun t ↦ t * g (q t)) atTop (𝓝 ν)) (hμν : ν < μ) :
    ∀ᶠ t in atTop, p t < q t := by
  filter_upwards [hp.eventually (lt_mem_nhds (show (μ + ν) / 2 < μ by linarith)),
    hq.eventually (gt_mem_nhds (show ν < (μ + ν) / 2 by linarith)), eventually_gt_atTop 0]
    with t h1 h2 ht
  by_contra hcon
  push Not at hcon
  have := mul_le_mul_of_nonneg_left (hg hcon) ht.le
  linarith

private lemma tendsto_real_of_tendsto_nat {φ : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) * φ n) atTop (𝓝 L)) :
    Tendsto (fun t : ℝ ↦ t * φ ⌊t⌋₊) atTop (𝓝 L) := by
  have h1 : Tendsto (fun t : ℝ ↦ (⌊t⌋₊ : ℝ) * φ ⌊t⌋₊) atTop (𝓝 L) :=
    h.comp tendsto_nat_floor_atTop
  have h2 : Tendsto (fun t : ℝ ↦ t / ⌊t⌋₊) atTop (𝓝 1) := by
    have := (tendsto_nat_floor_div_atTop (R := ℝ)).inv₀ one_ne_zero
    rw [inv_one] at this
    exact this.congr fun t ↦ inv_div _ _
  have := h2.mul h1
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have : (⌊t⌋₊ : ℝ) ≠ 0 := by
    have := Nat.floor_pos.2 ht
    positivity
  field_simp

/-- Replacing `a n * x + b n` by `a n * x` when `b n / a n → 0`. -/
private lemma tendsto_scale_of_tendsto_affine {g : ℝ → ℝ} (hg : Antitone g) {α : ℝ}
    {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hba : Tendsto (fun n ↦ b n / a n) atTop (𝓝 0))
    (h : ∀ y > 0, Tendsto (fun n : ℕ ↦ (n : ℝ) * g (a n * y + b n)) atTop (𝓝 (y ^ (-α))))
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * g (a n * x)) atTop (𝓝 (x ^ (-α))) := by
  have hc : Tendsto (fun y : ℝ ↦ y ^ (-α)) (𝓝 x) (𝓝 (x ^ (-α))) :=
    (Real.continuousAt_rpow_const x (-α) (Or.inl hx.ne')).tendsto
  rw [tendsto_order]
  constructor
  · intro l hl
    obtain ⟨x', hl', hx'⟩ := (((hc.mono_left nhdsWithin_le_nhds).eventually
      (lt_mem_nhds hl)).and (self_mem_nhdsWithin (s := Ioi x))).exists
    filter_upwards [(h x' (hx.trans hx')).eventually (lt_mem_nhds hl'),
      hba.eventually (lt_mem_nhds (show -(x' - x) < 0 by linarith [show x < x' from hx']))]
      with n h1 h2
    rw [lt_div_iff₀ (ha n)] at h2
    have hle : a n * x ≤ a n * x' + b n := by nlinarith
    have := mul_le_mul_of_nonneg_left (hg hle) (Nat.cast_nonneg n)
    linarith
  · intro u hu
    obtain ⟨x', hu', hx'⟩ := (((hc.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds hu)).and (Ioo_mem_nhdsLT hx)).exists
    filter_upwards [(h x' hx'.1).eventually (gt_mem_nhds hu'),
      hba.eventually (gt_mem_nhds (show 0 < x - x' by linarith [hx'.2]))]
      with n h1 h2
    rw [div_lt_iff₀ (ha n)] at h2
    have hle : a n * x' + b n ≤ a n * x := by nlinarith
    have := mul_le_mul_of_nonneg_left (hg hle) (Nat.cast_nonneg n)
    linarith

/-- From `n * g (a n * x) → x ^ (-α)` with `a n → ∞` to regular variation of `g`. -/
private lemma isRegularlyVarying_of_tendsto_scale {g : ℝ → ℝ} (hg : Antitone g)
    (hpos : ∀ x, 0 < g x) {α : ℝ} {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    (h : ∀ x > 0, Tendsto (fun n : ℕ ↦ (n : ℝ) * g (a n * x)) atTop (𝓝 (x ^ (-α)))) :
    IsRegularlyVarying g (-α) := by
  refine ⟨Eventually.of_forall hpos, fun c hc ↦ ?_⟩
  have hbdd : ∀ t, BddAbove {n | a n ≤ t} := by
    intro t
    obtain ⟨K, hK⟩ := eventually_atTop.1 (ha.eventually_gt_atTop t)
    refine ⟨K, fun n hn ↦ ?_⟩
    by_contra hlt
    push Not at hlt
    exact absurd (show a n ≤ t from hn) (not_le.2 (hK n hlt.le))
  set N : ℝ → ℕ := fun t ↦ sSup {n | a n ≤ t} with hN
  have hN1 : ∀ t, a 0 ≤ t → a (N t) ≤ t := fun t ht ↦ Nat.sSup_mem ⟨0, ht⟩ (hbdd t)
  have hN2 : ∀ t, t < a (N t + 1) := by
    intro t
    by_contra hcon
    push Not at hcon
    have := le_csSup (hbdd t) (show N t + 1 ∈ {n | a n ≤ t} from hcon)
    exact Nat.not_succ_le_self _ this
  have hNtop : Tendsto N atTop atTop := by
    refine tendsto_atTop.2 fun K ↦ ?_
    filter_upwards [eventually_ge_atTop (a K)] with t ht
    exact le_csSup (hbdd t) ht
  have hc' := h c hc
  have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) * g (a n)) atTop (𝓝 1) := by
    simpa using h 1 one_pos
  have hc'' : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * g (a (n + 1) * c)) atTop (𝓝 (c ^ (-α))) := by
    simpa using (tendsto_add_atTop_iff_nat 1).2 hc'
  have h1' : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * g (a (n + 1))) atTop (𝓝 1) := by
    simpa using (tendsto_add_atTop_iff_nat 1).2 h1
  have hq := tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1
  have hup : Tendsto (fun n : ℕ ↦ g (a n * c) / g (a (n + 1))) atTop (𝓝 (c ^ (-α))) := by
    have := (hc'.div h1' one_ne_zero).div hq one_ne_zero
    rw [div_one, div_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    have := (hpos (a (n + 1))).ne'
    simp only [Pi.div_apply]
    field_simp
  have hlow : Tendsto (fun n : ℕ ↦ g (a (n + 1) * c) / g (a n)) atTop (𝓝 (c ^ (-α))) := by
    have := (hc''.div h1 one_ne_zero).mul hq
    rw [div_one, mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    have := (hpos (a n)).ne'
    simp only [Pi.div_apply]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlow.comp hNtop) (hup.comp hNtop) ?_ ?_
  · filter_upwards [eventually_ge_atTop (a 0)] with t ht
    have e1 := hN1 t ht
    have e2 := (hN2 t).le
    simp only [Function.comp_apply]
    refine div_le_div₀ (hpos _).le (hg ?_) (hpos _) (hg e1)
    nlinarith
  · filter_upwards [eventually_ge_atTop (a 0)] with t ht
    have e1 := hN1 t ht
    have e2 := (hN2 t).le
    simp only [Function.comp_apply]
    refine div_le_div₀ (hpos _).le (hg ?_) (hpos _) (hg e2)
    nlinarith

/-- **Necessity in Gnedenko's theorem** (analytic form): if `g` is antitone and
`n * g (a n * y + b n) → y ^ (-α)` for every `y > 0`, with `a n > 0`, then `g` is regularly
varying with index `-α`. -/
theorem isRegularlyVarying_of_tendsto_mul_affine {g : ℝ → ℝ} (hg : Antitone g) {α : ℝ}
    (hα : 0 < α) {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h : ∀ y > 0, Tendsto (fun n : ℕ ↦ (n : ℝ) * g (a n * y + b n)) atTop (𝓝 (y ^ (-α)))) :
    IsRegularlyVarying g (-α) := by
  set A : ℝ → ℝ := fun t ↦ a ⌊t⌋₊ with hA
  set B : ℝ → ℝ := fun t ↦ b ⌊t⌋₊ with hB
  have hreal : ∀ y > 0, Tendsto (fun t ↦ t * g (A t * y + B t)) atTop (𝓝 (y ^ (-α))) :=
    fun y hy ↦ tendsto_real_of_tendsto_nat (φ := fun n ↦ g (a n * y + b n)) (h y hy)
  have hdbl : ∀ y > 0, Tendsto (fun t ↦ t * g (A (2 * t) * y + B (2 * t))) atTop
      (𝓝 (y ^ (-α) / 2)) := by
    intro y hy
    have := ((hreal y hy).comp (tendsto_id.const_mul_atTop two_pos)).div_const 2
    refine this.congr fun t ↦ ?_
    simp only [Function.comp_apply, id]
    ring
  set κ : ℝ := 2 ^ (1 / α) with hκ
  have hκ1 : 1 < κ := Real.one_lt_rpow (by norm_num) (by positivity)
  have hκpos : 0 < κ := by linarith
  have hκα : κ ^ (-α) = 1 / 2 := by
    rw [hκ, ← Real.rpow_mul (by norm_num), show 1 / α * -α = -1 by field_simp,
      Real.rpow_neg_one, one_div]
  have h2κα : (2 * κ) ^ (-α) = 2 ^ (-α) / 2 := by
    rw [Real.mul_rpow (by norm_num) hκpos.le, hκα]; ring
  have hone : (1 : ℝ) ^ (-α) / 2 = 1 / 2 := by rw [Real.one_rpow]
  have hnα : -α < 0 := by linarith
  -- the key relations between levels `t` and `2 t`
  have hrel : ∀ δ, 0 < δ → δ ≤ κ / 2 → ∀ᶠ t in atTop,
      A t * (κ - 2 * δ) ≤ A (2 * t) ∧ |B (2 * t) - B t| ≤ 3 * δ * A t := by
    intro δ hδ hδκ
    have p1 : 0 < κ - δ := by linarith
    have p3 : 0 < 2 * κ - δ := by linarith
    have q1 := eventually_lt_of_tendsto_mul hg (hreal (κ - δ) p1) (hdbl 1 one_pos)
      (by rw [hone, ← hκα]; exact Real.rpow_lt_rpow_of_neg p1 (by linarith) hnα)
    have q2 := eventually_lt_of_tendsto_mul hg (hdbl 1 one_pos) (hreal (κ + δ) (by linarith))
      (by rw [hone, ← hκα]; exact Real.rpow_lt_rpow_of_neg hκpos (by linarith) hnα)
    have q3 := eventually_lt_of_tendsto_mul hg (hreal (2 * κ - δ) p3) (hdbl 2 two_pos)
      (by rw [← h2κα]; exact Real.rpow_lt_rpow_of_neg p3 (by linarith) hnα)
    have q4 := eventually_lt_of_tendsto_mul hg (hdbl 2 two_pos) (hreal (2 * κ + δ) (by linarith))
      (by rw [← h2κα]; exact Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) hnα)
    filter_upwards [q1, q2, q3, q4] with t r1 r2 r3 r4
    have hA2 : A (2 * t) < A t * (κ + 2 * δ) := by linarith
    have hA1 : A t * (κ - 2 * δ) < A (2 * t) := by linarith
    refine ⟨hA1.le, abs_le.2 ⟨by linarith, by linarith⟩⟩
  set ρ := (κ + 1) / 2 with hρ
  have hρ1 : 1 < ρ := by rw [hρ]; linarith
  have hd1 : ∀ᶠ t in atTop, ρ * A t ≤ A (2 * t) := by
    filter_upwards [hrel ((κ - 1) / 4) (by linarith) (by linarith)] with t ht
    have : A t * (κ - 2 * ((κ - 1) / 4)) = ρ * A t := by rw [hρ]; ring
    linarith [ht.1]
  have hd2 : ∀ ε > 0, ∀ᶠ t in atTop, |B (2 * t) - B t| ≤ ε * A t := by
    intro ε hε
    filter_upwards [hrel (min (ε / 3) (κ / 2)) (lt_min (by positivity) (by positivity))
      (min_le_right _ _)] with t ht
    have hAt : 0 < A t := ha _
    have : 3 * min (ε / 3) (κ / 2) * A t ≤ ε * A t := by
      have := min_le_left (ε / 3) (κ / 2)
      nlinarith
    linarith [ht.2]
  have hloc : ∀ T : ℝ, ∃ m > 0, ∃ M, ∀ t ∈ Icc T (2 * T), m ≤ A t ∧ |B t| ≤ M := by
    intro T
    set K := ⌊2 * T⌋₊
    obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image (Finset.range (K + 1)) a
      ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
    refine ⟨a k₀, ha k₀, ∑ n ∈ Finset.range (K + 1), |b n|, fun t ht ↦ ?_⟩
    have hmem : ⌊t⌋₊ ∈ Finset.range (K + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.floor_le_floor ht.2))
    exact ⟨hk₀ _ hmem,
      Finset.single_le_sum (f := fun n ↦ |b n|) (fun i _ ↦ abs_nonneg _) hmem⟩
  obtain ⟨hAtop, hBA⟩ := tendsto_of_doubling hρ1 hd1 hd2 hloc
  have hatop : Tendsto a atTop atTop :=
    (hAtop.comp tendsto_natCast_atTop_atTop).congr fun n ↦ by simp [hA]
  have hba : Tendsto (fun n ↦ b n / a n) atTop (𝓝 0) :=
    (hBA.comp tendsto_natCast_atTop_atTop).congr fun n ↦ by simp [hA, hB]
  have hscale := fun x (hx : 0 < x) ↦ tendsto_scale_of_tendsto_affine hg ha hba h hx
  have hpos : ∀ x, 0 < g x := by
    intro x
    have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) * g (a n)) atTop (𝓝 1) := by
      simpa using hscale 1 one_pos
    obtain ⟨n, hn1, hn2⟩ := ((h1.eventually (lt_mem_nhds one_pos)).and
      (hatop.eventually_ge_atTop x)).exists
    have : 0 < g (a n) := by
      by_contra hcon
      push Not at hcon
      have : (n : ℝ) * g (a n) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hcon
      linarith
    exact this.trans_le (hg hn2)
  exact isRegularlyVarying_of_tendsto_scale hg hpos hatop hscale

end Frechet

end ExtremeValueTheory

namespace CumulativeDistributionFunction

open ExtremeValueTheory

/-- A c.d.f. `F` is in the maximum domain of attraction of the standard Fréchet distribution
`Φ_α(x) = exp (-x ^ (-α))` (for `x > 0`, and `0` for `x ≤ 0`) if there are orientation
preserving affine maps `A n` with `((A n • F) x) ^ n → Φ_α x` for every `x`. (Since `Φ_α` is
continuous, this is the same as convergence at all continuity points.) -/
def IsInMDAFrechet (F : CumulativeDistributionFunction) {α : ℝ} (hα : 0 < α) : Prop :=
  ∃ As : ℕ → AffineIncrEquiv,
    ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (standardFrechetCDF hα x))

private lemma standardFrechetCDF_mem_Ioo {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    standardFrechetCDF hα x ∈ Ioo 0 1 := by
  rw [standardFrechetCDF_apply_pos_eq hα hx]
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 ?_⟩
  have : 0 < Real.rpow x (-α) := Real.rpow_pos_of_pos hx _
  linarith

private lemma neg_log_standardFrechetCDF {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    -Real.log (standardFrechetCDF hα x) = x ^ (-α) := by
  rw [standardFrechetCDF_apply_pos_eq hα hx, Real.log_exp, neg_neg, Real.rpow_eq_pow]

private lemma antitone_one_sub (F : CumulativeDistributionFunction) :
    Antitone (fun x ↦ 1 - F x) :=
  fun _ _ h ↦ sub_le_sub_left (F.mono' h) 1

/-- **Gnedenko's theorem, sufficiency**: if the tail `1 - F` is regularly varying with index
`-α`, then `F` is in the maximum domain of attraction of the Fréchet distribution `Φ_α`. -/
theorem isInMDAFrechet_of_isRegularlyVarying (F : CumulativeDistributionFunction) {α : ℝ}
    (hα : 0 < α) (hRV : IsRegularlyVarying (fun x ↦ 1 - F x) (-α)) :
    F.IsInMDAFrechet hα := by
  have hg := F.antitone_one_sub
  have hgr : ∀ x, ContinuousWithinAt (fun x ↦ 1 - F x) (Ici x) x :=
    fun x ↦ continuousWithinAt_const.sub (F.right_continuous x)
  have hg0 : Tendsto (fun x ↦ 1 - F x) atTop (𝓝 0) := by
    simpa using (F.tendsto_atTop).const_sub 1
  obtain ⟨a, ha, hlim⟩ := Frechet.exists_tendsto_mul_of_isRegularlyVarying hg hgr hg0 hRV
  have gpos := IsRegularlyVarying.pos_of_antitone hg hRV.1
  refine ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs (ha n) 0)⁻¹, fun x ↦ ?_⟩
  have happ : ∀ n, ((AffineIncrEquiv.mkOfCoefs (ha n) 0)⁻¹ • F) x = F (a n * x) := by
    intro n; simp
  rcases le_or_gt x 0 with hx | hx
  · rw [standardFrechetCDF_apply_nonpos_eq hα hx]
    simp only [happ]
    have hF0 : F 0 < 1 := by have := gpos 0; linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_pow_atTop_nhds_zero_of_lt_one (F.apply_nonneg 0) hF0)
      (fun n ↦ pow_nonneg (F.apply_nonneg _) n) (fun n ↦ ?_)
    exact pow_le_pow_left₀ (F.apply_nonneg _)
      (F.mono' (mul_nonpos_of_nonneg_of_nonpos (ha n).le hx)) n
  · have hGx := standardFrechetCDF_mem_Ioo hα hx
    refine ((tfae_ev_limit_relation (F := F)
      (fun n ↦ (AffineIncrEquiv.mkOfCoefs (ha n) 0)⁻¹) hGx).out 1 3).2 ?_
    rw [neg_log_standardFrechetCDF hα hx]
    simpa only [happ] using hlim x hx

/-- **Gnedenko's theorem, necessity**: if `F` is in the maximum domain of attraction of the
Fréchet distribution `Φ_α`, then the tail `1 - F` is regularly varying with index `-α`. -/
theorem isRegularlyVarying_of_isInMDAFrechet (F : CumulativeDistributionFunction) {α : ℝ}
    (hα : 0 < α) (hF : F.IsInMDAFrechet hα) :
    IsRegularlyVarying (fun x ↦ 1 - F x) (-α) := by
  obtain ⟨As, hAs⟩ := hF
  have happ : ∀ n x, (As n • F) x = F ((As n)⁻¹.coefs.1 * x + (As n)⁻¹.coefs.2) := by
    intro n x
    rw [mulAction_apply_eq, AffineIncrEquiv.apply_eq]
  refine Frechet.isRegularlyVarying_of_tendsto_mul_affine F.antitone_one_sub hα
    (b := fun n ↦ ((As n)⁻¹).coefs.2)
    (fun n ↦ ((As n)⁻¹).coefs_fst_pos) fun y hy ↦ ?_
  have hGy := standardFrechetCDF_mem_Ioo hα hy
  have := ((tfae_ev_limit_relation (F := F) As hGy).out 1 3).1 (hAs y)
  rw [neg_log_standardFrechetCDF hα hy] at this
  simpa only [happ] using this

/-- **Gnedenko's theorem** for the Fréchet domain of attraction ([dHF, Theorem 1.2.1],
[Resnick, Proposition 1.11], [EKM, Theorem 3.3.7]): a c.d.f. `F` is in the maximum domain of
attraction of the Fréchet distribution `Φ_α` if and only if its tail `1 - F` is regularly varying
with index `-α`. -/
theorem isInMDAFrechet_iff (F : CumulativeDistributionFunction) {α : ℝ} (hα : 0 < α) :
    F.IsInMDAFrechet hα ↔ IsRegularlyVarying (fun x ↦ 1 - F x) (-α) :=
  ⟨F.isRegularlyVarying_of_isInMDAFrechet hα, F.isInMDAFrechet_of_isRegularlyVarying hα⟩

end CumulativeDistributionFunction
