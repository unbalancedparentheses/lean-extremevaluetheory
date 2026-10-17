/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.DomainOfAttraction.Frechet

/-!
# Gnedenko's theorem: the Weibull maximum domain of attraction

Let `F` be a c.d.f. and `α > 0`. We prove that `F` is in the maximum domain of attraction of the
standard Weibull distribution `Ψ_α(x) = exp (-(-x) ^ α)` (`x < 0`, and `Ψ_α(x) = 1` for `x ≥ 0`),
i.e. there are orientation preserving affine maps `A n` with `((A n • F) x) ^ n → Ψ_α x` for
all `x`, if and only if `F` has a finite right endpoint `x_F` (that is, `F x_F = 1` and
`F x < 1` for `x < x_F`) and `t ↦ 1 - F (x_F - t⁻¹)` is regularly varying at `+∞` with
index `-α`.

## References

* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 1.2.1(2) [dHF].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Theorem 3.3.12 [EKM].

## Main definitions and results

* `CumulativeDistributionFunction.IsInMDAWeibull F hα`: `F` is in the maximum domain of
  attraction of `standardWeibullCDF hα`.
* `CumulativeDistributionFunction.isInMDAWeibull_iff`: Gnedenko's characterization.

## Proof sketch

The transformation `x ↦ x_F - x⁻¹` reduces both directions to the analytic lemmas of the
Fréchet case (`ExtremeValueTheory.Frechet.exists_tendsto_mul_of_isRegularlyVarying` and
`ExtremeValueTheory.Frechet.isRegularlyVarying_of_tendsto_mul_affine`), applied to the antitone
function `t ↦ 1 - F (x_F - t⁻¹)` (suitably extended to `t ≤ 0` resp. `t < 1`).

The extra content of necessity is the finiteness of the right endpoint and the identification
`(b n - x_F) / a n → 0`, where `(A n)⁻¹ x = a n * x + b n`. Comparing the levels `n` and `2 n`
shows that `Φ n = b n + c * a n` is eventually non-increasing along doublings for every `c > 0`;
since `n (1 - F (b n)) → 0`, this forces `F (b n + c * a n) = 1` eventually.
-/

open Filter Topology Set

namespace ExtremeValueTheory

namespace Weibull

/-- An antitone, positive function which is regularly varying with negative index tends to `0`
at `+∞`. -/
theorem tendsto_zero_of_isRegularlyVarying {g : ℝ → ℝ} (hg : Antitone g) (hpos : ∀ x, 0 < g x)
    {α : ℝ} (hα : 0 < α) (hRV : IsRegularlyVarying g (-α)) : Tendsto g atTop (𝓝 0) := by
  have hbdd : BddBelow (range g) := ⟨0, by rintro _ ⟨x, rfl⟩; exact (hpos x).le⟩
  have hL := tendsto_atTop_ciInf hg hbdd
  have hL0 : 0 ≤ ⨅ x, g x := le_ciInf fun x ↦ (hpos x).le
  rcases hL0.lt_or_eq with hL0 | hL0
  · exfalso
    have h1 : Tendsto (fun x ↦ g (2 * x) / g x) atTop (𝓝 ((⨅ x, g x) / ⨅ x, g x)) :=
      (hL.comp (tendsto_id.const_mul_atTop two_pos)).div hL hL0.ne'
    rw [div_self hL0.ne'] at h1
    have h2 := tendsto_nhds_unique (hRV.tendsto two_pos) h1
    have : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    linarith
  · rw [← hL0] at hL
    exact hL

/-- If `t * u (p n) → μ` and `t * u (q n) → ν` with `ν < μ` and `u` antitone, then
eventually `p n < q n`. -/
private lemma eventually_lt_of_tendsto_mul {u : ℝ → ℝ} (hu : Antitone u) {p q : ℕ → ℝ}
    {μ ν : ℝ} (hp : Tendsto (fun n : ℕ ↦ (n : ℝ) * u (p n)) atTop (𝓝 μ))
    (hq : Tendsto (fun n : ℕ ↦ (n : ℝ) * u (q n)) atTop (𝓝 ν)) (hμν : ν < μ) :
    ∀ᶠ n in atTop, p n < q n := by
  filter_upwards [hp.eventually (lt_mem_nhds (show (μ + ν) / 2 < μ by linarith)),
    hq.eventually (gt_mem_nhds (show ν < (μ + ν) / 2 by linarith))] with n h1 h2
  by_contra hcon
  push Not at hcon
  have := mul_le_mul_of_nonneg_left (hu hcon) (Nat.cast_nonneg n)
  linarith

/-- **The endpoint lemma.** If `u` is antitone and nonnegative,
`n * u (a n * z + b n) → (-z) ^ α` for every `z < 0` and `n * u (b n) → 0`, then for every
`c > 0`, eventually `u (b n + c * a n) = 0`. -/
theorem eventually_eq_zero_of_tendsto_mul_affine {u : ℝ → ℝ} (hu : Antitone u)
    (hu0 : ∀ x, 0 ≤ u x) {α : ℝ} (hα : 0 < α) {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h : ∀ z < 0, Tendsto (fun n : ℕ ↦ (n : ℝ) * u (a n * z + b n)) atTop (𝓝 ((-z) ^ α)))
    (h0 : Tendsto (fun n : ℕ ↦ (n : ℝ) * u (b n)) atTop (𝓝 0)) :
    ∀ c > 0, ∀ᶠ n in atTop, u (b n + c * a n) = 0 := by
  set κ : ℝ := (2 : ℝ) ^ (-1 / α) with hκ
  have hκpos : 0 < κ := Real.rpow_pos_of_pos two_pos _
  have hκ1 : κ < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (div_neg_of_neg_of_pos (by norm_num) hα)
  have hκα : κ ^ α = 1 / 2 := by
    rw [hκ, ← Real.rpow_mul (by norm_num), show -1 / α * α = -1 by field_simp,
      Real.rpow_neg_one, one_div]
  have h2κα : (2 * κ) ^ α = 2 ^ α / 2 := by
    rw [Real.mul_rpow (by norm_num) hκpos.le, hκα]; ring
  have h2 : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ (by omega : n ≤ 2 * n)) tendsto_id
  have hdbl : ∀ z < 0, Tendsto (fun n : ℕ ↦ (n : ℝ) * u (a (2 * n) * z + b (2 * n))) atTop
      (𝓝 ((-z) ^ α / 2)) := by
    intro z hz
    refine (((h z hz).comp h2).div_const 2).congr fun n ↦ ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  -- comparison of the levels `n` and `2 n`
  have hstep : ∀ δ, 0 < δ → δ < κ → ∀ᶠ n in atTop,
      a (2 * n) < a n * (κ + 2 * δ) ∧ b (2 * n) < b n + 3 * δ * a n := by
    intro δ hδ hδκ
    have q1 := eventually_lt_of_tendsto_mul hu (p := fun n ↦ a (2 * n) * (-1) + b (2 * n))
      (q := fun n ↦ a n * (-κ + δ) + b n) (hdbl (-1) (by norm_num)) (h (-κ + δ) (by linarith))
      (by
        rw [show -(-κ + δ) = κ - δ by ring, neg_neg, Real.one_rpow,
          show (1 : ℝ) / 2 = κ ^ α from hκα.symm]
        exact Real.rpow_lt_rpow (by linarith) (by linarith) hα)
    have q2 := eventually_lt_of_tendsto_mul hu (p := fun n ↦ a n * (-2 * κ - δ) + b n)
      (q := fun n ↦ a (2 * n) * (-2) + b (2 * n)) (h (-2 * κ - δ) (by linarith))
      (hdbl (-2) (by norm_num))
      (by
        rw [show -(-2 * κ - δ) = 2 * κ + δ by ring, neg_neg, ← h2κα]
        exact Real.rpow_lt_rpow (by linarith) (by linarith) hα)
    filter_upwards [q1, q2] with n r1 r2
    constructor <;> nlinarith
  intro c hc
  set ρ : ℝ := (κ + 1) / 2 with hρ
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  set ε : ℝ := c * (1 - ρ) with hε
  have hεpos : 0 < ε := mul_pos hc (by linarith)
  set δ : ℝ := min (ε / 3) (min (κ / 2) ((1 - κ) / 4)) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by linarith))
  have hδ1 : δ ≤ ε / 3 := min_le_left _ _
  have hδ2 : δ ≤ κ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ (1 - κ) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  -- the potential `Φ n = b n + c * a n` is non-increasing along doublings
  have hΦ : ∀ᶠ n in atTop, b (2 * n) + c * a (2 * n) ≤ b n + c * a n := by
    filter_upwards [hstep δ hδpos (by linarith)] with n ⟨r1, r2⟩
    have han := ha n
    have e1 : a (2 * n) ≤ ρ * a n := by
      have : a n * (κ + 2 * δ) ≤ ρ * a n := by rw [hρ]; nlinarith
      linarith
    have e2 : c * a (2 * n) ≤ c * (ρ * a n) := mul_le_mul_of_nonneg_left e1 hc.le
    have e3 : 3 * δ * a n ≤ ε * a n := mul_le_mul_of_nonneg_right (by linarith) han.le
    have e4 : ε * a n + c * (ρ * a n) = c * a n := by rw [hε]; ring
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hΦ
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := le_of_max_le_left hn
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hchain : ∀ k : ℕ, b (2 ^ k * n) + c * a (2 ^ k * n) ≤ b n + c * a n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 ^ (k + 1) * n = 2 * (2 ^ k * n) by ring]
      have : N ≤ 2 ^ k * n := hnN.trans (Nat.le_mul_of_pos_left _ (by positivity))
      exact (hN _ this).trans ih
  by_contra hne
  have hη : 0 < u (b n + c * a n) := lt_of_le_of_ne (hu0 _) (Ne.symm hne)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (h0.eventually (gt_mem_nhds hη))
  set m := 2 ^ M * n with hm
  have hmM : M ≤ m := by
    have := Nat.lt_two_pow_self (n := M)
    have : 2 ^ M ≤ 2 ^ M * n := Nat.le_mul_of_pos_right _ hn1
    omega
  have hm1 : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hbm : b m ≤ b n + c * a n := by
    have := hchain M
    have := mul_pos hc (ha m)
    linarith
  have h1 := hM m hmM
  have h2 : u (b n + c * a n) ≤ u (b m) := hu hbm
  have h3 : u (b m) ≤ (m : ℝ) * u (b m) := le_mul_of_one_le_left (hu0 _) hm1
  linarith

/-- Replacing the centring `b n` by `x₀` when `(b n - x₀) / a n → 0`. -/
private lemma tendsto_of_tendsto_mul_affine_shift {u : ℝ → ℝ} (hu : Antitone u) {α : ℝ}
    (hα : 0 < α) {a b : ℕ → ℝ} (ha : ∀ n, 0 < a n) {x₀ : ℝ}
    (hd : Tendsto (fun n ↦ (b n - x₀) / a n) atTop (𝓝 0))
    (h : ∀ z < 0, Tendsto (fun n : ℕ ↦ (n : ℝ) * u (a n * z + b n)) atTop (𝓝 ((-z) ^ α)))
    {z : ℝ} (hz : z < 0) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * u (a n * z + x₀)) atTop (𝓝 ((-z) ^ α)) := by
  have hc : Tendsto (fun w : ℝ ↦ (-w) ^ α) (𝓝 z) (𝓝 ((-z) ^ α)) :=
    ((Real.continuousAt_rpow_const (-z) α (Or.inr hα.le)).comp continuousAt_neg).tendsto
  rw [tendsto_order]
  constructor
  · intro l hl
    obtain ⟨w, hl', hw⟩ := (((hc.mono_left nhdsWithin_le_nhds).eventually
      (lt_mem_nhds hl)).and (Ioo_mem_nhdsGT hz)).exists
    filter_upwards [(h w hw.2).eventually (lt_mem_nhds hl'),
      hd.eventually (lt_mem_nhds (show -(w - z) < 0 by linarith [hw.1]))] with n h1 h2
    rw [lt_div_iff₀ (ha n)] at h2
    have hle : a n * z + x₀ ≤ a n * w + b n := by nlinarith
    have := mul_le_mul_of_nonneg_left (hu hle) (Nat.cast_nonneg n)
    linarith
  · intro v hv
    obtain ⟨w, hv', hw⟩ := (((hc.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds hv)).and (Ioo_mem_nhdsLT (show z - 1 < z by linarith))).exists
    filter_upwards [(h w (by linarith [hw.2])).eventually (gt_mem_nhds hv'),
      hd.eventually (gt_mem_nhds (show 0 < z - w by linarith [hw.2]))] with n h1 h2
    rw [div_lt_iff₀ (ha n)] at h2
    have hle : a n * w + b n ≤ a n * z + x₀ := by nlinarith
    have := mul_le_mul_of_nonneg_left (hu hle) (Nat.cast_nonneg n)
    linarith

/-- If `p n ∈ [0, 1]` and `p n ^ n → 1`, then `n * (1 - p n) → 0`. -/
private lemma tendsto_mul_one_sub_of_tendsto_pow {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n)
    (hp1 : ∀ n, p n ≤ 1) (h : Tendsto (fun n ↦ p n ^ n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - p n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n ↦ -Real.log (p n ^ n)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto.comp h).neg
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
    (Eventually.of_forall fun n ↦ mul_nonneg (Nat.cast_nonneg n) (by linarith [hp1 n])) ?_
  filter_upwards [h.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    eventually_ge_atTop 1] with n hn hn1
  have hpos : 0 < p n := by
    rcases (hp0 n).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_pow (by omega)] at hn; norm_num at hn
  rw [Real.log_pow]
  have := Real.log_le_sub_one_of_pos hpos
  have := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg (α := ℝ) n)
  linarith

end Weibull

end ExtremeValueTheory

namespace CumulativeDistributionFunction

open ExtremeValueTheory

/-- A c.d.f. `F` is in the maximum domain of attraction of the standard Weibull distribution
`Ψ_α(x) = exp (-(-x) ^ α)` (for `x < 0`, and `1` for `x ≥ 0`) if there are orientation
preserving affine maps `A n` with `((A n • F) x) ^ n → Ψ_α x` for every `x`. (Since `Ψ_α` is
continuous, this is the same as convergence at all continuity points.) -/
def IsInMDAWeibull (F : CumulativeDistributionFunction) {α : ℝ} (hα : 0 < α) : Prop :=
  ∃ As : ℕ → AffineIncrEquiv,
    ∀ x, Tendsto (fun n : ℕ ↦ ((As n • F) x) ^ n) atTop (𝓝 (standardWeibullCDF hα x))

private lemma standardWeibullCDF_mem_Ioo {α x : ℝ} (hα : 0 < α) (hx : x < 0) :
    standardWeibullCDF hα x ∈ Ioo 0 1 := by
  rw [standardWeibullCDF_apply_neg_eq hα hx]
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 ?_⟩
  have : 0 < Real.rpow (-x) α := Real.rpow_pos_of_pos (by linarith) _
  linarith

private lemma neg_log_standardWeibullCDF {α x : ℝ} (hα : 0 < α) (hx : x < 0) :
    -Real.log (standardWeibullCDF hα x) = (-x) ^ α := by
  rw [standardWeibullCDF_apply_neg_eq hα hx, Real.log_exp, neg_neg, Real.rpow_eq_pow]

private lemma antitone_one_sub' (F : CumulativeDistributionFunction) :
    Antitone (fun x ↦ 1 - F x) :=
  fun _ _ h ↦ sub_le_sub_left (F.mono' h) 1

private lemma inv_neg_inv_rpow_neg {α y : ℝ} (hy : 0 < y) : (-(-y⁻¹)) ^ α = y ^ (-α) := by
  rw [neg_neg, Real.inv_rpow hy.le, Real.rpow_neg hy.le]

/-- **Gnedenko's theorem for the Weibull domain, sufficiency.** -/
theorem isInMDAWeibull_of_isRegularlyVarying (F : CumulativeDistributionFunction) {α : ℝ}
    (hα : 0 < α) {xF : ℝ} (hxF : F xF = 1)
    (hRV : IsRegularlyVarying (fun t ↦ 1 - F (xF - t⁻¹)) (-α)) :
    F.IsInMDAWeibull hα := by
  set G : ℝ → ℝ := fun t ↦ 1 - F (xF - (max t 1)⁻¹) with hG
  have hmax : ∀ t : ℝ, 0 < max t 1 := fun t ↦ lt_of_lt_of_le one_pos (le_max_right _ _)
  have hh : Monotone (fun t : ℝ ↦ xF - (max t 1)⁻¹) := fun s t hst ↦
    sub_le_sub_left (inv_anti₀ (hmax s) (max_le_max hst le_rfl)) xF
  have hGa : Antitone G := fun s t hst ↦ sub_le_sub_left (F.mono' (hh hst)) 1
  have hhc : Continuous (fun t : ℝ ↦ xF - (max t 1)⁻¹) :=
    continuous_const.sub ((continuous_id.max continuous_const).inv₀ fun t ↦ (hmax t).ne')
  have hGr : ∀ x, ContinuousWithinAt G (Ici x) x := fun x ↦
    continuousWithinAt_const.sub ((F.right_continuous _).comp hhc.continuousWithinAt
      fun t ht ↦ hh ht)
  have hGeq : (fun t ↦ 1 - F (xF - t⁻¹)) =ᶠ[atTop] G := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    simp [hG, max_eq_left ht]
  have hGRV := hRV.congr hGeq
  have hGpos : ∀ x, 0 < G x := IsRegularlyVarying.pos_of_antitone hGa hGRV.1
  have hG0 := Weibull.tendsto_zero_of_isRegularlyVarying hGa hGpos hα hGRV
  obtain ⟨a, ha, hlim⟩ := Frechet.exists_tendsto_mul_of_isRegularlyVarying hGa hGr hG0 hGRV
  have hatop : Tendsto a atTop atTop := by
    have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) * G (a n)) atTop (𝓝 1) := by
      simpa using hlim 1 one_pos
    have h2 : Tendsto (fun n : ℕ ↦ G (a n)) atTop (𝓝 0) := by
      have := h1.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [one_mul] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    refine Filter.tendsto_atTop.2 fun M ↦ ?_
    filter_upwards [h2.eventually (gt_mem_nhds (hGpos M))] with n hn
    by_contra hcon
    push Not at hcon
    exact absurd (hGa hcon.le) (not_le.2 hn)
  refine ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs (inv_pos.2 (ha n)) xF)⁻¹, fun x ↦ ?_⟩
  have happ : ∀ n, ((AffineIncrEquiv.mkOfCoefs (inv_pos.2 (ha n)) xF)⁻¹ • F) x =
      F ((a n)⁻¹ * x + xF) := by
    intro n; simp
  rcases le_or_gt 0 x with hx | hx
  · rw [standardWeibullCDF_apply_nonneg_eq hα hx]
    have : ∀ n, F ((a n)⁻¹ * x + xF) = 1 := fun n ↦
      le_antisymm (F.apply_le_one _) (hxF ▸ F.mono' (le_add_of_nonneg_left
        (mul_nonneg (inv_nonneg.2 (ha n).le) hx)))
    simp only [happ, this, one_pow]
    exact tendsto_const_nhds
  · have hGx := standardWeibullCDF_mem_Ioo hα hx
    refine ((tfae_ev_limit_relation (F := F)
      (fun n ↦ (AffineIncrEquiv.mkOfCoefs (inv_pos.2 (ha n)) xF)⁻¹) hGx).out 1 3).2 ?_
    rw [neg_log_standardWeibullCDF hα hx]
    simp only [happ]
    have hy : 0 < -x⁻¹ := neg_pos.2 (inv_lt_zero.2 hx)
    have := hlim (-x⁻¹) hy
    rw [show (-x⁻¹) ^ (-α) = (-x) ^ α by
      rw [← inv_neg_inv_rpow_neg hy, neg_neg, neg_inv, inv_inv]] at this
    refine this.congr' ?_
    filter_upwards [hatop.eventually_ge_atTop (-x)] with n hn
    have hge : 1 ≤ a n * -x⁻¹ := by
      have : (-x) * -x⁻¹ = 1 := by rw [neg_mul_neg, mul_inv_cancel₀ hx.ne]
      nlinarith
    have hne := (ha n).ne'
    have hxne := hx.ne
    simp only [hG, max_eq_left hge]
    congr 3
    field_simp
    ring

/-- **Gnedenko's theorem for the Weibull domain, necessity.** -/
theorem exists_endpoint_of_isInMDAWeibull (F : CumulativeDistributionFunction) {α : ℝ}
    (hα : 0 < α) (hF : F.IsInMDAWeibull hα) :
    ∃ xF : ℝ, F xF = 1 ∧ (∀ x < xF, F x < 1) ∧
      IsRegularlyVarying (fun t ↦ 1 - F (xF - t⁻¹)) (-α) := by
  obtain ⟨As, hAs⟩ := hF
  set a : ℕ → ℝ := fun n ↦ ((As n)⁻¹).coefs.1 with ha_def
  set b : ℕ → ℝ := fun n ↦ ((As n)⁻¹).coefs.2 with hb_def
  have ha : ∀ n, 0 < a n := fun n ↦ ((As n)⁻¹).coefs_fst_pos
  have happ : ∀ n x, (As n • F) x = F (a n * x + b n) := by
    intro n x
    rw [mulAction_apply_eq, AffineIncrEquiv.apply_eq]
  set u : ℝ → ℝ := fun x ↦ 1 - F x with hu_def
  have hu : Antitone u := F.antitone_one_sub'
  have hu0 : ∀ x, 0 ≤ u x := fun x ↦ by simp only [hu_def]; linarith [F.apply_le_one x]
  have hz : ∀ z < 0, Tendsto (fun n : ℕ ↦ (n : ℝ) * u (a n * z + b n)) atTop
      (𝓝 ((-z) ^ α)) := by
    intro z hz
    have hGz := standardWeibullCDF_mem_Ioo hα hz
    have := ((tfae_ev_limit_relation (F := F) As hGz).out 1 3).1 (hAs z)
    rw [neg_log_standardWeibullCDF hα hz] at this
    simpa only [happ] using this
  have h0 : Tendsto (fun n : ℕ ↦ (n : ℝ) * u (b n)) atTop (𝓝 0) := by
    have := hAs 0
    rw [standardWeibullCDF_apply_nonneg_eq hα le_rfl] at this
    simp only [happ, mul_zero, zero_add] at this
    exact Weibull.tendsto_mul_one_sub_of_tendsto_pow (fun n ↦ F.apply_nonneg _)
      (fun n ↦ F.apply_le_one _) this
  have hend := Weibull.eventually_eq_zero_of_tendsto_mul_affine hu hu0 hα ha hz h0
  have hF1 : ∀ x, u x = 0 → F x = 1 := fun x hx ↦ by simp only [hu_def] at hx; linarith
  set S : Set ℝ := {x | F x = 1} with hS
  have hne : S.Nonempty := by
    obtain ⟨n, hn⟩ := (hend 1 one_pos).exists
    exact ⟨_, hF1 _ hn⟩
  have hbdd : BddBelow S := by
    obtain ⟨x₀, hx₀⟩ := (F.tendsto_atBot.eventually (gt_mem_nhds
      (show (0 : ℝ) < 1 by norm_num))).exists
    refine ⟨x₀, fun x hx ↦ ?_⟩
    by_contra hlt
    push Not at hlt
    have : F x ≤ F x₀ := F.mono' hlt.le
    have : F x = 1 := hx
    change F.toFun x₀ < 1 at hx₀
    linarith
  set xF := sInf S with hxF_def
  have hlt : ∀ x < xF, F x < 1 := fun x hx ↦
    lt_of_le_of_ne (F.apply_le_one x) fun h ↦ not_le.2 hx (csInf_le hbdd h)
  have hxF1 : F xF = 1 := by
    refine le_antisymm (F.apply_le_one _) ?_
    have hlim : Tendsto F (𝓝[>] xF) (𝓝 (F xF)) :=
      (F.right_continuous xF).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy ↦ ?_)
    obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt hne (show sInf S < y from hy)
    have hs1 : F.toFun s = 1 := hs
    have hmono : F.toFun s ≤ F.toFun y := F.mono' hsy.le
    change 1 ≤ F.toFun y
    linarith
  have hd : Tendsto (fun n ↦ (b n - xF) / a n) atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro l hl
      filter_upwards [hend (-l / 2) (by linarith)] with n hn
      have h1 : xF ≤ b n + -l / 2 * a n := csInf_le hbdd (hF1 _ hn)
      rw [lt_div_iff₀ (ha n)]
      nlinarith [ha n]
    · intro v hv
      have hvα : 0 < (-(-v)) ^ α := by rw [neg_neg]; exact Real.rpow_pos_of_pos hv _
      filter_upwards [(hz (-v) (by linarith)).eventually (lt_mem_nhds hvα)] with n hn
      have hpos : 0 < u (a n * -v + b n) := by
        by_contra hcon
        push Not at hcon
        have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) n) hcon
        linarith
      have hlt' : a n * -v + b n < xF := by
        by_contra hcon
        push Not at hcon
        have := F.mono' hcon
        change F.toFun xF = 1 at hxF1
        simp only [hu_def] at hpos
        change 0 < 1 - F.toFun (a n * -v + b n) at hpos
        linarith
      rw [div_lt_iff₀ (ha n)]
      linarith
  have hzF := fun z (hz' : z < 0) ↦
    Weibull.tendsto_of_tendsto_mul_affine_shift hu hα ha hd hz hz'
  -- the transformed tail
  set G : ℝ → ℝ := fun t ↦ if 0 < t then u (xF - t⁻¹) else 1 with hG
  have hGa : Antitone G := by
    intro s t hst
    simp only [hG]
    split_ifs with h1 h2 h2
    · exact hu (sub_le_sub_left (inv_anti₀ h2 hst) xF)
    · simp only [hu_def]; linarith [F.apply_nonneg (xF - t⁻¹)]
    · exact absurd (h2.trans_le hst) h1
    · exact le_rfl
  have hGRV : IsRegularlyVarying G (-α) := by
    refine Frechet.isRegularlyVarying_of_tendsto_mul_affine hGa hα (a := fun n ↦ (a n)⁻¹)
      (b := fun _ ↦ 0) (fun n ↦ inv_pos.2 (ha n)) fun y hy ↦ ?_
    have := hzF (-y⁻¹) (neg_neg_of_pos (inv_pos.2 hy))
    rw [inv_neg_inv_rpow_neg hy] at this
    refine this.congr fun n ↦ ?_
    have hpos : 0 < (a n)⁻¹ * y + 0 := by have := ha n; positivity
    simp only [hG, hpos, ↓reduceIte]
    congr 2
    rw [add_zero, mul_inv, inv_inv]
    ring
  refine ⟨xF, hxF1, hlt, hGRV.congr ?_⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [hG, ht, hu_def]

/-- **Gnedenko's theorem** for the Weibull domain of attraction ([dHF, Theorem 1.2.1(2)],
[EKM, Theorem 3.3.12]): a c.d.f. `F` is in the maximum domain of attraction of the Weibull
distribution `Ψ_α` if and only if `F` has a finite right endpoint `x_F` (`F x_F = 1` and
`F x < 1` for `x < x_F`) and `t ↦ 1 - F (x_F - t⁻¹)` is regularly varying with index `-α`. -/
theorem isInMDAWeibull_iff (F : CumulativeDistributionFunction) {α : ℝ} (hα : 0 < α) :
    F.IsInMDAWeibull hα ↔ ∃ xF : ℝ, F xF = 1 ∧ (∀ x < xF, F x < 1) ∧
      IsRegularlyVarying (fun t ↦ 1 - F (xF - t⁻¹)) (-α) :=
  ⟨F.exists_endpoint_of_isInMDAWeibull hα, fun ⟨_, h1, _, hRV⟩ ↦
    F.isInMDAWeibull_of_isRegularlyVarying hα h1 hRV⟩

end CumulativeDistributionFunction
