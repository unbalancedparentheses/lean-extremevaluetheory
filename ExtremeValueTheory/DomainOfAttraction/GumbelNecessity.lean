/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.DomainOfAttraction.Gumbel

/-!
# The Gumbel maximum domain of attraction: necessity of the auxiliary function

We prove the converse of the auxiliary-function criterion of
`ExtremeValueTheory.DomainOfAttraction.Gumbel` (de Haan's theorem): if `F` is in the maximum
domain of attraction of the Gumbel distribution `Λ(x) = exp (-exp (-x))`, and `x_F ∈ (-∞, ∞]` is
the right endpoint of `F`, then there is a positive *auxiliary function* `f` with
`(1 - F (t + x * f t)) / (1 - F t) → exp (-x)` as `t ↑ x_F`, for every real `x`.
Combined with the sufficiency direction this gives a characterization of the Gumbel domain of
attraction, both for `x_F = +∞` and for a finite right endpoint.

## References

* L. de Haan, *On regular variation and its application to the weak convergence of sample
  extremes*, Mathematical Centre Tracts 32, Amsterdam (1970).
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 1.2.5 and Appendix B.2–B.3 (`Γ`-variation and `Π`-variation) [dHF].
* S. I. Resnick, *Extreme Values, Regular Variation, and Point Processes*, Springer (1987),
  Propositions 0.10 and 1.4 [Resnick].
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Theorem 3.3.26 [EKM].

## Main results

* `ExtremeValueTheory.Gumbel.exists_auxiliary_of_tendsto_mul`: the analytic core, for an
  antitone tail `g` with `n * g (a n * x + b n) → exp (-x)`, along an abstract filter `L`
  describing `t ↑ x_F`.
* `CumulativeDistributionFunction.exists_auxiliary_atTop_of_isInMDAGumbel`,
  `CumulativeDistributionFunction.exists_auxiliary_nhdsLT_of_isInMDAGumbel`: necessity, for
  infinite and finite right endpoint.
* `CumulativeDistributionFunction.isInMDAGumbel_iff_atTop`,
  `CumulativeDistributionFunction.isInMDAGumbel_iff_nhdsLT`: the characterizations.
* `CumulativeDistributionFunction.isInMDAGumbel_iff`: the characterization with a case split on
  whether `F` reaches `1`.

## Proof sketch

The classical route goes through `Π`-variation of the quantile function `U = F^← (1 - 1 / ·)` and
the fact that inverses of `Π`-varying functions are `Γ`-varying. We use instead a direct
sandwich argument, in the spirit of the necessity proof for the Fréchet domain of attraction.
Writing `g = 1 - F` and `(A n)⁻¹ x = a n * x + b n`, we have
`n * g (a n * x + b n) → exp (-x)`. Comparing the levels `n` and `n + 1` by monotonicity of `g`
gives `b (n + 1) < b n + δ * a n` eventually, for every `δ > 0`. For `t` close to `x_F` let
`N t = sup {n | b n ≤ t}`, so that `b (N t) ≤ t < b (N t + 1)` and `N t → ∞`. With
`f t = a (N t)`, both `t + x * f t` and `t` are trapped (up to `δ * a (N t)`) between the points
`b (N t) + y * a (N t)` at which the asymptotics of `g` are known, which yields
`g (t + x * f t) / g t → exp (-x)`.
-/

open Filter Topology Set

namespace ExtremeValueTheory

namespace Gumbel

/-- If `n * g (p n) → μ` and `n * g (q n) → ν` with `ν < μ` and `g` antitone, then eventually
`p n < q n`. -/
lemma eventually_lt_of_tendsto_natCast_mul {g : ℝ → ℝ} (hg : Antitone g) {p q : ℕ → ℝ}
    {μ ν : ℝ} (hp : Tendsto (fun n : ℕ ↦ (n : ℝ) * g (p n)) atTop (𝓝 μ))
    (hq : Tendsto (fun n : ℕ ↦ (n : ℝ) * g (q n)) atTop (𝓝 ν)) (hμν : ν < μ) :
    ∀ᶠ n in atTop, p n < q n := by
  filter_upwards [hp.eventually (lt_mem_nhds (show (μ + ν) / 2 < μ by linarith)),
    hq.eventually (gt_mem_nhds (show ν < (μ + ν) / 2 by linarith))] with n h1 h2
  by_contra hcon
  push Not at hcon
  have := mul_le_mul_of_nonneg_left (hg hcon) (Nat.cast_nonneg (α := ℝ) n)
  linarith

/-- If `n * g (b n) → 1`, `g` is antitone and `g t > 0`, then eventually `t < b n`. -/
lemma eventually_lt_of_tendsto_natCast_mul_one {g : ℝ → ℝ} (hg : Antitone g) {b : ℕ → ℝ}
    (hb : Tendsto (fun n : ℕ ↦ (n : ℝ) * g (b n)) atTop (𝓝 1)) {t : ℝ} (ht : 0 < g t) :
    ∀ᶠ n in atTop, t < b n := by
  have hN : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [(hN.atTop_mul_const ht).eventually_gt_atTop 2,
    hb.eventually (gt_mem_nhds one_lt_two)] with n h1 h2
  by_contra hcon
  push Not at hcon
  have := mul_le_mul_of_nonneg_left (hg hcon) (Nat.cast_nonneg (α := ℝ) n)
  linarith

/-- **Necessity of the auxiliary function, analytic core** ([dHF, Theorem 1.2.5],
[Resnick, Proposition 1.4]): let `g` be antitone with `n * g (a n * x + b n) → exp (-x)` for
every `x`, where `a n > 0`. Let `L` be a filter on `ℝ` (describing `t ↑ x_F`) such that for
`t` eventually in `L` the levels `b n` eventually exceed `t`, and such that for every `K` there is
eventually some `n ≥ K` with `b n ≤ t`. Then there is a positive function `f` with
`g (t + x * f t) / g t → exp (-x)` along `L`, for every `x`. -/
theorem exists_auxiliary_of_tendsto_mul {g : ℝ → ℝ} (hg : Antitone g) {a b : ℕ → ℝ}
    (ha : ∀ n, 0 < a n)
    (h : ∀ x, Tendsto (fun n : ℕ ↦ (n : ℝ) * g (a n * x + b n)) atTop (𝓝 (Real.exp (-x))))
    {L : Filter ℝ} (h1 : ∀ᶠ t in L, ∀ᶠ n in atTop, t < b n)
    (h2 : ∀ K : ℕ, ∀ᶠ t in L, ∃ n ≥ K, b n ≤ t) :
    ∃ f : ℝ → ℝ, (∀ t, 0 < f t) ∧
      ∀ x, Tendsto (fun t ↦ g (t + x * f t) / g t) L (𝓝 (Real.exp (-x))) := by
  set N : ℝ → ℕ := fun t ↦ sSup {n | b n ≤ t} with hN
  have hbdd : ∀ᶠ t in L, BddAbove {n | b n ≤ t} := by
    filter_upwards [h1] with t ht
    obtain ⟨K, hK⟩ := eventually_atTop.1 ht
    refine ⟨K, fun n hn ↦ ?_⟩
    by_contra hlt
    push Not at hlt
    exact absurd (show b n ≤ t from hn) (not_le.2 (hK n hlt.le))
  have hNle : ∀ᶠ t in L, b (N t) ≤ t ∧ t < b (N t + 1) := by
    filter_upwards [hbdd, h2 0] with t hB hex
    obtain ⟨n, -, hn⟩ := hex
    refine ⟨Nat.sSup_mem ⟨n, hn⟩ hB, ?_⟩
    by_contra hcon
    push Not at hcon
    exact Nat.not_succ_le_self _ (le_csSup hB (show N t + 1 ∈ {n | b n ≤ t} from hcon))
  have hNtop : Tendsto N L atTop := by
    refine tendsto_atTop.2 fun K ↦ ?_
    filter_upwards [hbdd, h2 K] with t hB hex
    obtain ⟨n, hnK, hn⟩ := hex
    exact hnK.trans (le_csSup hB hn)
  have hb0 : Tendsto (fun n : ℕ ↦ (n : ℝ) * g (b n)) atTop (𝓝 1) := by
    simpa using h 0
  have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) * g (b (n + 1))) atTop (𝓝 1) := by
    have h' : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * g (b (n + 1))) atTop (𝓝 1) := by
      simpa using (tendsto_add_atTop_iff_nat 1).2 hb0
    have := h'.mul (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1)
    rw [one_mul] at this
    refine this.congr fun n ↦ ?_
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hstep : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, b (n + 1) < a n * δ + b n := fun δ hδ ↦
    eventually_lt_of_tendsto_natCast_mul hg hshift (h δ)
      (Real.exp_lt_one_iff.2 (by linarith))
  have hpos : ∀ y, ∀ᶠ n : ℕ in atTop, 0 < g (a n * y + b n) := by
    intro y
    filter_upwards [(h y).eventually (lt_mem_nhds (Real.exp_pos (-y)))] with n hn
    by_contra hcon
    push Not at hcon
    have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) n) hcon
    linarith
  have hdiv : ∀ y z, Tendsto (fun n : ℕ ↦ g (a n * y + b n) / g (a n * z + b n)) atTop
      (𝓝 (Real.exp (-y) / Real.exp (-z))) := by
    intro y z
    refine ((h y).div (h z) (Real.exp_pos _).ne').congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    exact mul_div_mul_left _ _ this
  refine ⟨fun t ↦ a (N t), fun t ↦ ha _, fun x ↦ ?_⟩
  rw [tendsto_order]
  refine ⟨fun l hl ↦ ?_, fun u hu ↦ ?_⟩
  · have hc : Tendsto (fun δ : ℝ ↦ Real.exp (-(x + δ))) (𝓝 0) (𝓝 (Real.exp (-x))) :=
      (by fun_prop : Continuous fun δ : ℝ ↦ Real.exp (-(x + δ))).tendsto' 0 _ (by simp)
    obtain ⟨δ, hδl, hδ⟩ := (((hc.mono_left nhdsWithin_le_nhds).eventually
      (lt_mem_nhds hl)).and (self_mem_nhdsWithin (s := Ioi 0))).exists
    have hδ' : (0 : ℝ) < δ := hδ
    have hlim := hdiv (x + δ) 0
    rw [neg_zero, Real.exp_zero, div_one] at hlim
    filter_upwards [hNtop.eventually ((hlim.eventually (lt_mem_nhds hδl)).and
      ((hpos (x + δ)).and ((hpos δ).and (hstep δ hδ')))), hNle]
      with t hev hs
    obtain ⟨r1, r2, r3, r4⟩ := hev
    obtain ⟨s1, s2⟩ := hs
    simp only [mul_zero, zero_add] at r1
    set n := N t
    have e0 : a n * (x + δ) + b n = (a n * δ + b n) + x * a n := by ring
    have e1 : g (a n * (x + δ) + b n) ≤ g (t + x * a n) := hg (by rw [e0]; linarith)
    have e2 : g (a n * δ + b n) ≤ g t := hg (by linarith)
    have hgt : 0 < g t := r3.trans_le e2
    calc l < g (a n * (x + δ) + b n) / g (b n) := r1
      _ ≤ g (t + x * a n) / g t :=
        div_le_div₀ (r2.le.trans e1) e1 hgt (hg s1)
  · have hc : Tendsto (fun δ : ℝ ↦ Real.exp (-x + δ)) (𝓝 0) (𝓝 (Real.exp (-x))) :=
      (by fun_prop : Continuous fun δ : ℝ ↦ Real.exp (-x + δ)).tendsto' 0 _ (by simp)
    obtain ⟨δ, hδu, hδ⟩ := (((hc.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds hu)).and (self_mem_nhdsWithin (s := Ioi 0))).exists
    have hδ' : (0 : ℝ) < δ := hδ
    have hlim := hdiv x δ
    rw [← Real.exp_sub, sub_neg_eq_add] at hlim
    filter_upwards [hNtop.eventually ((hlim.eventually (gt_mem_nhds hδu)).and
      ((hpos x).and ((hpos δ).and (hstep δ hδ')))), hNle]
      with t hev hs
    obtain ⟨r1, r2, r3, r4⟩ := hev
    obtain ⟨s1, s2⟩ := hs
    set n := N t
    have e1 : g (t + x * a n) ≤ g (a n * x + b n) := hg (by linarith [mul_comm x (a n)])
    have e2 : g (a n * δ + b n) ≤ g t := hg (by linarith)
    calc g (t + x * a n) / g t ≤ g (a n * x + b n) / g (a n * δ + b n) :=
        div_le_div₀ r2.le e1 r3 e2
      _ < u := r1

end Gumbel

end ExtremeValueTheory

namespace CumulativeDistributionFunction

open ExtremeValueTheory

private lemma gumbelNec_standardGumbelCDF_mem_Ioo (x : ℝ) : standardGumbelCDF x ∈ Ioo 0 1 := by
  rw [standardGumbelCDF_apply_eq]
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith [Real.exp_pos (-x)])⟩

private lemma gumbelNec_neg_log_standardGumbelCDF (x : ℝ) :
    -Real.log (standardGumbelCDF x) = Real.exp (-x) := by
  rw [standardGumbelCDF_apply_eq, Real.log_exp, neg_neg]

private lemma gumbelNec_antitone_one_sub (F : CumulativeDistributionFunction) :
    Antitone (fun x ↦ 1 - F x) :=
  fun _ _ h ↦ sub_le_sub_left (F.mono' h) 1

/-- If `F` is in the Gumbel domain of attraction, there are `a n > 0` and `b n` with
`n * (1 - F (a n * x + b n)) → exp (-x)` for every `x`. -/
theorem tendsto_mul_of_isInMDAGumbel (F : CumulativeDistributionFunction)
    (hF : F.IsInMDAGumbel) :
    ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧
      ∀ x, Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - F (a n * x + b n))) atTop
        (𝓝 (Real.exp (-x))) := by
  obtain ⟨As, hAs⟩ := hF
  have happ : ∀ n x, (As n • F) x = F ((As n)⁻¹.coefs.1 * x + (As n)⁻¹.coefs.2) := by
    intro n x
    rw [mulAction_apply_eq, AffineIncrEquiv.apply_eq]
  refine ⟨fun n ↦ (As n)⁻¹.coefs.1, fun n ↦ (As n)⁻¹.coefs.2,
    fun n ↦ (As n)⁻¹.coefs_fst_pos, fun x ↦ ?_⟩
  have := ((tfae_ev_limit_relation (F := F) As
    (gumbelNec_standardGumbelCDF_mem_Ioo x)).out 1 3).1 (hAs x)
  rw [gumbelNec_neg_log_standardGumbelCDF] at this
  simpa only [happ] using this

/-- **Necessity of the auxiliary function, infinite right endpoint** ([dHF, Theorem 1.2.5],
[Resnick, Proposition 1.4], [EKM, Theorem 3.3.26]): if `F < 1` everywhere and `F` is in the
Gumbel domain of attraction, then there is a positive function `f` with
`(1 - F (t + x * f t)) / (1 - F t) → exp (-x)` as `t → ∞`, for every `x`. -/
theorem exists_auxiliary_atTop_of_isInMDAGumbel (F : CumulativeDistributionFunction)
    (hF : ∀ x, F x < 1) (h : F.IsInMDAGumbel) :
    ∃ f : ℝ → ℝ, (∀ t, 0 < f t) ∧
      ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) atTop
        (𝓝 (Real.exp (-x))) := by
  obtain ⟨a, b, ha, hlim⟩ := F.tendsto_mul_of_isInMDAGumbel h
  have hb : Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - F (b n))) atTop (𝓝 1) := by
    simpa using hlim 0
  refine Gumbel.exists_auxiliary_of_tendsto_mul F.gumbelNec_antitone_one_sub ha hlim
    (Eventually.of_forall fun t ↦
      Gumbel.eventually_lt_of_tendsto_natCast_mul_one F.gumbelNec_antitone_one_sub hb
        (by linarith [hF t])) fun K ↦ ?_
  filter_upwards [eventually_ge_atTop (b K)] with t ht
  exact ⟨K, le_rfl, ht⟩

/-- **Necessity of the auxiliary function, finite right endpoint** ([dHF, Theorem 1.2.5],
[Resnick, Proposition 1.4], [EKM, Theorem 3.3.26]): if `x_F` is the right endpoint of `F`
(`F < 1` on `(-∞, x_F)` and `F x_F = 1`) and `F` is in the Gumbel domain of attraction, then
there is a positive function `f` with `(1 - F (t + x * f t)) / (1 - F t) → exp (-x)` as
`t ↑ x_F`, for every `x`. -/
theorem exists_auxiliary_nhdsLT_of_isInMDAGumbel (F : CumulativeDistributionFunction)
    {xF : ℝ} (hlt : ∀ x < xF, F x < 1) (heq : F xF = 1) (h : F.IsInMDAGumbel) :
    ∃ f : ℝ → ℝ, (∀ t, 0 < f t) ∧
      ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) (𝓝[<] xF)
        (𝓝 (Real.exp (-x))) := by
  obtain ⟨a, b, ha, hlim⟩ := F.tendsto_mul_of_isInMDAGumbel h
  have hb : Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - F (b n))) atTop (𝓝 1) := by
    simpa using hlim 0
  refine Gumbel.exists_auxiliary_of_tendsto_mul F.gumbelNec_antitone_one_sub ha hlim
    (eventually_nhdsWithin_of_forall fun t ht ↦
      Gumbel.eventually_lt_of_tendsto_natCast_mul_one F.gumbelNec_antitone_one_sub hb
        (by linarith [hlt t ht])) fun K ↦ ?_
  obtain ⟨n, hn1, hnK⟩ := ((hb.eventually (lt_mem_nhds zero_lt_one)).and
    (eventually_ge_atTop K)).exists
  have hbn : b n < xF := by
    by_contra hcon
    push Not at hcon
    have h1 : F xF ≤ F (b n) := F.mono' hcon
    rw [heq] at h1
    have h2 : 1 - F (b n) ≤ 0 := by linarith
    have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) n) h2
    linarith
  filter_upwards [Ioo_mem_nhdsLT hbn] with t ht
  exact ⟨n, hnK, ht.1.le⟩

/-- **Characterization of the Gumbel domain of attraction, infinite right endpoint**
([dHF, Theorems 1.1.8 and 1.2.5], [EKM, Theorem 3.3.26], [Resnick, Propositions 1.1 and 1.4]):
if `F < 1` everywhere, then `F` is in the Gumbel domain of attraction if and only if there is an
eventually positive auxiliary function `f` with `(1 - F (t + x * f t)) / (1 - F t) → exp (-x)`
as `t → ∞`, for every `x`. -/
theorem isInMDAGumbel_iff_atTop (F : CumulativeDistributionFunction) (hF : ∀ x, F x < 1) :
    F.IsInMDAGumbel ↔ ∃ f : ℝ → ℝ, (∀ᶠ t in atTop, 0 < f t) ∧
      ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) atTop
        (𝓝 (Real.exp (-x))) := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf, hl⟩ ↦ F.isInMDAGumbel_of_auxiliary_atTop hF hf hl⟩
  obtain ⟨f, hf, hl⟩ := F.exists_auxiliary_atTop_of_isInMDAGumbel hF h
  exact ⟨f, Eventually.of_forall hf, hl⟩

/-- **Characterization of the Gumbel domain of attraction, finite right endpoint**
([dHF, Theorems 1.1.8 and 1.2.5], [EKM, Theorem 3.3.26], [Resnick, Propositions 1.1 and 1.4]):
if `x_F` is the right endpoint of `F` (`F < 1` on `(-∞, x_F)` and `F x_F = 1`), then `F` is in
the Gumbel domain of attraction if and only if there is an auxiliary function `f`, positive
near `x_F`, with `(1 - F (t + x * f t)) / (1 - F t) → exp (-x)` as `t ↑ x_F`, for every `x`. -/
theorem isInMDAGumbel_iff_nhdsLT (F : CumulativeDistributionFunction) {xF : ℝ}
    (hlt : ∀ x < xF, F x < 1) (heq : F xF = 1) :
    F.IsInMDAGumbel ↔ ∃ f : ℝ → ℝ, (∀ᶠ t in 𝓝[<] xF, 0 < f t) ∧
      ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) (𝓝[<] xF)
        (𝓝 (Real.exp (-x))) := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf, hl⟩ ↦ F.isInMDAGumbel_of_auxiliary_nhdsLT hlt heq hf hl⟩
  obtain ⟨f, hf, hl⟩ := F.exists_auxiliary_nhdsLT_of_isInMDAGumbel hlt heq h
  exact ⟨f, Eventually.of_forall hf, hl⟩

/-- If `F` reaches `1`, it has a finite right endpoint `x_F`: `F < 1` on `(-∞, x_F)` and
`F x_F = 1`. -/
theorem exists_rightEndpoint_of_not_lt_one (F : CumulativeDistributionFunction)
    (hF : ¬ ∀ x, F x < 1) : ∃ xF : ℝ, (∀ x < xF, F x < 1) ∧ F xF = 1 := by
  push Not at hF
  obtain ⟨x₁, hx₁⟩ := hF
  obtain ⟨y₀, hy₀⟩ := (F.tendsto_atBot.eventually (gt_mem_nhds one_pos)).exists
  have hq := Gumbel.quantile_spec (c := 0) F.gumbelNec_antitone_one_sub
    (fun x ↦ continuousWithinAt_const.sub (F.right_continuous x))
    ⟨x₁, by show 1 - F x₁ ≤ 0; linarith⟩ ⟨y₀, by show 0 < 1 - F y₀; linarith⟩
  refine ⟨sInf {x | 1 - F x ≤ 0}, fun x hx ↦ ?_, ?_⟩
  · have := hq.2 x hx
    linarith
  · have := hq.1
    linarith [F.apply_le_one (sInf {x | 1 - F x ≤ 0})]

/-- **De Haan's characterization of the Gumbel domain of attraction** ([dHF, Theorems 1.1.8
and 1.2.5], [EKM, Theorem 3.3.26], [Resnick, Propositions 1.1 and 1.4]): `F` is in the Gumbel
domain of attraction if and only if, with `x_F ∈ (-∞, ∞]` its right endpoint, there is an
auxiliary function `f`, positive near `x_F`, with `(1 - F (t + x * f t)) / (1 - F t) → exp (-x)`
as `t ↑ x_F`, for every `x`. The two disjuncts are the cases `x_F = +∞` and `x_F < ∞`. -/
theorem isInMDAGumbel_iff (F : CumulativeDistributionFunction) :
    F.IsInMDAGumbel ↔
      ((∀ x, F x < 1) ∧ ∃ f : ℝ → ℝ, (∀ᶠ t in atTop, 0 < f t) ∧
        ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) atTop
          (𝓝 (Real.exp (-x)))) ∨
      ∃ xF : ℝ, (∀ x < xF, F x < 1) ∧ F xF = 1 ∧ ∃ f : ℝ → ℝ, (∀ᶠ t in 𝓝[<] xF, 0 < f t) ∧
        ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) (𝓝[<] xF)
          (𝓝 (Real.exp (-x))) := by
  constructor
  · intro h
    by_cases hF : ∀ x, F x < 1
    · exact Or.inl ⟨hF, (F.isInMDAGumbel_iff_atTop hF).1 h⟩
    · obtain ⟨xF, hlt, heq⟩ := F.exists_rightEndpoint_of_not_lt_one hF
      exact Or.inr ⟨xF, hlt, heq, (F.isInMDAGumbel_iff_nhdsLT hlt heq).1 h⟩
  · rintro (⟨hF, hex⟩ | ⟨xF, hlt, heq, hex⟩)
    · exact (F.isInMDAGumbel_iff_atTop hF).2 hex
    · exact (F.isInMDAGumbel_iff_nhdsLT hlt heq).2 hex

end CumulativeDistributionFunction
