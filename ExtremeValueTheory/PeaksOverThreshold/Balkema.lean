/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.PeaksOverThreshold.Frechet
import ExtremeValueTheory.DomainOfAttraction.Weibull
import ExtremeValueTheory.DomainOfAttraction.Gumbel
import ExtremeValueTheory.DomainOfAttraction.GumbelNecessity

/-!
# The Pickands–Balkema–de Haan theorem

Let `F` be a c.d.f. with tail `F̄ = 1 - F` and let `F̄_u(x) = F̄ (u + x) / F̄ u` be the
conditional excess survival function (`ExtremeValueTheory.excessSurvival`). The
Pickands–Balkema–de Haan theorem says that, for `F` in the maximum domain of attraction of the
extreme value distribution `H_ξ`, there is a scale function `β(u) > 0` such that

  `sup_{x ≥ 0} |F̄_u (β(u) x) - Ḡ_{ξ,1}(x)| → 0` as `u ↑ x_F`,

where `Ḡ_{ξ,1}(x) = (1 + ξ x)₊ ^ (-1/ξ)` (`exp (-x)` for `ξ = 0`) is the generalized Pareto
survival function and `x_F` is the right endpoint of `F`.

## References

* A. A. Balkema and L. de Haan, *Residual life time at great age*, Ann. Probab. 2 (1974).
* J. Pickands III, *Statistical inference using extreme order statistics*, Ann. Statist. 3
  (1975).
* P. Embrechts, C. Klüppelberg and T. Mikosch, *Modelling Extremal Events*, Springer (1997),
  Theorem 3.4.13 [EKM].
* L. de Haan and A. Ferreira, *Extreme Value Theory: An Introduction*, Springer (2006),
  Theorem 1.1.6 [dHF].

## Main definitions

* `ExtremeValueTheory.gpdSurvival'`: the GPD survival function `(max (1 + ξ x / β) 0) ^ (-1/ξ)`
  for all shapes `ξ ∈ ℝ` (agreeing with `gpdSurvival` for `ξ ≥ 0`, `x ≥ 0`:
  `gpdSurvival'_eq_gpdSurvival`).
* `CumulativeDistributionFunction.IsInMDAGEV F ξ`: `F` is in the maximum domain of attraction
  of `H_ξ` (Fréchet with `α = 1/ξ` for `ξ > 0`, Weibull with `α = -1/ξ` for `ξ < 0`, Gumbel
  for `ξ = 0`).
* `CumulativeDistributionFunction.upperEndpointFilter F`: the filter `u ↑ x_F` (within
  `{F < 1}`); it is `atTop` if `x_F = ∞` and `𝓝[<] x_F` if `x_F < ∞`.

## Main results

* `ExtremeValueTheory.tendstoUniformlyOn_Ici_of_antitoneOn`: a Pólya-type lemma: pointwise
  convergence of antitone functions on `[a, ∞)` to a continuous antitone limit, with matching
  limits at `+∞`, is uniform.
* `ExtremeValueTheory.tendsto_iSup_abs_sub_iff`: uniform convergence in supremum form.
* `CumulativeDistributionFunction.isInMDAFrechet_iff_tendstoUniformlyOn_excessSurvival` and
  `..._iff_tendsto_sup_excessSurvival`: Fréchet case, as an equivalence, `β(u) = u / α`.
* `CumulativeDistributionFunction.isInMDAWeibull_iff_tendstoUniformlyOn_excessSurvival` and
  `..._iff_tendsto_sup_excessSurvival`: Weibull case, as an equivalence,
  `β(u) = (x_F - u) / α`, `u ↑ x_F`.
* `CumulativeDistributionFunction.tendstoUniformlyOn_excessSurvival_of_auxiliary`: Gumbel case
  from an auxiliary function `f`; `isInMDAGumbel_and_tendstoUniformlyOn_of_auxiliary_atTop`
  and `..._nhdsLT` add membership in the Gumbel domain via the existing sufficiency theorems.
* `CumulativeDistributionFunction.exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV`:
  unified statement for all `ξ ∈ ℝ` (for `ξ = 0` an auxiliary function is assumed, since the
  necessity of the auxiliary function is not used here).
-/

open Filter Topology Set Real

namespace ExtremeValueTheory

/-! ### A Pólya-type uniformity lemma -/

/-- **Pólya-type lemma.** Let `f i` be antitone on `[a, ∞)` and bounded below by `c`, and let
them converge pointwise on `[a, ∞)` to a continuous antitone `G` with `G x → c` as `x → ∞`.
Then the convergence is uniform on `[a, ∞)`. -/
theorem tendstoUniformlyOn_Ici_of_antitoneOn {ι : Type*} {L : Filter ι} {f : ι → ℝ → ℝ}
    {G : ℝ → ℝ} {a c : ℝ} (hf : ∀ᶠ i in L, AntitoneOn (f i) (Ici a))
    (hfc : ∀ᶠ i in L, ∀ x ∈ Ici a, c ≤ f i x) (hG : AntitoneOn G (Ici a))
    (hGc : ContinuousOn G (Ici a)) (hGlim : Tendsto G atTop (𝓝 c))
    (hlim : ∀ x ∈ Ici a, Tendsto (fun i => f i x) L (𝓝 (G x))) :
    TendstoUniformlyOn f G L (Ici a) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hGge : ∀ x ∈ Ici a, c ≤ G x := fun x hx =>
    le_of_tendsto hGlim (eventually_atTop.2 ⟨x, fun y hy =>
      hG hx (mem_Ici.2 (le_trans (mem_Ici.1 hx) hy)) hy⟩)
  obtain ⟨M, hMG, hMa⟩ := ((hGlim.eventually (gt_mem_nhds (show c < c + ε / 2 by linarith))).and
    (eventually_ge_atTop a)).exists
  have hUC : UniformContinuousOn G (Icc a M) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hGc.mono Icc_subset_Ici_self)
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.1 hUC (ε / 2) (half_pos hε)
  have hd0 : 0 < δ / 2 := half_pos hδ
  set d := δ / 2 with hd
  set N := ⌈(M - a) / d⌉₊ with hN
  set p : ℕ → ℝ := fun k => min (a + k * d) M with hp
  have hpI : ∀ k, p k ∈ Icc a M := fun k =>
    ⟨le_min (by have : 0 ≤ (k : ℝ) * d := by positivity
                linarith) hMa, min_le_right _ _⟩
  have hNle : M - a ≤ N * d := by
    have h1 : (M - a) / d ≤ N := Nat.le_ceil _
    rwa [div_le_iff₀ hd0] at h1
  have hpN : p N = M := min_eq_right (by linarith)
  have hev : ∀ᶠ i in L, ∀ k ∈ Finset.range (N + 1), dist (G (p k)) (f i (p k)) < ε / 2 :=
    (Finset.range (N + 1)).eventually_all.2 fun k _ =>
      (Metric.tendsto_nhds.1 (hlim (p k) (Icc_subset_Ici_self (hpI k))) (ε / 2)
        (half_pos hε)).mono fun i hi => by rw [dist_comm]; exact hi
  filter_upwards [hf, hfc, hev] with i hfi hfci hevi
  intro x hx
  have hx' : a ≤ x := hx
  rw [Real.dist_eq, abs_lt]
  rcases le_or_gt M x with hxM | hxM
  · have h1 := hevi N (Finset.mem_range.2 (Nat.lt_succ_self N))
    rw [hpN, Real.dist_eq, abs_lt] at h1
    have h2 : f i x ≤ f i M := hfi (mem_Ici.2 hMa) hx hxM
    have h3 := hfci x hx
    have h4 : G x ≤ G M := hG (mem_Ici.2 hMa) hx hxM
    have h5 := hGge x hx
    constructor <;> linarith
  · set k := ⌊(x - a) / d⌋₊ with hk
    have hq0 : 0 ≤ (x - a) / d := div_nonneg (sub_nonneg.2 hx') hd0.le
    have hk1 : (k : ℝ) * d ≤ x - a := by
      have := Nat.floor_le hq0
      rwa [le_div_iff₀ hd0] at this
    have hk2 : x - a < ((k : ℝ) + 1) * d := by
      have := Nat.lt_floor_add_one ((x - a) / d)
      rwa [div_lt_iff₀ hd0] at this
    have hkN : k + 1 ≤ N := by
      have : (k : ℝ) < N := by
        have h1 : (M - a) / d ≤ N := Nat.le_ceil _
        have h2 : (k : ℝ) ≤ (x - a) / d := Nat.floor_le hq0
        have h3 : (x - a) / d < (M - a) / d := div_lt_div_of_pos_right (by linarith) hd0
        linarith
      exact_mod_cast this
    have hpk : p k = a + k * d := min_eq_left (by linarith)
    have hpk1 : x ≤ p (k + 1) := by
      rw [hp]
      exact le_min (by push_cast; linarith) hxM.le
    have hpk1' : p (k + 1) ≤ a + ((k : ℝ) + 1) * d := by
      rw [hp]
      push_cast
      exact min_le_left _ _
    have hxk : p k ≤ x := by rw [hpk]; linarith
    have hdist : dist (G (p k)) (G (p (k + 1))) < ε / 2 := by
      refine hδG _ (hpI k) _ (hpI (k + 1)) ?_
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    rw [Real.dist_eq, abs_lt] at hdist
    have e1 := hevi k (Finset.mem_range.2 (by omega))
    have e2 := hevi (k + 1) (Finset.mem_range.2 (by omega))
    rw [Real.dist_eq, abs_lt] at e1 e2
    have m1 : f i x ≤ f i (p k) := hfi (Icc_subset_Ici_self (hpI k)) hx hxk
    have m2 : f i (p (k + 1)) ≤ f i x := hfi hx (Icc_subset_Ici_self (hpI (k + 1))) hpk1
    have g1 : G x ≤ G (p k) := hG (Icc_subset_Ici_self (hpI k)) hx hxk
    have g2 : G (p (k + 1)) ≤ G x := hG hx (Icc_subset_Ici_self (hpI (k + 1))) hpk1
    constructor <;> linarith

/-- Uniform convergence on `s` is equivalent to convergence of the supremum of the error to `0`,
provided the errors are eventually uniformly bounded. -/
theorem tendsto_iSup_abs_sub_iff {ι : Type*} {L : Filter ι} {f : ι → ℝ → ℝ} {G : ℝ → ℝ}
    {s : Set ℝ} {B : ℝ} (hB : ∀ᶠ i in L, ∀ x ∈ s, |f i x - G x| ≤ B) :
    Tendsto (fun i => ⨆ x ∈ s, |f i x - G x|) L (𝓝 0) ↔ TendstoUniformlyOn f G L s := by
  constructor
  · intro h
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [h.eventually (gt_mem_nhds hε), hB] with i hi hBi x hx
    have hbdd : BddAbove (range fun x => ⨆ (_ : x ∈ s), |f i x - G x|) :=
      ⟨max B 0, by
        rintro _ ⟨y, rfl⟩
        exact Real.iSup_le (fun hy => (hBi y hy).trans (le_max_left _ _)) (le_max_right _ _)⟩
    have : |f i x - G x| ≤ ⨆ x ∈ s, |f i x - G x| := by
      refine le_trans ?_ (le_ciSup hbdd x)
      rw [ciSup_pos hx]
    rw [Real.dist_eq, abs_sub_comm]
    linarith
  · intro hU
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hU (ε / 2) (half_pos hε)] with i hi
    have hb : ∀ x ∈ s, |f i x - G x| ≤ ε / 2 := by
      intro x hx
      have := hi x hx
      rw [Real.dist_eq, abs_sub_comm] at this
      exact this.le
    have hsup0 : 0 ≤ ⨆ x ∈ s, |f i x - G x| :=
      Real.iSup_nonneg fun x => Real.iSup_nonneg fun _ => abs_nonneg _
    have hsup : (⨆ x ∈ s, |f i x - G x|) ≤ ε / 2 :=
      Real.iSup_le (fun x => Real.iSup_le (fun hx => hb x hx) (half_pos hε).le)
        (half_pos hε).le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup0]
    linarith

/-- To check regular variation it suffices to consider `c ≥ 1`. -/
theorem isRegularlyVarying_of_one_le {h : ℝ → ℝ} {ρ : ℝ} (hpos : ∀ᶠ t in atTop, 0 < h t)
    (hlim : ∀ c : ℝ, 1 ≤ c → Tendsto (fun t => h (c * t) / h t) atTop (𝓝 (c ^ ρ))) :
    IsRegularlyVarying h ρ := by
  refine ⟨hpos, fun c hc => ?_⟩
  rcases le_or_gt 1 c with h1 | h1
  · exact hlim c h1
  · have hci : 1 ≤ c⁻¹ := (one_le_inv₀ hc).2 h1.le
    have h2 := ((hlim c⁻¹ hci).comp (tendsto_id.const_mul_atTop hc)).inv₀
      (rpow_pos_of_pos (inv_pos.2 hc) ρ).ne'
    rw [Real.inv_rpow hc.le, inv_inv] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp_apply, id]
    rw [inv_div, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-! ### The generalized Pareto distribution for all shapes -/

/-- The survival function of the generalized Pareto distribution with shape `ξ ∈ ℝ` and scale
`β`: `(max (1 + ξ x / β) 0) ^ (-(1 / ξ))` if `ξ ≠ 0` and `exp (-x / β)` if `ξ = 0`. For
`ξ < 0` it vanishes for `x ≥ -β / ξ`, the right endpoint of the GPD. -/
noncomputable def gpdSurvival' (ξ β x : ℝ) : ℝ :=
  if ξ = 0 then exp (-x / β) else (max (1 + ξ * x / β) 0) ^ (-(1 / ξ))

section GPD

variable {ξ β x : ℝ}

/-- `gpdSurvival'` agrees with `gpdSurvival` for `ξ ≥ 0`, `β > 0`, `x ≥ 0`. -/
theorem gpdSurvival'_eq_gpdSurvival (hξ : 0 ≤ ξ) (hβ : 0 < β) (hx : 0 ≤ x) :
    gpdSurvival' ξ β x = gpdSurvival ξ β x := by
  unfold gpdSurvival' gpdSurvival
  split_ifs
  · rfl
  · have : 0 ≤ ξ * x / β := by positivity
    rw [max_eq_left (by linarith)]

@[simp] theorem gpdSurvival'_zero_left (β x : ℝ) : gpdSurvival' 0 β x = exp (-x / β) := by
  simp [gpdSurvival']

/-- For `α > 0`, `Ḡ_{-1/α,1}(x) = (max (1 - x / α) 0) ^ α`. -/
theorem gpdSurvival'_neg_inv {α : ℝ} (hα : 0 < α) (x : ℝ) :
    gpdSurvival' (-1 / α) 1 x = (max (1 - x / α) 0) ^ α := by
  have hne : (-1 / α) ≠ 0 := div_ne_zero (by norm_num) hα.ne'
  simp only [gpdSurvival', hne, ↓reduceIte]
  congr 1
  · congr 1
    ring
  · field_simp

theorem gpdSurvival'_nonneg (ξ β x : ℝ) : 0 ≤ gpdSurvival' ξ β x := by
  unfold gpdSurvival'
  split_ifs
  · exact (exp_pos _).le
  · exact rpow_nonneg (le_max_right _ _) _

theorem gpdSurvival'_antitoneOn (hβ : 0 < β) : AntitoneOn (gpdSurvival' ξ β) (Ici 0) := by
  rcases lt_or_ge ξ 0 with hξ | hξ
  · intro x hx y hy hxy
    unfold gpdSurvival'
    simp only [hξ.ne, ↓reduceIte]
    have hp : 0 ≤ -(1 / ξ) := by
      have : 1 / ξ < 0 := one_div_neg.2 hξ
      linarith
    refine rpow_le_rpow (le_max_right _ _) (max_le_max ?_ le_rfl) hp
    have : ξ * y / β ≤ ξ * x / β :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonpos_left hxy hξ.le) hβ.le
    linarith
  · intro x hx y hy hxy
    rw [gpdSurvival'_eq_gpdSurvival hξ hβ hx, gpdSurvival'_eq_gpdSurvival hξ hβ hy]
    exact gpdSurvival_antitoneOn hξ hβ hx hy hxy

theorem gpdSurvival'_zero_right (ξ β : ℝ) : gpdSurvival' ξ β 0 = 1 := by
  unfold gpdSurvival'
  split_ifs <;> simp

theorem gpdSurvival'_le_one (hβ : 0 < β) (hx : 0 ≤ x) : gpdSurvival' ξ β x ≤ 1 := by
  simpa [gpdSurvival'_zero_right] using
    gpdSurvival'_antitoneOn (ξ := ξ) hβ (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx

theorem gpdSurvival'_continuousOn (hβ : 0 < β) : ContinuousOn (gpdSurvival' ξ β) (Ici 0) := by
  rcases lt_or_ge ξ 0 with hξ | hξ
  · have : gpdSurvival' ξ β = fun x => (max (1 + ξ * x / β) 0) ^ (-(1 / ξ)) := by
      funext x
      simp only [gpdSurvival', hξ.ne, ↓reduceIte]
    rw [this]
    refine ContinuousOn.rpow_const (by fun_prop) fun x _ => Or.inr ?_
    have : 1 / ξ < 0 := one_div_neg.2 hξ
    linarith
  · exact (gpdSurvival_continuousOn hξ hβ).congr fun x hx =>
      gpdSurvival'_eq_gpdSurvival hξ hβ hx

theorem gpdSurvival'_tendsto_atTop (hβ : 0 < β) :
    Tendsto (gpdSurvival' ξ β) atTop (𝓝 0) := by
  rcases lt_or_ge ξ 0 with hξ | hξ
  · have h1 : Tendsto (fun x : ℝ => 1 + ξ * x / β) atTop atBot :=
      tendsto_atBot_add_const_left _ _
        ((tendsto_id.const_mul_atTop_of_neg hξ).atBot_div_const hβ)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h1.eventually (eventually_le_atBot 0)] with x hx
    have hp : -(1 / ξ) ≠ 0 := by
      have : 1 / ξ < 0 := one_div_neg.2 hξ
      linarith
    simp only [gpdSurvival', hξ.ne, ↓reduceIte]
    rw [max_eq_right hx, zero_rpow hp]
  · refine (gpdSurvival_tendsto_atTop hξ hβ).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact (gpdSurvival'_eq_gpdSurvival hξ hβ hx).symm

end GPD

end ExtremeValueTheory

namespace CumulativeDistributionFunction

open ExtremeValueTheory

variable (F : CumulativeDistributionFunction)

private lemma balkema_antitone : Antitone (fun x ↦ 1 - F x) :=
  fun _ _ h ↦ sub_le_sub_left (F.mono' h) 1

private lemma balkema_nonneg (x : ℝ) : 0 ≤ 1 - F x := by linarith [F.apply_le_one x]

private lemma excess_nonneg (u b : ℝ) : 0 ≤ excessSurvival (fun y ↦ 1 - F y) u b :=
  div_nonneg (F.balkema_nonneg _) (F.balkema_nonneg _)

private lemma excess_le_one {u b : ℝ} (hb : 0 ≤ b) :
    excessSurvival (fun y ↦ 1 - F y) u b ≤ 1 :=
  div_le_one_of_le₀ (F.balkema_antitone (le_add_of_nonneg_right hb)) (F.balkema_nonneg _)

private lemma excess_antitoneOn {u β : ℝ} (hβ : 0 ≤ β) :
    AntitoneOn (fun x ↦ excessSurvival (fun y ↦ 1 - F y) u (β * x)) (Ici 0) := by
  intro x _ y _ hxy
  exact div_le_div_of_nonneg_right
    (F.balkema_antitone (add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy hβ)))
    (F.balkema_nonneg _)

private lemma abs_sub_le_one_of_mem {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (hb1 : b ≤ 1) : |a - b| ≤ 1 :=
  abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-! ### Fréchet case -/

/-- **Pickands–Balkema–de Haan theorem, Fréchet case** ([EKM, Theorem 3.4.13(b)]): `F` is in
the maximum domain of attraction of the Fréchet distribution `Φ_α` if and only if, with
`β(u) = u / α`, the rescaled conditional excess survival function
`x ↦ F̄ (u + β(u) x) / F̄ u` converges to `Ḡ_{1/α,1}` uniformly on `[0, ∞)` as `u → ∞`. -/
theorem isInMDAFrechet_iff_tendstoUniformlyOn_excessSurvival {α : ℝ} (hα : 0 < α) :
    F.IsInMDAFrechet hα ↔
      TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (u / α * x))
        (gpdSurvival (1 / α) 1) atTop (Ici 0) := by
  rw [F.isInMDAFrechet_iff hα]
  constructor
  · intro hRV
    exact IsRegularlyVarying.tendstoUniformlyOn_excessSurvival F.balkema_antitone hRV hα
  · intro hU
    have hpt : ∀ x, 0 ≤ x → Tendsto (fun u ↦ excessSurvival (fun y ↦ 1 - F y) u (u / α * x))
        atTop (𝓝 ((1 + x / α) ^ (-α))) := fun x hx ↦ by
      rw [← gpdSurvival_inv_one hα.ne']
      exact hU.tendsto_at (mem_Ici.2 hx)
    have hpos : ∀ᶠ u in atTop, 0 < 1 - F u := by
      have h0 := hpt 0 le_rfl
      simp only [zero_div, add_zero, one_rpow, mul_zero] at h0
      filter_upwards [h0.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))]
        with u hu
      by_contra hcon
      have h1 : 1 - F u = 0 := le_antisymm (not_lt.1 hcon) (F.balkema_nonneg u)
      simp only [excessSurvival, h1, div_zero] at hu
      linarith
    refine isRegularlyVarying_of_one_le hpos fun c hc ↦ ?_
    have h := hpt (α * (c - 1)) (mul_nonneg hα.le (by linarith))
    rw [show 1 + α * (c - 1) / α = c by field_simp; ring] at h
    refine h.congr fun u ↦ ?_
    simp only [excessSurvival]
    rw [show u + u / α * (α * (c - 1)) = c * u by field_simp; ring]

/-- **Pickands–Balkema–de Haan theorem, Fréchet case**, supremum form:
`F ∈ MDA(Φ_α)` iff `sup_{x ≥ 0} |F̄ (u + (u / α) x) / F̄ u - Ḡ_{1/α,1}(x)| → 0` as `u → ∞`. -/
theorem isInMDAFrechet_iff_tendsto_sup_excessSurvival {α : ℝ} (hα : 0 < α) :
    F.IsInMDAFrechet hα ↔
      Tendsto (fun u ↦ ⨆ x ∈ Ici (0 : ℝ),
        |excessSurvival (fun y ↦ 1 - F y) u (u / α * x) - gpdSurvival (1 / α) 1 x|)
        atTop (𝓝 0) := by
  rw [tendsto_iSup_abs_sub_iff (B := 1), F.isInMDAFrechet_iff_tendstoUniformlyOn_excessSurvival hα]
  filter_upwards [eventually_ge_atTop 0] with u hu x hx
  have hx' : (0 : ℝ) ≤ x := hx
  have hξ : (0 : ℝ) ≤ 1 / α := by positivity
  exact abs_sub_le_one_of_mem (F.excess_nonneg _ _) (F.excess_le_one (by positivity))
    (gpdSurvival_pos hξ one_pos hx').le (gpdSurvival_le_one hξ one_pos hx')

/-! ### Weibull case -/

private lemma tendsto_inv_sub_nhdsLT (xF : ℝ) :
    Tendsto (fun u ↦ (xF - u)⁻¹) (𝓝[<] xF) atTop := by
  have h : Tendsto (fun u ↦ xF - u) (𝓝[<] xF) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun u hu ↦
      mem_Ioi.2 (sub_pos.2 hu)⟩
    have : Tendsto (fun u ↦ xF - u) (𝓝 xF) (𝓝 (xF - xF)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_inv_nhdsGT_zero.comp h

private lemma tendsto_sub_inv_atTop (xF : ℝ) :
    Tendsto (fun t ↦ xF - t⁻¹) atTop (𝓝[<] xF) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_sub xF
    rwa [sub_zero] at this
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact sub_lt_self _ (inv_pos.2 ht)

/-- **Pickands–Balkema–de Haan theorem, Weibull case** ([EKM, Theorem 3.4.13(b)]): `F` is in
the maximum domain of attraction of the Weibull distribution `Ψ_α` if and only if `F` has a
finite right endpoint `x_F` and, with `β(u) = (x_F - u) / α`, the rescaled conditional excess
survival function `x ↦ F̄ (u + β(u) x) / F̄ u` converges to the GPD survival function
`Ḡ_{-1/α,1}(x) = (max (1 - x / α) 0) ^ α` uniformly on `[0, ∞)` as `u ↑ x_F`. -/
theorem isInMDAWeibull_iff_tendstoUniformlyOn_excessSurvival {α : ℝ} (hα : 0 < α) :
    F.IsInMDAWeibull hα ↔ ∃ xF : ℝ, F xF = 1 ∧ (∀ x < xF, F x < 1) ∧
      TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u ((xF - u) / α * x))
        (gpdSurvival' (-1 / α) 1) (𝓝[<] xF) (Ici 0) := by
  rw [F.isInMDAWeibull_iff hα]
  refine exists_congr fun xF ↦ and_congr_right fun h1 ↦ and_congr_right fun hlt ↦ ?_
  have hF1 : ∀ y, xF ≤ y → 1 - F y = 0 := fun y hy ↦ by
    have := le_antisymm (F.apply_le_one y) (h1 ▸ F.mono' hy)
    rw [this, sub_self]
  constructor
  · intro hRV
    refine tendstoUniformlyOn_Ici_of_antitoneOn (c := 0) ?_ ?_ (gpdSurvival'_antitoneOn one_pos)
      (gpdSurvival'_continuousOn one_pos) (gpdSurvival'_tendsto_atTop one_pos) ?_
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact F.excess_antitoneOn (div_nonneg (sub_nonneg.2 (le_of_lt hu)) hα.le)
    · exact Eventually.of_forall fun u x _ ↦ F.excess_nonneg _ _
    · intro x hx
      have hx' : (0 : ℝ) ≤ x := hx
      rw [gpdSurvival'_neg_inv hα]
      rcases lt_or_ge x α with hxα | hxα
      · have hb : 0 < 1 - x / α := by
          rw [sub_pos, div_lt_one hα]
          exact hxα
        set c := (1 - x / α)⁻¹ with hc
        have hc0 : 0 < c := inv_pos.2 hb
        have h := (hRV.2 c hc0).comp (tendsto_inv_sub_nhdsLT xF)
        rw [hc, Real.inv_rpow hb.le, Real.rpow_neg hb.le, inv_inv, ← hc] at h
        rw [max_eq_left hb.le]
        refine h.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu' : xF - u ≠ 0 := (sub_pos.2 hu).ne'
        simp only [Function.comp_apply, excessSurvival]
        simp only [hc, mul_inv, inv_inv]
        congr 3 <;> ring
      · have h0 : max (1 - x / α) 0 = 0 := max_eq_right (by
          rw [sub_nonpos, one_le_div hα]
          exact hxα)
        rw [h0, zero_rpow hα.ne']
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu' : 0 ≤ xF - u := (sub_pos.2 hu).le
        simp only [excessSurvival]
        rw [hF1, zero_div]
        have : (xF - u) / α * α ≤ (xF - u) / α * x :=
          mul_le_mul_of_nonneg_left hxα (div_nonneg hu' hα.le)
        rw [div_mul_cancel₀ _ hα.ne'] at this
        linarith
  · intro hU
    have hpos : ∀ᶠ t in atTop, 0 < 1 - F (xF - t⁻¹) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      have := hlt _ (sub_lt_self xF (inv_pos.2 ht))
      linarith
    refine isRegularlyVarying_of_one_le hpos fun c hc ↦ ?_
    have hc0 : 0 < c := by linarith
    have hci : 0 < c⁻¹ := inv_pos.2 hc0
    have hx : (0 : ℝ) ≤ α * (1 - c⁻¹) :=
      mul_nonneg hα.le (sub_nonneg.2 (inv_le_one_of_one_le₀ hc))
    have h := (hU.tendsto_at (mem_Ici.2 hx)).comp (tendsto_sub_inv_atTop xF)
    rw [gpdSurvival'_neg_inv hα, show 1 - α * (1 - c⁻¹) / α = c⁻¹ by field_simp; ring,
      max_eq_left hci.le, Real.inv_rpow hc0.le, ← Real.rpow_neg hc0.le] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply, excessSurvival]
    congr 3
    field_simp
    ring

/-- **Pickands–Balkema–de Haan theorem, Weibull case**, supremum form. -/
theorem isInMDAWeibull_iff_tendsto_sup_excessSurvival {α : ℝ} (hα : 0 < α) :
    F.IsInMDAWeibull hα ↔ ∃ xF : ℝ, F xF = 1 ∧ (∀ x < xF, F x < 1) ∧
      Tendsto (fun u ↦ ⨆ x ∈ Ici (0 : ℝ),
        |excessSurvival (fun y ↦ 1 - F y) u ((xF - u) / α * x) - gpdSurvival' (-1 / α) 1 x|)
        (𝓝[<] xF) (𝓝 0) := by
  rw [F.isInMDAWeibull_iff_tendstoUniformlyOn_excessSurvival hα]
  refine exists_congr fun xF ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rw [tendsto_iSup_abs_sub_iff (B := 1)]
  filter_upwards [self_mem_nhdsWithin] with u hu x hx
  have hx' : (0 : ℝ) ≤ x := hx
  have hu' : 0 ≤ xF - u := (sub_pos.2 hu).le
  exact abs_sub_le_one_of_mem (F.excess_nonneg _ _)
    (F.excess_le_one (mul_nonneg (div_nonneg hu' hα.le) hx')) (gpdSurvival'_nonneg _ _ _)
    (gpdSurvival'_le_one one_pos hx')

/-! ### Gumbel case -/

/-- **Pickands–Balkema–de Haan theorem, Gumbel case** ([EKM, Theorem 3.4.13(b)],
[dHF, Theorem 1.1.6]): if `f` is an auxiliary function for `F` along a filter `L` (typically
`u ↑ x_F`), i.e. `f > 0` eventually and `F̄ (u + x f(u)) / F̄ u → exp (-x)` for every `x ≥ 0`,
then the rescaled conditional excess survival function `x ↦ F̄ (u + f(u) x) / F̄ u` converges
to `Ḡ_{0,1}(x) = exp (-x)` uniformly on `[0, ∞)`. -/
theorem tendstoUniformlyOn_excessSurvival_of_auxiliary {L : Filter ℝ} {f : ℝ → ℝ}
    (hf : ∀ᶠ u in L, 0 < f u)
    (h : ∀ x, 0 ≤ x → Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) L
      (𝓝 (Real.exp (-x)))) :
    TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (f u * x))
      (gpdSurvival' 0 1) L (Ici 0) := by
  refine tendstoUniformlyOn_Ici_of_antitoneOn (c := 0) ?_ ?_ (gpdSurvival'_antitoneOn one_pos)
    (gpdSurvival'_continuousOn one_pos) (gpdSurvival'_tendsto_atTop one_pos) ?_
  · filter_upwards [hf] with u hu
    exact F.excess_antitoneOn hu.le
  · exact Eventually.of_forall fun u x _ ↦ F.excess_nonneg _ _
  · intro x hx
    rw [gpdSurvival'_zero_left, div_one]
    refine (h x hx).congr fun u ↦ ?_
    simp only [excessSurvival, mul_comm]

/-- **Pickands–Balkema–de Haan theorem, Gumbel case**, supremum form. -/
theorem tendsto_sup_excessSurvival_of_auxiliary {L : Filter ℝ} {f : ℝ → ℝ}
    (hf : ∀ᶠ u in L, 0 < f u)
    (h : ∀ x, 0 ≤ x → Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) L
      (𝓝 (Real.exp (-x)))) :
    Tendsto (fun u ↦ ⨆ x ∈ Ici (0 : ℝ),
      |excessSurvival (fun y ↦ 1 - F y) u (f u * x) - Real.exp (-x)|) L (𝓝 0) := by
  have hG : ∀ x : ℝ, Real.exp (-x) = gpdSurvival' 0 1 x := fun x ↦ by simp
  simp only [hG]
  rw [tendsto_iSup_abs_sub_iff (B := 1)]
  · exact F.tendstoUniformlyOn_excessSurvival_of_auxiliary hf h
  · filter_upwards [hf] with u hu x hx
    have hx' : (0 : ℝ) ≤ x := hx
    exact abs_sub_le_one_of_mem (F.excess_nonneg _ _) (F.excess_le_one (by positivity))
      (gpdSurvival'_nonneg _ _ _) (gpdSurvival'_le_one one_pos hx')

/-- **Gumbel case, infinite right endpoint**: an auxiliary function `f` (with the relation for
all real `x`) gives both membership in the Gumbel domain of attraction (via
`isInMDAGumbel_of_auxiliary_atTop`) and the uniform GPD approximation of the excesses with
`β = f`, `ξ = 0`, as `u → ∞`. -/
theorem isInMDAGumbel_and_tendstoUniformlyOn_of_auxiliary_atTop (hF : ∀ x, F x < 1)
    {f : ℝ → ℝ} (hf : ∀ᶠ t in atTop, 0 < f t)
    (h : ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) atTop
      (𝓝 (Real.exp (-x)))) :
    F.IsInMDAGumbel ∧ TendstoUniformlyOn
      (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (f u * x)) (gpdSurvival' 0 1) atTop
      (Ici 0) :=
  ⟨F.isInMDAGumbel_of_auxiliary_atTop hF hf h,
    F.tendstoUniformlyOn_excessSurvival_of_auxiliary hf fun x _ ↦ h x⟩

/-- **Gumbel case, finite right endpoint**: an auxiliary function `f` (with the relation for
all real `x`, as `t ↑ x_F`) gives both membership in the Gumbel domain of attraction (via
`isInMDAGumbel_of_auxiliary_nhdsLT`) and the uniform GPD approximation of the excesses with
`β = f`, `ξ = 0`, as `u ↑ x_F`. -/
theorem isInMDAGumbel_and_tendstoUniformlyOn_of_auxiliary_nhdsLT {xF : ℝ}
    (hlt : ∀ x < xF, F x < 1) (heq : F xF = 1) {f : ℝ → ℝ}
    (hf : ∀ᶠ t in 𝓝[<] xF, 0 < f t)
    (h : ∀ x, Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) (𝓝[<] xF)
      (𝓝 (Real.exp (-x)))) :
    F.IsInMDAGumbel ∧ TendstoUniformlyOn
      (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (f u * x)) (gpdSurvival' 0 1) (𝓝[<] xF)
      (Ici 0) :=
  ⟨F.isInMDAGumbel_of_auxiliary_nhdsLT hlt heq hf h,
    F.tendstoUniformlyOn_excessSurvival_of_auxiliary hf fun x _ ↦ h x⟩

/-! ### Unified statement -/

/-- `F` is in the maximum domain of attraction of the extreme value distribution `H_ξ`:
of the Fréchet distribution `Φ_{1/ξ}` if `ξ > 0`, of the Weibull distribution `Ψ_{-1/ξ}` if
`ξ < 0`, and of the Gumbel distribution `Λ` if `ξ = 0`. -/
def IsInMDAGEV (ξ : ℝ) : Prop :=
  if hξ : 0 < ξ then F.IsInMDAFrechet (one_div_pos.2 hξ)
  else if hξ' : ξ < 0 then F.IsInMDAWeibull (div_pos_of_neg_of_neg neg_one_lt_zero hξ')
  else F.IsInMDAGumbel

/-- The filter `u ↑ x_F`, where `x_F = sup {x | F x < 1}` is the right endpoint of `F`: it is
generated by the sets `(x, ∞) ∩ {F < 1}` with `F x < 1`. -/
def upperEndpointFilter : Filter ℝ :=
  ⨅ x ∈ {x | F x < 1}, 𝓟 (Ioi x ∩ {y | F y < 1})

/-- If `x_F = ∞`, the filter `u ↑ x_F` is `atTop`. -/
theorem upperEndpointFilter_eq_atTop (hF : ∀ x, F x < 1) : F.upperEndpointFilter = atTop := by
  have hS : {x | F x < 1} = univ := eq_univ_of_forall hF
  rw [upperEndpointFilter, hS, atTop_basis_Ioi.eq_iInf]
  simp

/-- If `x_F < ∞`, the filter `u ↑ x_F` is `𝓝[<] x_F`. -/
theorem upperEndpointFilter_eq_nhdsLT {xF : ℝ} (h1 : F xF = 1) (hlt : ∀ x < xF, F x < 1) :
    F.upperEndpointFilter = 𝓝[<] xF := by
  have hS : {x | F x < 1} = Iio xF := by
    ext y
    refine ⟨fun hy ↦ ?_, fun hy ↦ hlt y hy⟩
    by_contra hcon
    have := F.mono' (not_lt.1 hcon)
    change F y < 1 at hy
    change F xF ≤ F y at this
    linarith
  rw [upperEndpointFilter, hS, (nhdsLT_basis xF).eq_biInf]
  simp only [mem_Iio, Ioi_inter_Iio]

/-- **Pickands–Balkema–de Haan theorem, unified form**: if `F ∈ MDA(H_ξ)`, then there is a
scale function `β > 0` with `sup_{x ≥ 0} |F̄ (u + β(u) x) / F̄ u - Ḡ_{ξ,1}(x)| → 0` (uniform
convergence on `[0, ∞)`) as `u ↑ x_F`. For `ξ = 0` an auxiliary function along `u ↑ x_F` is
assumed (the hypothesis `haux` is vacuous for `ξ ≠ 0`). -/
theorem exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV {ξ : ℝ} (hF : F.IsInMDAGEV ξ)
    (haux : ξ = 0 → ∃ f : ℝ → ℝ, (∀ᶠ u in F.upperEndpointFilter, 0 < f u) ∧
      ∀ x, 0 ≤ x → Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) F.upperEndpointFilter
        (𝓝 (Real.exp (-x)))) :
    ∃ β : ℝ → ℝ, (∀ᶠ u in F.upperEndpointFilter, 0 < β u) ∧
      TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
        (gpdSurvival' ξ 1) F.upperEndpointFilter (Ici 0) := by
  unfold IsInMDAGEV at hF
  split_ifs at hF with hξ hξ'
  · -- Fréchet
    have hα : 0 < 1 / ξ := one_div_pos.2 hξ
    have hRV := (F.isInMDAFrechet_iff hα).1 hF
    have hpos := IsRegularlyVarying.pos_of_antitone F.balkema_antitone hRV.1
    have hlt : ∀ x, F x < 1 := fun x ↦ by linarith [hpos x]
    rw [F.upperEndpointFilter_eq_atTop hlt]
    refine ⟨fun u ↦ u / (1 / ξ), ?_, ?_⟩
    · filter_upwards [eventually_gt_atTop 0] with u hu
      positivity
    · have hU := (F.isInMDAFrechet_iff_tendstoUniformlyOn_excessSurvival hα).1 hF
      rw [one_div_one_div] at hU
      exact hU.congr_right fun x hx ↦ (gpdSurvival'_eq_gpdSurvival hξ.le one_pos hx).symm
  · -- Weibull
    have hα : 0 < -1 / ξ := div_pos_of_neg_of_neg neg_one_lt_zero hξ'
    obtain ⟨xF, h1, hlt, hU⟩ :=
      (F.isInMDAWeibull_iff_tendstoUniformlyOn_excessSurvival hα).1 hF
    rw [F.upperEndpointFilter_eq_nhdsLT h1 hlt]
    refine ⟨fun u ↦ (xF - u) / (-1 / ξ), ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact div_pos (sub_pos.2 hu) hα
    · rwa [show -1 / (-1 / ξ) = ξ by field_simp] at hU
  · -- Gumbel
    have h0 : ξ = 0 := le_antisymm (not_lt.1 hξ) (not_lt.1 hξ')
    subst h0
    obtain ⟨f, hf, h⟩ := haux rfl
    exact ⟨f, hf, F.tendstoUniformlyOn_excessSurvival_of_auxiliary hf h⟩

/-- In the Gumbel case an auxiliary function always exists (de Haan's theorem,
`exists_auxiliary_atTop_of_isInMDAGumbel` / `exists_auxiliary_nhdsLT_of_isInMDAGumbel`), along
the filter `u ↑ x_F`. -/
theorem exists_auxiliary_upperEndpointFilter_of_isInMDAGumbel (h : F.IsInMDAGumbel) :
    ∃ f : ℝ → ℝ, (∀ᶠ u in F.upperEndpointFilter, 0 < f u) ∧
      ∀ x, 0 ≤ x → Tendsto (fun t ↦ (1 - F (t + x * f t)) / (1 - F t)) F.upperEndpointFilter
        (𝓝 (Real.exp (-x))) := by
  by_cases hF : ∀ x, F x < 1
  · obtain ⟨f, hf, hlim⟩ := F.exists_auxiliary_atTop_of_isInMDAGumbel hF h
    rw [F.upperEndpointFilter_eq_atTop hF]
    exact ⟨f, Eventually.of_forall hf, fun x _ ↦ hlim x⟩
  · obtain ⟨xF, hlt, heq⟩ := F.exists_rightEndpoint_of_not_lt_one hF
    obtain ⟨f, hf, hlim⟩ := F.exists_auxiliary_nhdsLT_of_isInMDAGumbel hlt heq h
    rw [F.upperEndpointFilter_eq_nhdsLT heq hlt]
    exact ⟨f, Eventually.of_forall hf, fun x _ ↦ hlim x⟩

/-- **Pickands–Balkema–de Haan theorem**: if `F` is in the domain of attraction of the
generalized extreme value law with shape `ξ ∈ ℝ`, there is a scale function `β > 0` such that the
scaled excess distribution `F̄(u + β(u) x) / F̄(u)` converges to the generalized Pareto survival
function with shape `ξ`, uniformly in `x ≥ 0`, as `u` tends to the right endpoint of `F`. -/
theorem exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV' {ξ : ℝ} (hF : F.IsInMDAGEV ξ) :
    ∃ β : ℝ → ℝ, (∀ᶠ u in F.upperEndpointFilter, 0 < β u) ∧
      TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
        (gpdSurvival' ξ 1) F.upperEndpointFilter (Ici 0) := by
  refine F.exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV hF fun hξ ↦ ?_
  subst hξ
  exact F.exists_auxiliary_upperEndpointFilter_of_isInMDAGumbel (by simpa [IsInMDAGEV] using hF)

end CumulativeDistributionFunction
