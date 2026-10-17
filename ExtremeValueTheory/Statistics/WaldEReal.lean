/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Wald

/-!
# Wald's consistency theorem for extended-real criteria

Wald's theorem (`ExtremeValueTheory.ae_tendsto_of_wald`) for a real-valued criterion needs a
two-sided integrable envelope `|m(θ, x)| ≤ G(x)`. For log-likelihoods of families with a
parameter-dependent support (the generalized Pareto law with `ξ < 0`), the natural criterion is
the log-density with `log 0 = -∞`, which takes the value `-∞` on a set of positive probability.
This file proves the theorem in the form of Wald (1949) and Kiefer–Wolfowitz (1956):

Let `Θ` be a compact metric space and `m : Θ → α → [-∞, ∞)` (an `EReal`-valued criterion) with

* `θ ↦ m(θ, x)` upper semicontinuous for every `x`;
* the local suprema `x ↦ sup_{θ' ∈ B(θ, r)} m(θ', x)` measurable (automatic for criteria
  continuous in `θ`, see `ae_tendsto_of_wald_ereal_of_continuous`);
* an integrable *upper* envelope: `m(θ, x) ≤ G(x)` for all `θ`, with `G` integrable;
* at the true parameter `θ₀`, `m(θ₀, X)` is a.s. finite and integrable;
* identifiability: `E m(θ, X) < E m(θ₀, X)` for `θ ≠ θ₀`. Since `m(θ, ·) ≤ G`, the expectation
  `E m(θ, X) ∈ [-∞, ∞)` is always defined; it is finite exactly when `m(θ, X)` is a.s. finite
  with integrable real part, and the hypothesis only has to be checked in that case.

Then almost surely every sequence of approximate maximizers `θ̂ₙ`, i.e.
`∑_{i<n} m(θ₀, Xᵢ) ≤ ∑_{i<n} m(θ̂ₙ, Xᵢ) + n εₙ` with `εₙ → 0`, converges to `θ₀`.

## Main results

* `ExtremeValueTheory.exists_integral_toReal_max_lt`: the truncation lemma — if `E L < c` (in
  the extended sense) for `L ≤ G` integrable from above, then `E max(L, M) < c` for some real
  `M`.
* `ExtremeValueTheory.ae_tendsto_of_wald_ereal`: Wald's theorem for upper semicontinuous
  extended-real criteria.
* `ExtremeValueTheory.ae_tendsto_of_wald_ereal_of_continuous`: the same for criteria continuous
  in `θ` (with values in `EReal`), where the measurability of the local suprema is automatic.

## Proof

For `θ ≠ θ₀`, the truncation lemma gives `M` with `E max(m(θ, X), M) < E m(θ₀, X)`. The local
suprema `w_r(x) = sup_{B(θ, r)} m(·, x)` decrease to `m(θ, x)` as `r ↓ 0` by upper
semicontinuity, so `max(w_r, M)` (which lies between `M` and `max(G, M)`) converges to
`max(m(θ, ·), M)` boundedly, and some ball `B(θ, r_θ)` has `E max(w_{r_θ}, M) < E m(θ₀, X)`. For
each `k`, the compact set `{d(θ, θ₀) ≥ 1/(k + 1)}` is covered by finitely many such balls, which
gives countably many real integrable functions overall. The strong law of large numbers for them
and for `m(θ₀, ·)` shows that eventually the empirical criterion on each ball stays below its
value at `θ₀` by a fixed margin, which beats the slack `εₙ`.

## References

* A. Wald, *Note on the consistency of the maximum likelihood estimate*, Ann. Math. Statist. 20
  (1949).
* J. Kiefer and J. Wolfowitz, *Consistency of the maximum likelihood estimator in the presence of
  infinitely many incidental parameters*, Ann. Math. Statist. 27 (1956).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge (1998), Theorem 5.14.
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ExtremeValueTheory

/-! ### Extended reals: small helpers -/

section ERealHelpers

lemma EReal.coe_max' (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) :=
  EReal.coe_strictMono.monotone.map_max

lemma EReal.coe_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

/-- An extended real between `⊥` and a real bound is the coercion of its real part. -/
lemma EReal.coe_toReal_of_le {x : EReal} {g : ℝ} (hx : x ≠ ⊥) (hg : x ≤ g) :
    ((x.toReal : ℝ) : EReal) = x :=
  EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top g) hg) hx

/-- The truncation `max x M` of an extended real `x ≤ g` has real part between `M` and
`max g M`. -/
lemma EReal.toReal_max_bounds {x : EReal} {g M : ℝ} (hg : x ≤ g) :
    M ≤ (max x (M : EReal)).toReal ∧ (max x (M : EReal)).toReal ≤ max g M ∧
      (((max x (M : EReal)).toReal : ℝ) : EReal) = max x (M : EReal) := by
  have hb : max x (M : EReal) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot M) (le_max_right _ _)
  have hu : max x (M : EReal) ≤ ((max g M : ℝ) : EReal) := by
    rw [EReal.coe_max']; exact max_le_max hg le_rfl
  have hc := EReal.coe_toReal_of_le hb hu
  refine ⟨?_, ?_, hc⟩
  · rw [← EReal.coe_le_coe_iff, hc]; exact le_max_right _ _
  · rw [← EReal.coe_le_coe_iff, hc]; exact hu

end ERealHelpers

/-! ### The truncation lemma -/

section Truncation

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- **Truncation lemma.** Let `L : α → [-∞, ∞)` be measurable and bounded above by an integrable
`G`, so that `E L ∈ [-∞, ∞)` is defined. If `E L < c` — i.e. `∫ L < c` whenever `L` is a.e.
finite with integrable real part — then already `E max(L, M) < c` for some real `M`. -/
theorem exists_integral_toReal_max_lt [IsFiniteMeasure μ] {L : α → EReal} {G : α → ℝ}
    (hL : Measurable L) (hG : Integrable G μ) (hLG : ∀ x, L x ≤ G x) {c : ℝ}
    (h : (∀ᵐ x ∂μ, L x ≠ ⊥) → Integrable (fun x => (L x).toReal) μ →
      ∫ x, (L x).toReal ∂μ < c) :
    ∃ M : ℝ, ∫ x, (max (L x) (M : EReal)).toReal ∂μ < c := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  set f : ℕ → α → ℝ := fun k x => (max (L x) ((-(k : ℝ) : ℝ) : EReal)).toReal with hf
  set Gp : α → ℝ := fun x => max (G x) 0
  have hGp : Integrable Gp μ := hG.sup (integrable_const 0)
  -- pointwise description of `f`
  have hf_bot : ∀ k x, L x = ⊥ → f k x = -k := fun k x hx => by
    simp only [hf, hx, max_eq_right bot_le, EReal.toReal_coe]
  have hf_fin : ∀ k x, L x ≠ ⊥ → f k x = max (L x).toReal (-k) := fun k x hx => by
    have hc := EReal.coe_toReal_of_le hx (hLG x)
    simp only [hf]
    rw [← hc, ← EReal.coe_max', EReal.toReal_coe, hc]
  have hf_meas : ∀ k, Measurable (f k) := fun k =>
    (hL.max measurable_const).ereal_toReal
  have hf_bd : ∀ k x, |f k x| ≤ |G x| + k := fun k x => by
    obtain ⟨h1, h2, -⟩ := EReal.toReal_max_bounds (M := -(k : ℝ)) (hLG x)
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    rw [abs_le]
    constructor
    · linarith [abs_nonneg (G x)]
    · calc f k x ≤ max (G x) (-k) := h2
        _ ≤ |G x| + k := max_le (by linarith [le_abs_self (G x)])
            (by linarith [abs_nonneg (G x)])
  have hf_int : ∀ k, Integrable (f k) μ := fun k =>
    (hG.abs.add (integrable_const (k : ℝ))).mono' (hf_meas k).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).le.trans (hf_bd k x))
  have hf_le : ∀ k x, f k x ≤ Gp x := fun k x => by
    obtain ⟨-, h2, -⟩ := EReal.toReal_max_bounds (M := -(k : ℝ)) (hLG x)
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    exact h2.trans (max_le_max le_rfl (by linarith))
  -- monotone convergence for `Gp - f k`
  set g : ℕ → α → ℝ≥0∞ := fun k x => ENNReal.ofReal (Gp x - f k x)
  have hg_mono : Monotone g := fun k l hkl x => by
    refine ENNReal.ofReal_le_ofReal (sub_le_sub_left ?_ _)
    simp only [hf]
    have h1 := EReal.toReal_max_bounds (M := -(k : ℝ)) (hLG x)
    have h2 := EReal.toReal_max_bounds (M := -(l : ℝ)) (hLG x)
    rw [← EReal.coe_le_coe_iff, h1.2.2, h2.2.2]
    refine max_le_max le_rfl (EReal.coe_le_coe_iff.2 ?_)
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hg_int : ∀ k, ∫⁻ x, g k x ∂μ ≤ ENNReal.ofReal (∫ x, Gp x ∂μ - c) := fun k => by
    show ∫⁻ x, ENNReal.ofReal ((Gp - f k) x) ∂μ ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal (hGp.sub (hf_int k))
      (ae_of_all _ fun x => sub_nonneg.2 (hf_le k x)), Pi.sub_def, integral_sub hGp (hf_int k)]
    exact ENNReal.ofReal_le_ofReal (by linarith [hcon (-(k : ℝ))])
  have hg_meas : ∀ k, AEMeasurable (g k) μ := fun k =>
    (hGp.aemeasurable.sub (hf_meas k).aemeasurable).ennreal_ofReal
  have hsup : ∫⁻ x, ⨆ k, g k x ∂μ < ⊤ := by
    rw [lintegral_iSup' hg_meas (ae_of_all _ fun x k l hkl => hg_mono hkl x)]
    exact (iSup_le hg_int).trans_lt ENNReal.ofReal_lt_top
  have hae_fin : ∀ᵐ x ∂μ, (⨆ k, g k x) < ⊤ :=
    ae_lt_top' (AEMeasurable.iSup hg_meas) hsup.ne
  -- `L` is a.e. finite
  have hbot : ∀ᵐ x ∂μ, L x ≠ ⊥ := by
    filter_upwards [hae_fin] with x hx hLx
    refine hx.ne (eq_top_iff.2 ?_)
    rw [← ENNReal.iSup_natCast]
    refine iSup_mono fun n => ?_
    simp only [g, hf_bot n x hLx, sub_neg_eq_add]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by simp only [Gp]; linarith [le_max_right (G x) 0])
  -- the real part of `L` is integrable
  have hLle : ∀ x, L x ≠ ⊥ → (L x).toReal ≤ G x := fun x hx => by
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal_of_le hx (hLG x)]; exact hLG x
  set φ : α → ℝ := fun x => Gp x - (L x).toReal
  have hφ0 : 0 ≤ᵐ[μ] φ := by
    filter_upwards [hbot] with x hx
    simp only [Pi.zero_apply, φ, Gp, sub_nonneg]
    exact (hLle x hx).trans (le_max_left _ _)
  have hφle : ∀ᵐ x ∂μ, ENNReal.ofReal (φ x) ≤ ⨆ k, g k x := by
    filter_upwards [hbot] with x hx
    refine le_iSup_of_le (Nat.ceil (-(L x).toReal)) (le_of_eq ?_)
    simp only [g, φ, hf_fin _ x hx]
    rw [max_eq_left (by linarith [Nat.le_ceil (-(L x).toReal)])]
  have hφint : Integrable φ μ := by
    refine ⟨hGp.1.sub hL.ereal_toReal.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hφ0]
    exact (lintegral_mono_ae hφle).trans_lt hsup
  have hLint : Integrable (fun x => (L x).toReal) μ :=
    (hGp.sub hφint).congr (ae_of_all _ fun x => by simp [φ])
  have hlt := h hbot hLint
  -- the truncations converge to `E L`
  have hlim : Tendsto (fun k => ∫ x, f k x ∂μ) atTop (𝓝 (∫ x, (L x).toReal ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |(L x).toReal|)
      (fun k => (hf_meas k).aestronglyMeasurable) hLint.abs (fun k => ?_) ?_
    · filter_upwards [hbot] with x hx
      rw [hf_fin k x hx, Real.norm_eq_abs]
      rcases le_total (-(k : ℝ)) (L x).toReal with hk | hk
      · rw [max_eq_left hk]
      · rw [max_eq_right hk, abs_neg, abs_of_nonneg (Nat.cast_nonneg k)]
        have : (0 : ℝ) ≤ k := k.cast_nonneg
        rw [abs_of_nonpos (by linarith)]; linarith
    · filter_upwards [hbot] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (Nat.ceil (-(L x).toReal))] with k hk
      rw [hf_fin k x hx, max_eq_left]
      have := (Nat.ceil_le).1 hk
      linarith
  have := ge_of_tendsto' hlim fun k => hcon (-(k : ℝ))
  linarith

end Truncation

/-! ### Local suprema and their truncations -/

section LocalSup

variable {Θ : Type*} [MetricSpace Θ] {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  {m : Θ → α → EReal} {G : α → ℝ}

/-- The supremum of the criterion over the open ball `B(θ, r)`. -/
noncomputable def waldBallSup (m : Θ → α → EReal) (θ : Θ) (r : ℝ) (x : α) : EReal :=
  ⨆ θ' ∈ Metric.ball θ r, m θ' x

/-- The truncated local supremum `max(sup_{B(θ, r)} m(·, x), M)`, a real number. -/
noncomputable def waldTrunc (m : Θ → α → EReal) (θ : Θ) (r M : ℝ) (x : α) : ℝ :=
  (max (waldBallSup m θ r x) (M : EReal)).toReal

lemma le_waldBallSup {θ θ' : Θ} {r : ℝ} (h : θ' ∈ Metric.ball θ r) (x : α) :
    m θ' x ≤ waldBallSup m θ r x :=
  le_iSup₂ (f := fun θ' (_ : θ' ∈ Metric.ball θ r) => m θ' x) θ' h

lemma waldBallSup_le (hbound : ∀ θ x, m θ x ≤ G x) (θ : Θ) (r : ℝ) (x : α) :
    waldBallSup m θ r x ≤ G x :=
  iSup₂_le fun θ' _ => hbound θ' x

lemma waldTrunc_bounds (hbound : ∀ θ x, m θ x ≤ G x) (θ : Θ) (r M : ℝ) (x : α) :
    M ≤ waldTrunc m θ r M x ∧ waldTrunc m θ r M x ≤ max (G x) M ∧
      ((waldTrunc m θ r M x : ℝ) : EReal) = max (waldBallSup m θ r x) (M : EReal) :=
  EReal.toReal_max_bounds (waldBallSup_le hbound θ r x)

lemma le_waldTrunc (hbound : ∀ θ x, m θ x ≤ G x) {θ θ' : Θ} {r : ℝ}
    (h : θ' ∈ Metric.ball θ r) (M : ℝ) (x : α) : m θ' x ≤ waldTrunc m θ r M x := by
  rw [(waldTrunc_bounds hbound θ r M x).2.2]
  exact (le_waldBallSup h x).trans (le_max_left _ _)

lemma abs_waldTrunc_le (hbound : ∀ θ x, m θ x ≤ G x) (θ : Θ) (r M : ℝ) (x : α) :
    |waldTrunc m θ r M x| ≤ |G x| + |M| := by
  obtain ⟨h1, h2, -⟩ := waldTrunc_bounds hbound θ r M x
  rw [abs_le]
  constructor
  · linarith [neg_abs_le M, abs_nonneg (G x)]
  · exact h2.trans (max_le (by linarith [le_abs_self (G x), abs_nonneg M])
      (by linarith [le_abs_self M, abs_nonneg (G x)]))

/-- Shrinking balls: by upper semicontinuity, the truncated local suprema converge to the
truncated criterion. -/
lemma tendsto_waldTrunc (hbound : ∀ θ x, m θ x ≤ G x) {θ : Θ} {x : α}
    (husc : UpperSemicontinuousAt (fun θ => m θ x) θ) (M : ℝ) :
    Tendsto (fun j : ℕ => waldTrunc m θ (1 / ((j : ℝ) + 1)) M x) atTop
      (𝓝 ((max (m θ x) (M : EReal)).toReal)) := by
  obtain ⟨-, -, hc⟩ := EReal.toReal_max_bounds (M := M) (hbound θ x)
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun j => ?_, fun b hb => ?_⟩
  · refine ha.trans_le ?_
    rw [← EReal.coe_le_coe_iff, hc, (waldTrunc_bounds hbound θ _ M x).2.2]
    exact max_le_max (le_waldBallSup (Metric.mem_ball_self (by positivity)) x) le_rfl
  · obtain ⟨b', hb', hb'b⟩ := exists_between hb
    have hlt : max (m θ x) (M : EReal) < (b' : EReal) := by
      rw [← hc]; exact EReal.coe_lt_coe_iff.2 hb'
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
      (husc b' ((le_max_left _ _).trans_lt hlt))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    filter_upwards [eventually_ge_atTop N] with j hj
    refine lt_of_le_of_lt ?_ hb'b
    have hrj : 1 / ((j : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
    rw [← EReal.coe_le_coe_iff, (waldTrunc_bounds hbound θ _ M x).2.2]
    refine max_le (iSup₂_le fun θ' hθ' => (hball ?_).le) ((le_max_right _ _).trans hlt.le)
    exact (Metric.mem_ball.1 hθ').trans (hrj.trans_lt hN)

lemma measurable_waldTrunc
    (hsup : ∀ θ (r : ℝ), Measurable fun x => ⨆ θ' ∈ Metric.ball θ r, m θ' x)
    (θ : Θ) (r M : ℝ) : Measurable (waldTrunc m θ r M) :=
  ((hsup θ r).max measurable_const).ereal_toReal

end LocalSup

/-! ### Wald's theorem -/

section Wald

variable {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ] {α : Type*} {mα : MeasurableSpace α}
  {μ : Measure α} {m : Θ → α → EReal} {G : α → ℝ}

omit [CompactSpace Θ] in
/-- For `θ ≠ θ₀`, some ball around `θ` and some truncation level have a truncated local
supremum with expectation below `E m(θ₀, X)`. -/
lemma exists_ball_integral_waldTrunc_lt [IsFiniteMeasure μ]
    (husc : ∀ x, UpperSemicontinuous fun θ => m θ x) (hmeas : ∀ θ, Measurable (m θ))
    (hsup : ∀ θ (r : ℝ), Measurable fun x => ⨆ θ' ∈ Metric.ball θ r, m θ' x)
    (hG : Integrable G μ) (hbound : ∀ θ x, m θ x ≤ G x) {θ : Θ} {c : ℝ}
    (hident : (∀ᵐ x ∂μ, m θ x ≠ ⊥) → Integrable (fun x => (m θ x).toReal) μ →
      ∫ x, (m θ x).toReal ∂μ < c) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, ∫ x, waldTrunc m θ r M x ∂μ < c := by
  obtain ⟨M, hM⟩ := exists_integral_toReal_max_lt (hmeas θ) hG (hbound θ) hident
  have hlim : Tendsto (fun j : ℕ => ∫ x, waldTrunc m θ (1 / ((j : ℝ) + 1)) M x ∂μ) atTop
      (𝓝 (∫ x, (max (m θ x) (M : EReal)).toReal ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => |G x| + |M|)
      (fun j => (measurable_waldTrunc hsup θ _ M).aestronglyMeasurable)
      (hG.abs.add (integrable_const _))
      (fun j => ae_of_all _ fun x => (Real.norm_eq_abs _).le.trans
        (abs_waldTrunc_le hbound θ _ M x))
      (ae_of_all _ fun x => tendsto_waldTrunc hbound (husc x θ) M)
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hM)).exists
  exact ⟨_, by positivity, M, hj⟩

/-- **Wald's consistency theorem for extended-real criteria** (Wald 1949, Kiefer–Wolfowitz).
Let `Θ` be a compact metric space and `X₀, X₁, …` iid with law `μ`. Let the criterion
`m(θ, x) ∈ [-∞, ∞)` be upper semicontinuous in `θ`, with measurable local suprema over balls,
bounded above by an integrable `G`, a.s. finite and integrable at `θ₀`, and assume
`E m(θ, X) < E m(θ₀, X)` for `θ ≠ θ₀` (which only needs checking when `E m(θ, X)` is finite).
Then almost surely every sequence of approximate maximizers — `θ̂ₙ` with
`∑_{i<n} m(θ₀, Xᵢ) ≤ ∑_{i<n} m(θ̂ₙ, Xᵢ) + n εₙ` eventually, for some `εₙ → 0` — converges to
`θ₀`. -/
theorem ae_tendsto_of_wald_ereal [IsProbabilityMeasure μ] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : ℕ → Ω → α} (hX : ∀ i, HasLaw (X i) μ P) (hind : iIndepFun X P)
    (husc : ∀ x, UpperSemicontinuous fun θ => m θ x) (hmeas : ∀ θ, Measurable (m θ))
    (hsup : ∀ θ (r : ℝ), Measurable fun x => ⨆ θ' ∈ Metric.ball θ r, m θ' x)
    (hG : Integrable G μ) (hbound : ∀ θ x, m θ x ≤ G x) {θ₀ : Θ}
    (h₀ : ∀ᵐ x ∂μ, m θ₀ x ≠ ⊥) (hint₀ : Integrable (fun x => (m θ₀ x).toReal) μ)
    (hident : ∀ θ, θ ≠ θ₀ → (∀ᵐ x ∂μ, m θ x ≠ ⊥) → Integrable (fun x => (m θ x).toReal) μ →
      ∫ x, (m θ x).toReal ∂μ < ∫ x, (m θ₀ x).toReal ∂μ) :
    ∀ᵐ ω ∂P, ∀ (θhat : ℕ → Θ) (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) →
      (∀ᶠ n in atTop, ∑ i ∈ Finset.range n, m θ₀ (X i ω) ≤
        ∑ i ∈ Finset.range n, m (θhat n) (X i ω) + ((n * ε n : ℝ) : EReal)) →
      Tendsto θhat atTop (𝓝 θ₀) := by
  set c₀ := ∫ x, (m θ₀ x).toReal ∂μ
  -- the balls with truncated local suprema below `c₀`
  have key : ∀ θ : Θ, θ ≠ θ₀ → ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, ∫ x, waldTrunc m θ r M x ∂μ < c₀ :=
    fun θ hθ => exists_ball_integral_waldTrunc_lt husc hmeas hsup hG hbound (hident θ hθ)
  choose r hr M hM using key
  -- the compact shells `K k = {d(θ, θ₀) ≥ 1/(k + 1)}` and their finite covers
  set K : ℕ → Set Θ := fun k => {θ | 1 / ((k : ℝ) + 1) ≤ dist θ θ₀}
  have hKne : ∀ k, ∀ θ ∈ K k, θ ≠ θ₀ := fun k θ hθ h => by
    simp only [K, mem_ofPred_eq, h, dist_self] at hθ
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hKc : ∀ k, IsCompact (K k) := fun k =>
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  have hcover : ∀ k, K k ⊆ ⋃ p : K k, Metric.ball p.1 (r p.1 (hKne k p.1 p.2)) :=
    fun k θ hθ => mem_iUnion.2 ⟨⟨θ, hθ⟩, Metric.mem_ball_self (hr θ _)⟩
  choose t ht using fun k => (hKc k).elim_finite_subcover _ (fun _ => Metric.isOpen_ball)
    (hcover k)
  -- the strong law of large numbers for the countably many functions involved
  have hint : ∀ k (p : K k), Integrable (waldTrunc m p.1 (r p.1 (hKne k p.1 p.2))
      (M p.1 (hKne k p.1 p.2))) μ := fun k p =>
    (hG.abs.add (integrable_const _)).mono'
      (measurable_waldTrunc hsup _ _ _).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).le.trans (abs_waldTrunc_le hbound _ _ _ x))
  have hw : ∀ᵐ ω ∂P, ∀ k, ∀ p : t k, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      waldTrunc m p.1.1 (r p.1.1 (hKne k p.1.1 p.1.2)) (M p.1.1 (hKne k p.1.1 p.1.2)) (X i ω))
      atTop (𝓝 (∫ x, waldTrunc m p.1.1 (r p.1.1 (hKne k p.1.1 p.1.2))
        (M p.1.1 (hKne k p.1.1 p.1.2)) x ∂μ)) :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun p =>
      ae_tendsto_avg_comp hX hind (measurable_waldTrunc hsup _ _ _) (hint k p.1)
  have h0 := ae_tendsto_avg_comp hX hind (hmeas θ₀).ereal_toReal hint₀
  have hfin : ∀ᵐ ω ∂P, ∀ i, m θ₀ (X i ω) ≠ ⊥ := ae_all_iff.2 fun i =>
    ae_of_ae_map (hX i).aemeasurable ((hX i).map_eq ▸ h₀)
  filter_upwards [hw, h0, hfin] with ω hw h0 hfin θhat ε hε hθ
  refine Metric.tendsto_nhds.2 fun η hη => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
  -- eventually, on every ball of the `k`-th cover, the empirical criterion is too small
  have hev : ∀ᶠ n : ℕ in atTop, ∀ p ∈ t k, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      waldTrunc m p.1 (r p.1 (hKne k p.1 p.2)) (M p.1 (hKne k p.1 p.2)) (X i ω) + ε n <
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (m θ₀ (X i ω)).toReal := by
    refine (t k).eventually_all.2 fun p hp => ?_
    have := ((hw k ⟨p, hp⟩).add hε).sub h0
    have hneg : ∫ x, waldTrunc m p.1 (r p.1 (hKne k p.1 p.2)) (M p.1 (hKne k p.1 p.2)) x ∂μ +
        0 - c₀ < 0 := by linarith [hM p.1 (hKne k p.1 p.2)]
    filter_upwards [this.eventually (gt_mem_nhds hneg)] with n hn
    linarith
  filter_upwards [hev, hθ, eventually_gt_atTop 0] with n hn hθn hn0
  by_contra hfar
  have hmem : θhat n ∈ K k := (hk.trans_le (not_lt.1 hfar)).le
  obtain ⟨p, hp, hball⟩ := mem_iUnion₂.1 (ht k hmem)
  set w := waldTrunc m p.1 (r p.1 (hKne k p.1 p.2)) (M p.1 (hKne k p.1 p.2))
  have hle : ∑ i ∈ Finset.range n, m (θhat n) (X i ω) ≤
      ((∑ i ∈ Finset.range n, w (X i ω) : ℝ) : EReal) := by
    rw [EReal.coe_finsetSum]
    exact Finset.sum_le_sum fun i _ => le_waldTrunc hbound hball _ _
  have heq : ∑ i ∈ Finset.range n, m θ₀ (X i ω) =
      ((∑ i ∈ Finset.range n, (m θ₀ (X i ω)).toReal : ℝ) : EReal) := by
    rw [EReal.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => (EReal.coe_toReal_of_le (hfin i) (hbound _ _)).symm
  have hreal : ∑ i ∈ Finset.range n, (m θ₀ (X i ω)).toReal ≤
      ∑ i ∈ Finset.range n, w (X i ω) + n * ε n := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_add, ← heq]
    exact hθn.trans (add_le_add_left hle _)
  have hn' : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hn0)
  have := hn p hp
  have h2 : (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, w (X i ω) + n * ε n) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, w (X i ω) + ε n := by
    field_simp
  have := mul_le_mul_of_nonneg_left hreal hn'.le
  linarith

/-- For a criterion continuous in `θ`, the supremum over a ball is a countable supremum over a
dense sequence, hence measurable. -/
lemma measurable_biSup_ball_of_continuous (hcont : ∀ x, Continuous fun θ => m θ x)
    (hmeas : ∀ θ, Measurable (m θ)) (θ : Θ) (r : ℝ) :
    Measurable fun x => ⨆ θ' ∈ Metric.ball θ r, m θ' x := by
  classical
  have : Nonempty Θ := ⟨θ⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Θ
  have heq : (fun x => ⨆ θ' ∈ Metric.ball θ r, m θ' x) =
      fun x => ⨆ k : ℕ, if u k ∈ Metric.ball θ r then m (u k) x else ⊥ := by
    funext x
    refine le_antisymm (iSup₂_le fun θ' hθ' => le_of_forall_lt fun a ha => ?_)
      (iSup_le fun k => ?_)
    · have hev : ∀ᶠ θ'' in 𝓝 θ', a < m θ'' x ∧ θ'' ∈ Metric.ball θ r :=
        ((hcont x).continuousAt.eventually (lt_mem_nhds ha)).and
          (Metric.isOpen_ball.mem_nhds hθ')
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hu.inter_nhds_nonempty hev
      refine hk.1.trans_le (le_iSup_of_le k ?_)
      rw [ite_eq_left_iff.2 fun h => absurd hk.2 h]
    · split_ifs with h
      · exact le_iSup₂ (f := fun θ' (_ : θ' ∈ Metric.ball θ r) => m θ' x) (u k) h
      · exact bot_le
  rw [heq]
  refine Measurable.iSup fun k => ?_
  split_ifs
  · exact hmeas _
  · exact measurable_const

/-- **Wald's consistency theorem for extended-real criteria continuous in the parameter.** As
`ae_tendsto_of_wald_ereal`, for a criterion `θ ↦ m(θ, x) ∈ [-∞, ∞)` continuous for every `x`
(for the topology of `EReal`); the measurability of the local suprema is then automatic. -/
theorem ae_tendsto_of_wald_ereal_of_continuous [IsProbabilityMeasure μ] {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → α} (hX : ∀ i, HasLaw (X i) μ P)
    (hind : iIndepFun X P) (hcont : ∀ x, Continuous fun θ => m θ x)
    (hmeas : ∀ θ, Measurable (m θ)) (hG : Integrable G μ) (hbound : ∀ θ x, m θ x ≤ G x)
    {θ₀ : Θ} (h₀ : ∀ᵐ x ∂μ, m θ₀ x ≠ ⊥) (hint₀ : Integrable (fun x => (m θ₀ x).toReal) μ)
    (hident : ∀ θ, θ ≠ θ₀ → (∀ᵐ x ∂μ, m θ x ≠ ⊥) → Integrable (fun x => (m θ x).toReal) μ →
      ∫ x, (m θ x).toReal ∂μ < ∫ x, (m θ₀ x).toReal ∂μ) :
    ∀ᵐ ω ∂P, ∀ (θhat : ℕ → Θ) (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) →
      (∀ᶠ n in atTop, ∑ i ∈ Finset.range n, m θ₀ (X i ω) ≤
        ∑ i ∈ Finset.range n, m (θhat n) (X i ω) + ((n * ε n : ℝ) : EReal)) →
      Tendsto θhat atTop (𝓝 θ₀) :=
  have : Nonempty Θ := ⟨θ₀⟩
  ae_tendsto_of_wald_ereal hX hind (fun x => (hcont x).upperSemicontinuous) hmeas
    (measurable_biSup_ball_of_continuous hcont hmeas) hG hbound h₀ hint₀ hident

end Wald

end ExtremeValueTheory
