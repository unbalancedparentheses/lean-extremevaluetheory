/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.GeneralizedCLTConverseAsymmetric.Symmetrization

/-!
# The converse of the generalized central limit theorem (general case)

Let `X₁, X₂, …` be i.i.d. with law `μ` (no symmetry assumed), `aₙ > 0`, `bₙ ∈ ℝ`, and suppose
the laws of `(Sₙ - bₙ) / aₙ` converge weakly to a law `ν` which is not a Dirac mass. We prove
the necessity half of Feller's criterion ([Feller, Vol. II, §XVII.5, Theorem 2],
[GK, §35, Theorem 2]): `U(x) = E[X² 1{|X| ≤ x}]` is regularly varying with index `2 - α` for
some `0 < α ≤ 2`, and for `α < 2` the tail `P(|X| > x)` is regularly varying with index `-α`,
`n P(|X| > aₙ)` converges to a positive limit, and the tails are balanced,
`P(X > x) / P(|X| > x) → p ∈ [0, 1]`. We also construct the canonical normalizing sequence
`aₙ = inf {x : P(|X| > x) ≤ 1 / n}` and restate the symmetric Feller criterion as an iff.

## Main definitions

* `GCLTConverse.normSeq μ n = inf {x : P(|X| > x) ≤ 1 / n}`.
* `GCLTConverse.symmLaw μ`, the law of `X - X'` for independent copies.
* `GCLTConverse.ramp ε`, `GCLTConverse.rampTail μ ε x = E[fε(X / x)]`: a smoothed right tail.

## Main results

* `GCLTConverse.tendsto_mul_absTail_normSeq`: if `P(|X| > ·) ∈ RV(-α)` then
  `n P(|X| > aₙ) → 1` for `aₙ = normSeq μ n`.
* `GCLTConverse.tendsto_map_convPow_normSeq`, `GCLTConverse.domainOfAttraction_isSymmStable_iff`:
  for symmetric `μ` and `0 < α < 2`, `Sₙ / aₙ` converges to a symmetric `α`-stable law for some
  `aₙ > 0` iff `P(|X| > ·) ∈ RV(-α)`, and then `aₙ = normSeq μ n` works.
* `GCLTConverse.exists_isRegularlyVarying_of_tendsto_sub`: the regular-variation part of the
  converse without symmetry.
* `GCLTConverse.exists_isRegularlyVarying_tailBalance_of_tendsto`: **the converse GCLT with tail
  balance**.
* `GCLTConverse.exists_tendsto_mul_tails_of_tendsto`: the Lévy measure of the limit,
  `n P(X > aₙ u) → c₊ u^(-α)`, `n P(X < -aₙ u) → c₋ u^(-α)`.

## Proof outline

1. *Symmetrization* (`tendsto_map_convPow_symmLaw`, `symmLaw_ne_dirac`): `(Sₙ - S'ₙ) / aₙ`
   converges to `ν ∗ ν̃ ≠ δ₀` (characteristic functions `|φ|²`), so the symmetric converse
   (`exists_tendsto_mul_sqRatio_of_tendsto`) gives `α` and the scaling of the symmetrized law.
2. *Weak symmetrization inequalities* (`two_mul_absTail_mul_le_absTail_symmLaw`,
   `absTail_symmLaw_le`): `2 P(|X| > s + u) P(|X| ≤ u) ≤ P(|X - X'| > s)` and
   `P(|X - X'| > s + u) ≤ 2 P(|X| > s) + P(|X| > u)²`; with regular variation they give
   `P(|X| > x) / P(|X - X'| > x) → 1 / 2` (`tendsto_absTail_div_absTail_symmLaw`). For `α = 2`,
   `E[min (x², (X - X')²)] ≤ 4 E[min (x², X²)]` transfers slow variation.
3. *Tail balance* (`exists_tendsto_mul_integral_comp` in
   `ExtremeValueTheory.StableLaws.LevyMeasureLimit`): `n E[fε(X / aₙ)]` converges for every
   ramp `fε`; the bracketing lemma `tendsto_div_of_tendsto_mul` turns this into
   `E[fε(X / x)] / P(|X| > x) → pε`, and `P(X > (1 + ε) x) ≤ E[fε(X / x)] ≤ P(X > x)` with
   `ε → 0` gives `P(X > x) / P(|X| > x) → p`
   (`exists_tendsto_measureReal_Ioi_div_absTail`).

## File layout

* `ExtremeValueTheory.StableLaws.GeneralizedCLTConverseAsymmetric.Symmetrization`: `normSeq`, the
  symmetric Feller criterion, symmetrization and tail comparison (steps 1–2).
* this file: the bracketing lemma, ramps and tail balance (step 3).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

namespace GCLTConverse

open GCLT Subexp

section Bracket

variable {F G : ℝ → ℝ} {a : ℕ → ℝ}

/-- `n F(aₙ u) → A u ^ ρ` when `F ∈ RV(ρ)`, `n F(aₙ) → A` and `aₙ → ∞`. -/
theorem tendsto_mul_comp_mul_of_tendsto {ρ A : ℝ} (hRV : IsRegularlyVarying F ρ)
    (ha : Tendsto a atTop atTop)
    (hA : Tendsto (fun n : ℕ => (n : ℝ) * F (a n)) atTop (𝓝 A)) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * F (a n * u)) atTop (𝓝 (A * u ^ ρ)) := by
  refine (hA.mul ((hRV.2 u hu).comp ha)).congr' ?_
  filter_upwards [ha.eventually hRV.1] with n hn
  have := hn.ne'
  simp only [Function.comp, mul_comm u (a n)]
  field_simp

/-- **Bracketing for two functions.** If `F ≥ 0` and `G > 0` are nonincreasing on `(0, ∞)`,
`aₙ > 0`, `aₙ → ∞`, `n F(aₙ) → A` and `n G(aₙ) → B > 0`, then `F(x) / G(x) → A / B`. -/
theorem tendsto_div_of_tendsto_mul (hF : AntitoneOn F (Ioi 0)) (hF0 : ∀ x, 0 < x → 0 ≤ F x)
    (hG : AntitoneOn G (Ioi 0)) (hGpos : ∀ x, 0 < x → 0 < G x) (ha : ∀ n, 0 < a n)
    (hatop : Tendsto a atTop atTop) {A B : ℝ}
    (hA : Tendsto (fun n : ℕ => (n : ℝ) * F (a n)) atTop (𝓝 A))
    (hB : Tendsto (fun n : ℕ => (n : ℝ) * G (a n)) atTop (𝓝 B)) (hB0 : 0 < B) :
    Tendsto (fun x => F x / G x) atTop (𝓝 (A / B)) := by
  have hsucc : ∀ {H : ℝ → ℝ} {C : ℝ}, Tendsto (fun n : ℕ => (n : ℝ) * H (a n)) atTop (𝓝 C) →
      Tendsto (fun n : ℕ => (n : ℝ) * H (a (n + 1))) atTop (𝓝 C) := by
    intro H C h
    have h1 := h.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
      have := tendsto_natCast_div_add_atTop (1 : ℝ)
      refine this.congr fun n => ?_
      push_cast; ring
    refine (by simpa using h2.mul h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ) *
      (((n + 1 : ℕ) : ℝ) * H (a (n + 1)))) atTop (𝓝 C)).congr' ?_
    filter_upwards with n
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hup : Tendsto (fun n : ℕ => F (a n) / G (a (n + 1))) atTop (𝓝 (A / B)) := by
    refine (hA.div (hsucc hB) hB0.ne').congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Pi.div_apply]
    field_simp
  have hlo : Tendsto (fun n : ℕ => F (a (n + 1)) / G (a n)) atTop (𝓝 (A / B)) := by
    refine ((hsucc hA).div hB hB0.ne').congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Pi.div_apply]
    field_simp
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_order.1 hlo).1 b hb)
    filter_upwards [eventually_ge_atTop (a K)] with x hx
    obtain ⟨N, hKN, h1, h2⟩ := exists_bracket hatop hx
    have hx0 : 0 < x := (ha K).trans_le hx
    refine (hK N hKN).trans_le ?_
    exact div_le_div₀ (hF0 _ hx0) (hF hx0 (ha _) h2.le) (hGpos _ hx0) (hG (ha N) hx0 h1)
  · obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_order.1 hup).2 b hb)
    filter_upwards [eventually_ge_atTop (a K)] with x hx
    obtain ⟨N, hKN, h1, h2⟩ := exists_bracket hatop hx
    have hx0 : 0 < x := (ha K).trans_le hx
    refine lt_of_le_of_lt ?_ (hK N hKN)
    exact div_le_div₀ (hF0 _ (ha N)) (hF (ha N) hx0 h1) (hGpos _ (ha _)) (hG hx0 (ha _) h2.le)

end Bracket

section Ramp

/-- The ramp `fε(z) = max 0 (min 1 ((z - 1) / ε))`, a continuous version of `1{z > 1}`. -/
noncomputable def ramp (ε z : ℝ) : ℝ := max 0 (min 1 ((z - 1) / ε))

variable {ε : ℝ}

theorem ramp_nonneg (z : ℝ) : 0 ≤ ramp ε z := le_max_left _ _

theorem ramp_le_one (z : ℝ) : ramp ε z ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem ramp_eq_zero (hε : 0 < ε) {z : ℝ} (hz : z ≤ 1) : ramp ε z = 0 :=
  max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le))

theorem ramp_eq_one (hε : 0 < ε) {z : ℝ} (hz : 1 + ε ≤ z) : ramp ε z = 1 := by
  have : 1 ≤ (z - 1) / ε := by rw [le_div_iff₀ hε]; linarith
  rw [ramp, min_eq_left this, max_eq_right zero_le_one]

theorem ramp_mono (hε : 0 < ε) : Monotone (ramp ε) := fun z z' h =>
  max_le_max le_rfl (min_le_min le_rfl (div_le_div_of_nonneg_right (by linarith) hε.le))

theorem ramp_anti {ε ε' : ℝ} (hε' : 0 < ε') (h : ε' ≤ ε) (z : ℝ) : ramp ε z ≤ ramp ε' z := by
  rcases le_total z 1 with hz | hz
  · rw [ramp_eq_zero (hε'.trans_le h) hz]; exact ramp_nonneg _
  · exact max_le_max le_rfl (min_le_min le_rfl
      (div_le_div_of_nonneg_left (by linarith) hε' h))

theorem continuous_ramp : Continuous (ramp ε) := by unfold ramp; fun_prop

theorem lipschitzWith_ramp (hε : 0 < ε) : LipschitzWith (Real.toNNReal ε⁻¹) (ramp ε) := by
  have h : LipschitzWith (Real.toNNReal ε⁻¹) fun z : ℝ => (z - 1) / ε := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hε.le), ← sub_div,
      show u - 1 - (v - 1) = u - v by ring, abs_div, abs_of_pos hε, div_eq_inv_mul]
  exact (h.const_min 1).const_max 0

/-- The ramp as a bounded continuous function. -/
noncomputable def rampBCF (ε : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (ramp ε) continuous_ramp 1 fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg z)]; exact ramp_le_one z

theorem rampBCF_apply (z : ℝ) : rampBCF ε z = ramp ε z := rfl

/-- `Tε(x) = E[fε(X / x)]`, a smoothed right tail. -/
noncomputable def rampTail (μ : Measure ℝ) (ε x : ℝ) : ℝ := ∫ y, ramp ε (x⁻¹ * y) ∂μ

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

theorem integrable_ramp (x : ℝ) : Integrable (fun y => ramp ε (x⁻¹ * y)) μ :=
  Integrable.of_bound (continuous_ramp.comp (by fun_prop)).aestronglyMeasurable 1
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg _)]; exact ramp_le_one _)

omit [IsProbabilityMeasure μ] in
theorem rampTail_nonneg (x : ℝ) : 0 ≤ rampTail μ ε x :=
  integral_nonneg fun _ => ramp_nonneg _

theorem rampTail_antitoneOn (hε : 0 < ε) : AntitoneOn (rampTail μ ε) (Ioi 0) := by
  intro x hx x' hx' hxx'
  refine integral_mono (integrable_ramp _) (integrable_ramp _) fun y => ?_
  have hx0 : (0 : ℝ) < x := hx
  rcases le_total y 0 with hy | hy
  · rw [ramp_eq_zero hε (by nlinarith [inv_pos.2 hx0, inv_pos.2 (hx0.trans_le hxx')]),
      ramp_eq_zero hε (by nlinarith [inv_pos.2 hx0])]
  · exact ramp_mono hε (mul_le_mul_of_nonneg_right ((inv_le_inv₀ (hx0.trans_le hxx') hx0).2
      hxx') hy)

theorem rampTail_le (hε : 0 < ε) {x : ℝ} (hx : 0 < x) : rampTail μ ε x ≤ μ.real (Ioi x) := by
  calc rampTail μ ε x ≤ ∫ y, (Ioi x).indicator (fun _ => (1 : ℝ)) y ∂μ := by
        refine integral_mono (integrable_ramp _) ((integrable_const 1).indicator measurableSet_Ioi)
          fun y => ?_
        by_cases hy : x < y
        · rw [Set.indicator_of_mem (show y ∈ Ioi x from hy)]; exact ramp_le_one _
        · rw [Set.indicator_of_notMem (show y ∉ Ioi x from hy),
            ramp_eq_zero hε (by rw [inv_mul_le_iff₀ hx]; linarith [not_lt.1 hy])]
    _ = μ.real (Ioi x) := by rw [integral_indicator_const _ measurableSet_Ioi]; simp

theorem le_rampTail (hε : 0 < ε) {x : ℝ} (hx : 0 < x) :
    μ.real (Ioi ((1 + ε) * x)) ≤ rampTail μ ε x := by
  calc μ.real (Ioi ((1 + ε) * x)) = ∫ y, (Ioi ((1 + ε) * x)).indicator (fun _ => (1 : ℝ)) y ∂μ := by
        rw [integral_indicator_const _ measurableSet_Ioi]; simp
    _ ≤ rampTail μ ε x := by
        refine integral_mono ((integrable_const 1).indicator measurableSet_Ioi) (integrable_ramp _)
          fun y => ?_
        by_cases hy : (1 + ε) * x < y
        · rw [Set.indicator_of_mem (show y ∈ Ioi ((1 + ε) * x) from hy),
            ramp_eq_one hε (by rw [le_inv_mul_iff₀ hx]; linarith)]
        · rw [Set.indicator_of_notMem (show y ∉ Ioi ((1 + ε) * x) from hy)]
          exact ramp_nonneg _

theorem rampTail_anti {ε ε' : ℝ} (hε' : 0 < ε') (h : ε' ≤ ε) (x : ℝ) :
    rampTail μ ε x ≤ rampTail μ ε' x :=
  integral_mono (integrable_ramp _) (integrable_ramp _) fun _ => ramp_anti hε' h _

end Ramp

section TailBalance

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ} {a : ℕ → ℝ}

/-- **Tail balance from the convergence of smoothed tails.** Let `P(|X| > ·)` be regularly
varying with index `-α`, `aₙ > 0`, `aₙ → ∞`, `n P(|X| > aₙ) → B > 0`, and suppose that for
every `ε ∈ (0, 1)` the sequence `n E[fε(X / aₙ)]` converges (`fε` the ramp from `1` to `1 + ε`).
Then `P(X > x) / P(|X| > x) → p` for some `p ∈ [0, 1]`. -/
theorem exists_tendsto_measureReal_Ioi_div_absTail
    (hRV : IsRegularlyVarying (absTail μ) (-α)) (ha : ∀ n, 0 < a n)
    (hatop : Tendsto a atTop atTop) {B : ℝ}
    (hB : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 B)) (hB0 : 0 < B)
    (hT : ∀ ε, 0 < ε → ε < 1 → ∃ L,
      Tendsto (fun n : ℕ => (n : ℝ) * rampTail μ ε (a n)) atTop (𝓝 L)) :
    ∃ p, 0 ≤ p ∧ p ≤ 1 ∧ Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p) := by
  have hGpos := absTail_pos hRV
  set ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 2) with hεdef
  have hε0 : ∀ m, 0 < ε m := fun m => by positivity
  have hε1 : ∀ m, ε m < 1 := fun m => by
    simp only [hεdef]; rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hεanti : Antitone ε := fun m m' h => by
    simp only [hεdef]
    have : (m : ℝ) ≤ m' := by exact_mod_cast h
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  choose L hL using fun m => hT (ε m) (hε0 m) (hε1 m)
  have hp : ∀ m, Tendsto (fun x => rampTail μ (ε m) x / absTail μ x) atTop (𝓝 (L m / B)) :=
    fun m => tendsto_div_of_tendsto_mul (rampTail_antitoneOn (hε0 m))
      (fun x _ => rampTail_nonneg x) (absTail_antitone.antitoneOn _) (fun x _ => hGpos x) ha
      hatop (hL m) hB hB0
  set q : ℕ → ℝ := fun m => L m / B
  have hq0 : ∀ m, 0 ≤ q m := fun m => ge_of_tendsto (hp m) (Eventually.of_forall fun x =>
    div_nonneg (rampTail_nonneg x) (hGpos x).le)
  have hq1 : ∀ m, q m ≤ 1 := fun m => le_of_tendsto (hp m) (by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [div_le_one (hGpos x)]
    exact (rampTail_le (hε0 m) hx).trans (measureReal_Ioi_le_absTail x))
  have hqmono : Monotone q := fun m m' h => le_of_tendsto_of_tendsto' (hp m) (hp m') fun x =>
    div_le_div_of_nonneg_right (rampTail_anti (hε0 m') (hεanti h) x) (hGpos x).le
  set p := ⨆ m, q m
  have hbdd : BddAbove (Set.range q) := ⟨1, fun _ ⟨m, hm⟩ => hm ▸ hq1 m⟩
  have hqp : Tendsto q atTop (𝓝 p) := tendsto_atTop_ciSup hqmono hbdd
  have hp0 : 0 ≤ p := (hq0 0).trans (le_ciSup hbdd 0)
  have hp1 : p ≤ 1 := ciSup_le hq1
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
    exact this.inv_tendsto_atTop.congr fun m => by simp [hεdef]
  refine ⟨p, hp0, hp1, tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · obtain ⟨m, hm⟩ := ((tendsto_order.1 hqp).1 b hb).exists
    filter_upwards [(tendsto_order.1 (hp m)).1 b hm, eventually_gt_atTop 0] with x hx hx0
    refine hx.trans_le (div_le_div_of_nonneg_right ?_ (hGpos x).le)
    exact rampTail_le (hε0 m) hx0
  · -- `R(x) ≤ Tε(x / (1 + ε))`
    have hlim : Tendsto (fun m => q m * (1 + ε m) ^ α) atTop (𝓝 (p * (1 + 0) ^ α)) :=
      hqp.mul (((tendsto_const_nhds.add hεlim).rpow_const (Or.inl (by norm_num))))
    rw [add_zero, Real.one_rpow, mul_one] at hlim
    obtain ⟨m, hm⟩ := ((tendsto_order.1 hlim).2 b hb).exists
    set c := (1 + ε m)⁻¹ with hc
    have hc0 : 0 < c := by have := hε0 m; positivity
    have hcα : c ^ (-α) = (1 + ε m) ^ α := by
      rw [hc, Real.inv_rpow (by linarith [hε0 m]), Real.rpow_neg (by linarith [hε0 m]), inv_inv]
    have h1 : Tendsto (fun x => rampTail μ (ε m) (c * x) / absTail μ (c * x) *
        (absTail μ (c * x) / absTail μ x)) atTop (𝓝 (q m * (1 + ε m) ^ α)) := by
      rw [← hcα]
      exact ((hp m).comp (tendsto_id.const_mul_atTop hc0)).mul (hRV.2 c hc0)
    filter_upwards [(tendsto_order.1 h1).2 b hm, eventually_gt_atTop 0] with x hx hx0
    refine lt_of_le_of_lt ?_ hx
    rw [div_mul_div_cancel₀ (hGpos _).ne']
    refine div_le_div_of_nonneg_right ?_ (hGpos x).le
    have := le_rampTail (μ := μ) (hε0 m) (mul_pos hc0 hx0)
    rwa [← mul_assoc, hc, mul_inv_cancel₀ (by linarith [hε0 m]), one_mul] at this

end TailBalance

section ConverseTailBalance

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ}

/-- The characteristic function of a limit of normalized sums does not vanish: its squared
modulus is the characteristic function of the limit of the symmetrized sums. -/
theorem charFun_ne_zero_of_tendsto {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    (t : ℝ) : charFun (ν : Measure ℝ) t ≠ 0 := by
  have hs := tendsto_map_convPow_symmLaw hconv
  obtain ⟨δ, -, hb⟩ := exists_nh_le symmLaw_map_neg hs
  have h := (tendsto_nh symmLaw_map_neg hs hb t).1
  simp only [ProbabilityMeasure.coe_mk, charFun_symmLaw, Complex.ofReal_re] at h
  intro h0
  rw [h0, map_zero] at h
  exact lt_irrefl _ h

/-- The tail part of the converse, from the symmetrized scaling limit: if `(Sₙ - bₙ) / aₙ → ν`
and `n E[min (1, (X - X')² / (aₙ x)²)] → K x ^ (-α)` with `K > 0`, `0 < α < 2`, then
`P(|X| > ·) ∈ RV(-α)`, `n P(|X| > aₙ) → B > 0` and the tails are balanced. -/
theorem tailBalance_of_tendsto_mul_sqRatio_symmLaw (ha : ∀ n, 0 < a n)
    {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν))
    {α K : ℝ} (hα0 : 0 < α) (hlt : α < 2) (hK : 0 < K)
    (hL : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n * x)) atTop
      (𝓝 (K * x ^ (-α)))) :
    IsRegularlyVarying (absTail μ) (-α) ∧
      (∃ B > 0, Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 B)) ∧
      ∃ p, 0 ≤ p ∧ p ≤ 1 ∧ Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p) := by
  obtain ⟨hGs, -, hBs⟩ := isRegularlyVarying_of_tendsto_mul_sqRatio (μ := symmLaw μ) ha hK hα0
    hlt hL
  have hG := isRegularlyVarying_absTail_of_symmLaw hGs
  refine ⟨hG, ?_⟩
  have hGpos := absTail_pos hG
  have hatop : Tendsto a atTop atTop :=
    tendsto_atTop_of_tendsto_mul_comp (T := absTail (symmLaw μ)) (L := fun _ => K * ((2 - α) / 2))
      (absTail_antitone.antitoneOn _) (fun x _ => absTail_pos hGs x) ha hBs
  -- `n P(|X| > aₙ) → B > 0`
  set B := K * ((2 - α) / 2) * (1 / 2) with hBdef
  have hB0 : 0 < B := by
    have : 0 < 2 - α := by linarith
    positivity
  have hB : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 B) := by
    refine (hBs.mul ((tendsto_absTail_div_absTail_symmLaw hGs).comp hatop)).congr fun n => ?_
    have := (absTail_pos hGs (a n)).ne'
    simp only [Function.comp]
    field_simp
  -- `n E[min (1, (X / aₙ x)²)] → B κ x ^ (-α)`
  set κ := 2 / (2 - α) with hκdef
  have hκ0 : 0 < κ := div_pos two_pos (by linarith)
  have hκ : Tendsto (fun x => sqRatio μ x / absTail μ x) atTop (𝓝 κ) := by
    refine (tendsto_minSqMoment_div_sq_mul_absTail hlt hG).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [sqRatio_eq_div hx.ne', div_div]
  have hTRV : IsRegularlyVarying (sqRatio μ) (-α) := hG.of_tendsto_div hκ hκ0
  have hS0 : Tendsto (fun n : ℕ => (n : ℝ) * sqRatio μ (a n)) atTop (𝓝 (B * κ)) := by
    refine (hB.mul (hκ.comp hatop)).congr fun n => ?_
    have := (hGpos (a n)).ne'
    simp only [Function.comp]
    field_simp
  have hS : ∃ C, ∀ᶠ n : ℕ in atTop, (n : ℝ) * sqRatio μ (a n) ≤ C :=
    ⟨B * κ + 1, ((tendsto_order.1 hS0).2 (B * κ + 1) (by linarith)).mono fun _ h => h.le⟩
  have hsmall : ∀ η > 0, ∃ s₀ > 0, ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * sqRatio μ (a n / s₀) ≤ η := by
    intro η hη
    set s₀ := (η / (2 * (B * κ))) ^ α⁻¹
    have hs₀ : 0 < s₀ := Real.rpow_pos_of_pos (by positivity) _
    refine ⟨s₀, hs₀, ?_⟩
    have h := tendsto_mul_comp_mul_of_tendsto hTRV hatop hS0 (inv_pos.2 hs₀)
    have he : B * κ * s₀⁻¹ ^ (-α) = η / 2 := by
      rw [Real.inv_rpow hs₀.le, Real.rpow_neg hs₀.le, inv_inv,
        Real.rpow_inv_rpow (by positivity) hα0.ne']
      field_simp
    rw [he] at h
    filter_upwards [(tendsto_order.1 h).2 η (by linarith)] with n hn
    exact hn.le
  have hlow : ∃ c > 0, ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) * absTail μ (2 * a n) := by
    have h := tendsto_mul_comp_mul_of_tendsto hG hatop hB two_pos
    have h2 : 0 < B * 2 ^ (-α) := mul_pos hB0 (Real.rpow_pos_of_pos two_pos _)
    refine ⟨B * 2 ^ (-α) / 2, by positivity, ?_⟩
    filter_upwards [(tendsto_order.1 h).1 (B * 2 ^ (-α) / 2) (by linarith)] with n hn
    rw [mul_comm 2 (a n)]
    exact hn.le
  have hφ := charFun_ne_zero_of_tendsto hconv
  have hT : ∀ ε, 0 < ε → ε < 1 → ∃ L,
      Tendsto (fun n : ℕ => (n : ℝ) * rampTail μ ε (a n)) atTop (𝓝 L) := by
    intro ε hε _
    exact exists_tendsto_mul_integral_comp ha hconv hφ hS hsmall hlow (rampBCF ε) one_pos
      (fun z hz => ramp_eq_zero hε ((le_abs_self z).trans hz.le)) (lipschitzWith_ramp hε)
  exact ⟨⟨B, hB0, hB⟩, exists_tendsto_measureReal_Ioi_div_absTail hG ha hatop hB hB0 hT⟩

/-- **Converse of the generalized central limit theorem** ([Feller, Vol. II, §XVII.5,
Theorem 2], [GK, §35, Theorem 2]): necessity of Feller's conditions, without symmetry. Let
`aₙ > 0`, `bₙ ∈ ℝ`, and suppose the laws of `(X₁ + ⋯ + Xₙ - bₙ) / aₙ` converge weakly to a law
`ν` which is not a Dirac mass. Then there is `0 < α ≤ 2` such that the truncated second moment
`U(x) = E[X² 1{|X| ≤ x}]` is regularly varying with index `2 - α`, and, if `α < 2`, the
two-sided tail `P(|X| > x)` is regularly varying with index `-α`, `n P(|X| > aₙ)` converges to
some `B > 0` (so `aₙ` is the right scale), and the tails are balanced:
`P(X > x) / P(|X| > x) → p` for some `p ∈ [0, 1]`. -/
theorem exists_isRegularlyVarying_tailBalance_of_tendsto (ha : ∀ n, 0 < a n)
    {ν : ProbabilityMeasure ℝ} (hnd : ∀ x, (ν : Measure ℝ) ≠ Measure.dirac x)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ α, 0 < α ∧ α ≤ 2 ∧ IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧
      (α < 2 → IsRegularlyVarying (absTail μ) (-α) ∧
        (∃ B > 0, Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a n)) atTop (𝓝 B)) ∧
        ∃ p, 0 ≤ p ∧ p ≤ 1 ∧ Tendsto (fun x => μ.real (Ioi x) / absTail μ x) atTop (𝓝 p)) := by
  obtain ⟨α, hα0, hα2, K, hK, hL⟩ := exists_tendsto_mul_sqRatio_symmLaw ha hnd hconv
  have hZs := isRegularlyVarying_minSqMoment_of_tendsto_mul_sqRatio ha hK hL
  rcases lt_or_eq_of_le hα2 with hlt | heq
  swap
  · subst heq
    refine ⟨2, hα0, le_rfl, ?_, fun h => absurd h (lt_irrefl _)⟩
    rw [sub_self] at hZs ⊢
    exact isRegularlyVarying_truncSecondMoment_of_minSqMoment (by norm_num)
      (isRegularlyVarying_minSqMoment_of_symmLaw hZs)
  have h := tailBalance_of_tendsto_mul_sqRatio_symmLaw ha hconv hα0 hlt hK hL
  exact ⟨α, hα0, hα2, isRegularlyVarying_truncSecondMoment_of_absTail hα0 hlt h.1, fun _ => h⟩

/-- **The Lévy measure of the limit** (asymmetric converse GCLT, [Feller, Vol. II, §XVII.5],
[GK, §35]): under the hypotheses of `exists_isRegularlyVarying_tailBalance_of_tendsto`, with
`α < 2`, there are `c₊, c₋ ≥ 0`, `c₊ + c₋ > 0`, such that for every `u > 0`,
`n P(X > aₙ u) → c₊ u ^ (-α)` and `n P(X < -aₙ u) → c₋ u ^ (-α)`; that is,
`n P(X / aₙ ∈ ·)` converges on `(0, ∞)` and on `(-∞, 0)` to `c₊ α x^{-α-1} dx` and
`c₋ α |x|^{-α-1} dx`. -/
theorem exists_tendsto_mul_tails_of_tendsto (ha : ∀ n, 0 < a n)
    {ν : ProbabilityMeasure ℝ} (hnd : ∀ x, (ν : Measure ℝ) ≠ Measure.dirac x)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 2 ∧ (α < 2 → ∃ cp cm : ℝ, 0 ≤ cp ∧ 0 ≤ cm ∧ 0 < cp + cm ∧
      ∀ u : ℝ, 0 < u →
        Tendsto (fun n : ℕ => (n : ℝ) * μ.real (Ioi (a n * u))) atTop (𝓝 (cp * u ^ (-α))) ∧
        Tendsto (fun n : ℕ => (n : ℝ) * μ.real (Iio (-(a n * u)))) atTop
          (𝓝 (cm * u ^ (-α)))) := by
  obtain ⟨α, hα0, hα2, -, h⟩ := exists_isRegularlyVarying_tailBalance_of_tendsto ha hnd hconv
  refine ⟨α, hα0, hα2, fun hlt => ?_⟩
  obtain ⟨hG, ⟨B, hB0, hB⟩, p, hp0, hp1, hp⟩ := h hlt
  have hGpos := absTail_pos hG
  have hatop : Tendsto a atTop atTop :=
    tendsto_atTop_of_tendsto_mul_comp (T := absTail μ) (L := fun _ => B)
      (absTail_antitone.antitoneOn _) (fun x _ => hGpos x) ha hB
  have hq : Tendsto (fun x => μ.real (Iio (-x)) / absTail μ x) atTop (𝓝 (1 - p)) := by
    refine (tendsto_const_nhds.sub hp).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    have := (hGpos x).ne'
    rw [absTail_eq_add hx] at this ⊢
    field_simp
    ring
  refine ⟨B * p, B * (1 - p), by positivity, mul_nonneg hB0.le (by linarith), by
    rw [← mul_add]; simpa using hB0, fun u hu => ⟨?_, ?_⟩⟩
  · have h1 := (tendsto_mul_comp_mul_of_tendsto hG hatop hB hu).mul
      (hp.comp (hatop.atTop_mul_const hu))
    rw [show B * u ^ (-α) * p = B * p * u ^ (-α) by ring] at h1
    refine h1.congr fun n => ?_
    have := (hGpos (a n * u)).ne'
    simp only [Function.comp]
    field_simp
  · have h1 := (tendsto_mul_comp_mul_of_tendsto hG hatop hB hu).mul
      (hq.comp (hatop.atTop_mul_const hu))
    rw [show B * u ^ (-α) * (1 - p) = B * (1 - p) * u ^ (-α) by ring] at h1
    refine h1.congr fun n => ?_
    have := (hGpos (a n * u)).ne'
    simp only [Function.comp]
    field_simp

end ConverseTailBalance

end GCLTConverse

end ExtremeValueTheory
