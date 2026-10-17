/-
Copyright (c) 2026 Federico Carrone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
module

public import ExtremeValueTheory.ForMathlib.Topology.Skorokhod.Separable
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Completeness of the Skorokhod space: Billingsley's metric `d°`

The Skorokhod `J₁` metric `d` on `D([0, 1], E)` is not complete. Following
[Billingsley, *Convergence of Probability Measures*, §12][billingsley1999] we introduce an
equivalent complete metric `d°`. For a time change `φ` (an order automorphism of `I = [0, 1]`)
let
`‖φ‖° = sup_{s < t} |log ((φ t - φ s) / (t - s))|`
be its *log-slope norm*, with values in `ℝ≥0∞` (it is finite exactly when `φ` is bi-Lipschitz),
and let
`d°(x, y) = inf_φ max (‖φ‖°, sup_t edist (x t) (y (φ t)))`.

The proof of completeness is Billingsley's: given a sequence with `d°(xₙ, xₙ₊₁) < 2⁻ⁿ` choose
time changes `μₙ` realising these distances. The compositions `μₙ₊ₘ ∘ ⋯ ∘ μₙ` converge, as
`m → ∞`, to time changes `λₙ` with `‖λₙ‖° ≤ 2¹⁻ⁿ` and `λₙ = λₙ₊₁ ∘ μₙ`, the functions
`xₙ ∘ λₙ⁻¹` are uniformly Cauchy, and their uniform limit `y` is càdlàg with `d°(xₙ, y) → 0`.

## Main definitions

* `unitInterval.logSlopeNorm φ`: the log-slope norm `‖φ‖°` of a time change.
* `billingsleyEDist x y`: Billingsley's distance `d°` between functions `I → E`.
* `SkorokhodSpace.Billingsley E`: a type synonym for `D([0, 1], E)` carrying the metric `d°`.
* `SkorokhodSpace.homeomorphBillingsley`: the identity `D([0, 1], E) ≃ₜ Billingsley E`.

## Main statements

* `billingsleyEDist_triangle`, `billingsleyEDist_comm`, `billingsleyEDist_self`, and
  `SkorokhodSpace.Billingsley.instMetricSpace`: `d°` is a metric on `D([0, 1], E)`.
* `skorokhodEDist_le_exp_billingsleyEDist_sub_one`: `d ≤ exp d° - 1` (Billingsley (12.16)).
* `IsCadlag.exists_billingsleyEDist_lt`: at a càdlàg `x`, `d`-small implies `d°`-small
  (Billingsley, Theorem 12.1). Hence `d` and `d°` are topologically equivalent
  (`SkorokhodSpace.homeomorphBillingsley`).
* `SkorokhodSpace.Billingsley.instCompleteSpace`: `(D, d°)` is complete when `E` is
  (Billingsley, Theorem 12.2).
* `SkorokhodSpace.instIsCompletelyMetrizableSpace`, `SkorokhodSpace.instPolishSpace`:
  `D([0, 1], E)` with the `J₁` topology is completely metrizable, and Polish when `E` is moreover
  separable.
* `IsCadlag.of_tendstoUniformly`: a uniform limit of càdlàg functions is càdlàg.

## References

* [P. Billingsley, *Convergence of Probability Measures*][billingsley1999]
-/

@[expose] public section

open Filter Set Topology Metric unitInterval TopologicalSpace
open scoped ENNReal

namespace unitInterval

/-- The *log-slope norm* of a time change `φ` of the unit interval,
`‖φ‖° = sup_{s < t} |log ((φ t - φ s) / (t - s))|`
([Billingsley, *Convergence of Probability Measures*, (12.13)][billingsley1999]).
It takes values in `ℝ≥0∞` and is infinite unless `φ` is bi-Lipschitz. -/
noncomputable def logSlopeNorm (φ : I ≃o I) : ℝ≥0∞ :=
  ⨆ (s : I) (t : I) (_ : s < t), ENNReal.ofReal |Real.log (((φ t : ℝ) - φ s) / ((t : ℝ) - s))|

private lemma abs_log_le_iff {q r : ℝ} (hq : 0 < q) :
    |Real.log q| ≤ r ↔ Real.exp (-r) ≤ q ∧ q ≤ Real.exp r := by
  rw [abs_le, Real.le_log_iff_exp_le hq, Real.log_le_iff_le_exp hq]

lemma ofReal_abs_log_le_logSlopeNorm (φ : I ≃o I) {s t : I} (hst : s < t) :
    ENNReal.ofReal |Real.log (((φ t : ℝ) - φ s) / ((t : ℝ) - s))| ≤ logSlopeNorm φ :=
  le_iSup₂_of_le (f := fun (s t : I) ↦ ⨆ (_ : s < t),
    ENNReal.ofReal |Real.log (((φ t : ℝ) - φ s) / ((t : ℝ) - s))|) s t (le_iSup_of_le hst le_rfl)

/-- The log-slope norm of `φ` is at most `r` if and only if the increments of `φ` are within a
factor `exp (± r)` of the increments of the identity. -/
lemma logSlopeNorm_le_ofReal_iff {φ : I ≃o I} {r : ℝ} (hr : 0 ≤ r) :
    logSlopeNorm φ ≤ ENNReal.ofReal r ↔ ∀ s t : I, s ≤ t →
      Real.exp (-r) * ((t : ℝ) - s) ≤ (φ t : ℝ) - φ s ∧
        (φ t : ℝ) - φ s ≤ Real.exp r * ((t : ℝ) - s) := by
  simp only [logSlopeNorm, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hr]
  constructor
  · intro h s t hst
    rcases hst.lt_or_eq with hst | rfl
    · have hts : 0 < (t : ℝ) - s := sub_pos.2 (Subtype.coe_lt_coe.2 hst)
      have hpos : 0 < ((φ t : ℝ) - φ s) / ((t : ℝ) - s) :=
        div_pos (sub_pos.2 (Subtype.coe_lt_coe.2 (φ.strictMono hst))) hts
      obtain ⟨h1, h2⟩ := (abs_log_le_iff hpos).1 (h s t hst)
      exact ⟨(le_div_iff₀ hts).1 h1, (div_le_iff₀ hts).1 h2⟩
    · simp
  · intro h s t hst
    have hts : 0 < (t : ℝ) - s := sub_pos.2 (Subtype.coe_lt_coe.2 hst)
    have hpos : 0 < ((φ t : ℝ) - φ s) / ((t : ℝ) - s) :=
      div_pos (sub_pos.2 (Subtype.coe_lt_coe.2 (φ.strictMono hst))) hts
    obtain ⟨h1, h2⟩ := h s t hst.le
    exact (abs_log_le_iff hpos).2 ⟨(le_div_iff₀ hts).2 h1, (div_le_iff₀ hts).2 h2⟩

@[simp]
lemma logSlopeNorm_refl : logSlopeNorm (OrderIso.refl I) = 0 :=
  nonpos_iff_eq_zero.1 <| by
    simpa using (logSlopeNorm_le_ofReal_iff (φ := OrderIso.refl I) le_rfl).2 fun s t _ ↦ by simp

lemma logSlopeNorm_trans (φ ψ : I ≃o I) :
    logSlopeNorm (φ.trans ψ) ≤ logSlopeNorm φ + logSlopeNorm ψ := by
  refine iSup₂_le fun s t ↦ iSup_le fun hst ↦ ?_
  have h1 : 0 < (t : ℝ) - s := sub_pos.2 (Subtype.coe_lt_coe.2 hst)
  have h2 : 0 < (φ t : ℝ) - φ s := sub_pos.2 (Subtype.coe_lt_coe.2 (φ.strictMono hst))
  have h3 : 0 < (ψ (φ t) : ℝ) - ψ (φ s) :=
    sub_pos.2 (Subtype.coe_lt_coe.2 (ψ.strictMono (φ.strictMono hst)))
  have e : ((ψ (φ t) : ℝ) - ψ (φ s)) / ((t : ℝ) - s) =
      ((ψ (φ t) : ℝ) - ψ (φ s)) / ((φ t : ℝ) - φ s) * (((φ t : ℝ) - φ s) / ((t : ℝ) - s)) := by
    field_simp
  simp only [OrderIso.trans_apply]
  rw [e, Real.log_mul (div_pos h3 h2).ne' (div_pos h2 h1).ne', add_comm (logSlopeNorm φ)]
  calc ENNReal.ofReal |Real.log (((ψ (φ t) : ℝ) - ψ (φ s)) / ((φ t : ℝ) - φ s)) +
        Real.log (((φ t : ℝ) - φ s) / ((t : ℝ) - s))|
      ≤ ENNReal.ofReal (|Real.log (((ψ (φ t) : ℝ) - ψ (φ s)) / ((φ t : ℝ) - φ s))| +
        |Real.log (((φ t : ℝ) - φ s) / ((t : ℝ) - s))|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ ≤ _ := ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add (ofReal_abs_log_le_logSlopeNorm ψ (φ.strictMono hst))
        (ofReal_abs_log_le_logSlopeNorm φ hst)

@[simp]
lemma logSlopeNorm_symm (φ : I ≃o I) : logSlopeNorm φ.symm = logSlopeNorm φ := by
  suffices H : ∀ φ : I ≃o I, logSlopeNorm φ.symm ≤ logSlopeNorm φ from
    le_antisymm (H φ) (by simpa using H φ.symm)
  intro φ
  refine iSup₂_le fun s t ↦ iSup_le fun hst ↦ ?_
  have hst' : φ.symm s < φ.symm t := φ.symm.strictMono hst
  have e : ((t : ℝ) - s) = (φ (φ.symm t) : ℝ) - φ (φ.symm s) := by simp
  rw [e, ← inv_div, Real.log_inv, abs_neg]
  exact ofReal_abs_log_le_logSlopeNorm φ hst'

/-- A time change with log-slope norm at most `r` is within `exp r - 1` of the identity
([Billingsley, (12.16)][billingsley1999]). -/
lemma dist_apply_le_of_logSlopeNorm_le {φ : I ≃o I} {r : ℝ} (hr : 0 ≤ r)
    (h : logSlopeNorm φ ≤ ENNReal.ofReal r) (t : I) : dist (φ t) t ≤ Real.exp r - 1 := by
  obtain ⟨h1, h2⟩ := (logSlopeNorm_le_ofReal_iff hr).1 h 0 t (show (0 : I) ≤ t from t.2.1)
  have h0 : φ 0 = 0 := φ.map_bot
  rw [h0, Icc.coe_zero, sub_zero, sub_zero] at h1 h2
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have he1 := Real.add_one_le_exp r
  have he2 := Real.add_one_le_exp (-r)
  rw [Subtype.dist_eq, Real.dist_eq, abs_le]
  constructor
  · nlinarith [mul_nonneg (by linarith : 0 ≤ Real.exp (-r) - 1 + (Real.exp r - 1)) ht0,
      mul_nonneg (by linarith : 0 ≤ Real.exp r - 1) (by linarith : 0 ≤ 1 - (t : ℝ))]
  · nlinarith [mul_nonneg (by linarith : 0 ≤ Real.exp r - 1) (by linarith : 0 ≤ 1 - (t : ℝ))]

lemma edist_apply_le_of_logSlopeNorm_le {φ : I ≃o I} {r : ℝ} (hr : 0 ≤ r)
    (h : logSlopeNorm φ ≤ ENNReal.ofReal r) (t : I) :
    edist (φ t) t ≤ ENNReal.ofReal (Real.exp r - 1) := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_apply_le_of_logSlopeNorm_le hr h t)

end unitInterval

variable {E : Type*}

section billingsleyEDist

variable [PseudoEMetricSpace E] {x y z : I → E} {φ : I ≃o I} {ε : ℝ≥0∞}

/-- The cost of matching `x` with `y` through the time change `φ` in Billingsley's metric:
the larger of the log-slope norm of `φ` and the uniform distance from `x` to `y ∘ φ`. -/
noncomputable def billingsleyEDistWith (φ : I ≃o I) (x y : I → E) : ℝ≥0∞ :=
  max (logSlopeNorm φ) (⨆ t, edist (x t) (y (φ t)))

/-- *Billingsley's metric* `d°` on functions `I → E`
([Billingsley, *Convergence of Probability Measures*, (12.16)][billingsley1999]):
the infimum over all time changes `φ` of `max ‖φ‖° (sup_t edist (x t) (y (φ t)))`, where `‖φ‖°`
is the log-slope norm `unitInterval.logSlopeNorm`. -/
noncomputable def billingsleyEDist (x y : I → E) : ℝ≥0∞ :=
  ⨅ φ : I ≃o I, billingsleyEDistWith φ x y

lemma logSlopeNorm_le_billingsleyEDistWith (φ : I ≃o I) (x y : I → E) :
    logSlopeNorm φ ≤ billingsleyEDistWith φ x y :=
  le_max_left _ _

lemma edist_apply_apply_le_billingsleyEDistWith (φ : I ≃o I) (x y : I → E) (t : I) :
    edist (x t) (y (φ t)) ≤ billingsleyEDistWith φ x y :=
  (le_iSup (fun t ↦ edist (x t) (y (φ t))) t).trans (le_max_right _ _)

lemma billingsleyEDistWith_le (hφ : logSlopeNorm φ ≤ ε)
    (hxy : ∀ t, edist (x t) (y (φ t)) ≤ ε) : billingsleyEDistWith φ x y ≤ ε :=
  max_le hφ (iSup_le hxy)

/-- To bound Billingsley's distance, it suffices to exhibit a single good time change. -/
lemma billingsleyEDist_le_of_forall (φ : I ≃o I) (hφ : logSlopeNorm φ ≤ ε)
    (hxy : ∀ t, edist (x t) (y (φ t)) ≤ ε) : billingsleyEDist x y ≤ ε :=
  (iInf_le _ φ).trans (billingsleyEDistWith_le hφ hxy)

/-- If Billingsley's distance is less than `ε`, there is a time change of log-slope norm less
than `ε` matching `x` with `y` up to `ε`. -/
lemma exists_timeChange_of_billingsleyEDist_lt (h : billingsleyEDist x y < ε) :
    ∃ φ : I ≃o I, logSlopeNorm φ < ε ∧ ∀ t, edist (x t) (y (φ t)) < ε := by
  obtain ⟨φ, hφ⟩ := iInf_lt_iff.1 h
  exact ⟨φ, (logSlopeNorm_le_billingsleyEDistWith φ x y).trans_lt hφ,
    fun t ↦ (edist_apply_apply_le_billingsleyEDistWith φ x y t).trans_lt hφ⟩

@[simp]
lemma billingsleyEDist_self (x : I → E) : billingsleyEDist x x = 0 :=
  nonpos_iff_eq_zero.1 <| billingsleyEDist_le_of_forall (OrderIso.refl I) (by simp) (by simp)

/-- Billingsley's distance is bounded by the uniform distance. -/
lemma billingsleyEDist_le_iSup_edist (x y : I → E) :
    billingsleyEDist x y ≤ ⨆ t, edist (x t) (y t) :=
  billingsleyEDist_le_of_forall (OrderIso.refl I) (by simp)
    (fun t ↦ le_iSup (fun t ↦ edist (x t) (y t)) t)

lemma billingsleyEDist_comm (x y : I → E) : billingsleyEDist x y = billingsleyEDist y x := by
  suffices H : ∀ x y : I → E, billingsleyEDist y x ≤ billingsleyEDist x y from
    le_antisymm (H y x) (H x y)
  intro x y
  refine le_iInf fun φ ↦ billingsleyEDist_le_of_forall φ.symm ?_ (fun t ↦ ?_)
  · rw [logSlopeNorm_symm]
    exact logSlopeNorm_le_billingsleyEDistWith φ x y
  · have := edist_apply_apply_le_billingsleyEDistWith φ x y (φ.symm t)
    rwa [OrderIso.apply_symm_apply, edist_comm] at this

lemma billingsleyEDist_triangle (x y z : I → E) :
    billingsleyEDist x z ≤ billingsleyEDist x y + billingsleyEDist y z := by
  refine ENNReal.le_iInf_add_iInf fun φ ψ ↦
    billingsleyEDist_le_of_forall (φ.trans ψ) ?_ (fun t ↦ ?_)
  · exact (logSlopeNorm_trans φ ψ).trans (add_le_add
      (logSlopeNorm_le_billingsleyEDistWith φ x y) (logSlopeNorm_le_billingsleyEDistWith ψ y z))
  · calc edist (x t) (z (ψ (φ t))) ≤ edist (x t) (y (φ t)) + edist (y (φ t)) (z (ψ (φ t))) :=
          edist_triangle _ _ _
      _ ≤ billingsleyEDistWith φ x y + billingsleyEDistWith ψ y z :=
        add_le_add (edist_apply_apply_le_billingsleyEDistWith φ x y t)
          (edist_apply_apply_le_billingsleyEDistWith ψ y z (φ t))

/-- If Billingsley's distance is less than `r`, the Skorokhod distance is at most `exp r - 1`.
-/
theorem skorokhodEDist_le_of_billingsleyEDist_lt {r : ℝ} (hr : 0 ≤ r)
    (h : billingsleyEDist x y < ENNReal.ofReal r) :
    skorokhodEDist x y ≤ ENNReal.ofReal (Real.exp r - 1) := by
  obtain ⟨φ, hφ, hxy⟩ := exists_timeChange_of_billingsleyEDist_lt h
  refine skorokhodEDist_le_of_forall φ (fun t ↦ edist_apply_le_of_logSlopeNorm_le hr hφ.le t)
    (fun t ↦ (hxy t).le.trans (ENNReal.ofReal_le_ofReal ?_))
  linarith [Real.add_one_le_exp r]

/-- **Billingsley, (12.16).** The Skorokhod distance is bounded by `exp d° - 1`, where `d°` is
Billingsley's distance. -/
theorem skorokhodEDist_le_exp_billingsleyEDist_sub_one (h : billingsleyEDist x y ≠ ⊤) :
    skorokhodEDist x y ≤ ENNReal.ofReal (Real.exp (billingsleyEDist x y).toReal - 1) := by
  set a := (billingsleyEDist x y).toReal
  have ha : billingsleyEDist x y = ENNReal.ofReal a := (ENNReal.ofReal_toReal h).symm
  have hT : Tendsto (fun r ↦ ENNReal.ofReal (Real.exp r - 1)) (𝓝[>] a)
      (𝓝 (ENNReal.ofReal (Real.exp a - 1))) :=
    ((ENNReal.continuous_ofReal.comp (by fun_prop : Continuous fun r : ℝ ↦ Real.exp r - 1)).tendsto
      a).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hT ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 < r := ENNReal.toReal_nonneg.trans_lt hr
  exact skorokhodEDist_le_of_billingsleyEDist_lt hr0.le
    (by rw [ha]; exact (ENNReal.ofReal_lt_ofReal_iff hr0).2 hr)

lemma skorokhodEDist_eq_zero_of_billingsleyEDist_eq_zero (h : billingsleyEDist x y = 0) :
    skorokhodEDist x y = 0 := by
  have := skorokhodEDist_le_exp_billingsleyEDist_sub_one (h ▸ ENNReal.zero_ne_top)
  simpa [h] using this

private lemma exists_pos_separated (S : Finset I) :
    ∃ η > (0 : ℝ), ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 4 * η ≤ dist a b := by
  classical
  set P := (S ×ˢ S).filter fun p : I × I ↦ p.1 ≠ p.2
  rcases P.eq_empty_or_nonempty with hP | hP
  · refine ⟨1, one_pos, fun a ha b hb hab ↦ ?_⟩
    have : (a, b) ∈ P := Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩
    simp [hP] at this
  · obtain ⟨p₀, hp₀, hmin⟩ := P.exists_min_image (fun p ↦ dist p.1 p.2) hP
    have hne := dist_pos.2 (Finset.mem_filter.1 hp₀).2
    refine ⟨dist p₀.1 p₀.2 / 4, by positivity, fun a ha b hb hab ↦ ?_⟩
    have := hmin (a, b) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩)
    linarith

/-- **Billingsley, Theorem 12.1.** For a càdlàg function `x` and `ε > 0` there is `δ > 0` such
that every `y` at Skorokhod distance less than `δ` from `x` is at Billingsley distance less than
`ε` from `x`. -/
theorem IsCadlag.exists_billingsleyEDist_lt (hx : IsCadlag x) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : I → E, skorokhodEDist x y < δ → billingsleyEDist x y < ε := by
  classical
  obtain ⟨ε₁, hε₁, hε₁ε⟩ := exists_between hε
  set ε₀ := ε₁ / 2
  have hε₀ : 0 < ε₀ := ENNReal.half_pos hε₁.ne'
  have hε₀top : ε₀ ≠ ⊤ := ne_top_of_le_ne_top hε₁ε.ne_top ENNReal.half_le_self
  set e := ε₀.toReal
  have he : 0 < e := ENNReal.toReal_pos hε₀.ne' hε₀top
  obtain ⟨s, hs⟩ := hx.exists_finset_edist_lt hε₀
  obtain ⟨ρ, hρ, hsep⟩ := exists_pos_separated (insert 0 (insert 1 s))
  have hmemS {r : I} (hr : r ∈ s) : r ∈ insert 0 (insert 1 s) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)
  set R := s.filter fun r ↦ r ≠ 0 ∧ r ≠ 1
  set k : ℝ := (R.card : ℝ)
  have hR0 (r : I) (hr : r ∈ R) : 2 * ρ ≤ (r : ℝ) ∧ (r : ℝ) + 2 * ρ ≤ 1 := by
    obtain ⟨hrs, h0, h1⟩ := Finset.mem_filter.1 hr
    have h0' := hsep r (hmemS hrs) 0 (Finset.mem_insert_self _ _) h0
    have h1' := hsep r (hmemS hrs) 1 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h1
    rw [Subtype.dist_eq, Real.dist_eq] at h0' h1'
    simp only [Icc.coe_zero, sub_zero, Icc.coe_one] at h0' h1'
    rw [abs_of_nonneg r.2.1] at h0'
    rw [abs_of_nonpos (sub_nonpos.2 r.2.2)] at h1'
    constructor <;> linarith
  set δr := min (ρ / 2) (min (e / 2) (e * ρ / (k + 1)))
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hδr : 0 < δr := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨ENNReal.ofReal δr, ENNReal.ofReal_pos.2 hδr, fun y hy ↦ ?_⟩
  obtain ⟨μ, hμ, hxy⟩ := exists_timeChange_of_skorokhodEDist_lt hy
  have hμd (t : I) : dist (μ t) t < δr := edist_lt_ofReal.1 (hμ t)
  obtain ⟨φ, hφR, -, -, hφslope⟩ := unitInterval.exists_orderIso_apply_eq_of_separated_and_slope
    R μ hR0
    (fun r hr r' hr' hne ↦ hsep r (hmemS (Finset.mem_filter.1 hr).1) r'
      (hmemS (Finset.mem_filter.1 hr').1) hne)
    (fun r _ ↦ (hμd r).trans_le ((min_le_left _ _).trans (by linarith)))
  -- The log-slope norm of `φ` is at most `ε₀`.
  have hsum : 2 * ∑ r ∈ R, dist (μ r) r / (2 * ρ) ≤ e := by
    calc 2 * ∑ r ∈ R, dist (μ r) r / (2 * ρ) ≤ 2 * ∑ r ∈ R, δr / (2 * ρ) := by
          gcongr with r hr
          exact (hμd r).le
      _ = k * δr / ρ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
          rfl
      _ ≤ e := by
          rw [div_le_iff₀ hρ]
          have h1 : δr ≤ e * ρ / (k + 1) := (min_le_right _ _).trans (min_le_right _ _)
          calc k * δr ≤ k * (e * ρ / (k + 1)) := mul_le_mul_of_nonneg_left h1 hk
            _ ≤ e * ρ := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity)]
              nlinarith [mul_pos he hρ]
  have hφn : logSlopeNorm φ ≤ ε₀ := by
    rw [← ENNReal.ofReal_toReal hε₀top]
    refine (logSlopeNorm_le_ofReal_iff he.le).2 fun s t hst ↦ ?_
    obtain ⟨h1, h2⟩ := hφslope s t hst
    have hts : 0 ≤ (t : ℝ) - s := sub_nonneg.2 (Subtype.coe_le_coe.2 hst)
    exact ⟨(mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg hsum)) hts).trans h1,
      h2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hsum) hts)⟩
  -- `φ` agrees with `μ` on the cut points, so `ψ = μ⁻¹ ∘ φ` preserves the cells.
  have hφs (r : I) (hr : r ∈ s) : φ r = μ r := by
    by_cases h0 : r = 0
    · subst h0
      rw [show φ 0 = 0 from φ.map_bot, show μ 0 = 0 from μ.map_bot]
    by_cases h1 : r = 1
    · subst h1
      rw [show φ 1 = 1 from φ.map_top, show μ 1 = 1 from μ.map_top]
    exact hφR r (Finset.mem_filter.2 ⟨hr, h0, h1⟩)
  set ψ := φ.trans μ.symm
  have hψ (r : I) (hr : r ∈ s) : ψ r = r := by
    simp [ψ, hφs r hr]
  have hμψ (t : I) : μ (ψ t) = φ t := by simp [ψ]
  have hiff (r : I) (hr : r ∈ s) (t : I) : r ≤ t ↔ r ≤ ψ t := by
    conv_rhs => rw [← hψ r hr]
    exact ψ.le_iff_le.symm
  have hcell (t : I) : edist (x t) (x (ψ t)) < ε₀ := by
    rcases le_total t (ψ t) with htp | hpt
    · refine hs t (ψ t) htp fun r hr ↦ ?_
      rcases le_or_gt r t with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge fun h' ↦ (not_le.2 h) ((hiff r hr t).2 h'))
    · rw [edist_comm]
      refine hs (ψ t) t hpt fun r hr ↦ ?_
      rcases le_or_gt r (ψ t) with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge fun h' ↦ (not_le.2 h) ((hiff r hr t).1 h'))
  have hδε₀ : ENNReal.ofReal δr ≤ ε₀ := by
    rw [← ENNReal.ofReal_toReal hε₀top]
    exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _) |>.trans
      (by linarith))
  refine lt_of_le_of_lt ?_ hε₁ε
  refine billingsleyEDist_le_of_forall φ (hφn.trans ENNReal.half_le_self) fun t ↦ ?_
  calc edist (x t) (y (φ t)) ≤ edist (x t) (x (ψ t)) + edist (x (ψ t)) (y (μ (ψ t))) := by
        rw [hμψ]; exact edist_triangle _ _ _
    _ ≤ ε₀ + ε₀ := add_le_add (hcell t).le ((hxy (ψ t)).le.trans hδε₀)
    _ = ε₁ := ENNReal.add_halves ε₁

end billingsleyEDist

lemma billingsleyEDist_ne_top {E : Type*} [PseudoMetricSpace E] {x y : I → E}
    (hx : Bornology.IsBounded (range x)) (hy : Bornology.IsBounded (range y)) :
    billingsleyEDist x y ≠ ⊤ := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (hx.union hy)
  have hC0 : 0 ≤ C := dist_nonneg.trans (hC (Or.inl ⟨0, rfl⟩) (Or.inl ⟨0, rfl⟩))
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((billingsleyEDist_le_iSup_edist x y).trans
    (iSup_le fun t ↦ (edist_le_ofReal hC0).2 (hC (Or.inl ⟨t, rfl⟩) (Or.inr ⟨t, rfl⟩))))

/-! ### Uniform limits of càdlàg functions -/

/-- A uniform limit of càdlàg functions with values in a complete space is càdlàg. -/
theorem IsCadlag.of_tendstoUniformly {X : Type*} [TopologicalSpace X] [LinearOrder X]
    [PseudoEMetricSpace E] [CompleteSpace E] {F : ℕ → X → E} {f : X → E}
    (hF : ∀ n, IsCadlag (F n)) (h : TendstoUniformly F f atTop) : IsCadlag f where
  isRightContinuous x := continuousWithinAt_Ioi_iff_Ici.2 <|
    continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt self_mem_Ici
      fun u hu ↦ by
        obtain ⟨n, hn⟩ := (h u hu).exists
        exact ⟨univ, univ_mem, F n, continuousWithinAt_Ioi_iff_Ici.1 ((hF n).isRightContinuous x),
          fun y _ ↦ hn y⟩
  tendsto_nhdsLT x := by
    rcases eq_or_neBot (𝓝[<] x) with hb | hb
    · exact ⟨f x, by rw [hb]; exact tendsto_bot⟩
    refine cauchy_map_iff_exists_tendsto.1 (EMetric.cauchy_iff.2 ⟨(hb.map f).ne, fun ε hε ↦ ?_⟩)
    set δ := ε / 2 / 2
    have hδ : 0 < δ := ENNReal.half_pos (ENNReal.half_pos hε.ne').ne'
    obtain ⟨n, hn⟩ := (EMetric.tendstoUniformly_iff.1 h δ hδ).exists
    obtain ⟨l, hl⟩ := (hF n).tendsto_nhdsLT x
    have key (c : X) (hc : c ∈ F n ⁻¹' Metric.eball l δ) : edist (f c) l < ε / 2 :=
      calc edist (f c) l ≤ edist (f c) (F n c) + edist (F n c) l := edist_triangle _ _ _
        _ < δ + δ := ENNReal.add_lt_add (hn c) hc
        _ = ε / 2 := ENNReal.add_halves _
    refine ⟨f '' (F n ⁻¹' Metric.eball l δ), image_mem_map (hl (Metric.eball_mem_nhds l hδ)), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    calc edist (f a) (f b) ≤ edist (f a) l + edist (f b) l := edist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (key a ha) (key b hb)
      _ = ε := ENNReal.add_halves ε

/-- Composing a càdlàg function with a time change gives a càdlàg function. -/
theorem IsCadlag.comp_orderIso [TopologicalSpace E] {f : I → E} (hf : IsCadlag f)
    (ψ : I ≃o I) : IsCadlag (f ∘ ψ) where
  isRightContinuous t :=
    (hf.isRightContinuous (ψ t)).comp ψ.continuous.continuousWithinAt
      fun _ hs ↦ ψ.strictMono hs
  tendsto_nhdsLT t := by
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (ψ t)
    exact ⟨l, hl.comp (tendsto_nhdsWithin_iff.2 ⟨(ψ.continuous.tendsto t).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun _ hs ↦ ψ.strictMono hs⟩)⟩

namespace unitInterval

/-- A self-map of the unit interval fixing `0` and `1` whose increments are within a factor
`exp (± r)` of the increments of the identity is a time change. -/
lemma exists_orderIso_of_slope {f : I → I} {r : ℝ} (h0 : f 0 = 0) (h1 : f 1 = 1)
    (h : ∀ s t : I, s ≤ t → Real.exp (-r) * ((t : ℝ) - s) ≤ (f t : ℝ) - f s ∧
      (f t : ℝ) - f s ≤ Real.exp r * ((t : ℝ) - s)) :
    ∃ φ : I ≃o I, ∀ t, φ t = f t := by
  have hmono : StrictMono f := fun s t hst ↦ by
    have h₁ := (h s t hst.le).1
    have : 0 < (t : ℝ) - s := sub_pos.2 (Subtype.coe_lt_coe.2 hst)
    have := mul_pos (Real.exp_pos (-r)) this
    exact Subtype.coe_lt_coe.1 (by linarith)
  have key (s t : I) (hst : s ≤ t) : dist (f s) (f t) ≤ Real.exp r * dist s t := by
    have hst' : 0 ≤ (t : ℝ) - s := sub_nonneg.2 (Subtype.coe_le_coe.2 hst)
    have hf' : 0 ≤ (f t : ℝ) - f s :=
      (mul_nonneg (Real.exp_pos _).le hst').trans (h s t hst).1
    rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg hf', dist_comm, Subtype.dist_eq,
      Real.dist_eq, abs_of_nonneg hst']
    exact (h s t hst).2
  have hcont : Continuous f := by
    refine (LipschitzWith.of_dist_le_mul (K := ⟨Real.exp r, (Real.exp_pos r).le⟩)
      fun s t ↦ ?_).continuous
    rcases le_total s t with hst | hst
    · exact key s t hst
    · rw [dist_comm, dist_comm s]
      exact key t s hst
  have hsurj : Function.Surjective f := fun y ↦
    intermediate_value_univ 0 1 hcont ⟨by rw [h0]; exact nonneg', by rw [h1]; exact le_one'⟩
  exact ⟨StrictMono.orderIsoOfSurjective f hmono hsurj, fun t ↦ rfl⟩

/-- The composition `μ (n + m - 1) ∘ ⋯ ∘ μ (n + 1) ∘ μ n` of `m` consecutive time changes. -/
noncomputable def compSeq (μ : ℕ → I ≃o I) : ℕ → ℕ → I ≃o I
  | _, 0 => OrderIso.refl I
  | n, m + 1 => (μ n).trans (compSeq μ (n + 1) m)

lemma compSeq_succ_apply (μ : ℕ → I ≃o I) (n m : ℕ) (t : I) :
    compSeq μ n (m + 1) t = compSeq μ (n + 1) m (μ n t) := rfl

lemma compSeq_succ_apply' (μ : ℕ → I ≃o I) (n m : ℕ) (t : I) :
    compSeq μ n (m + 1) t = μ (n + m) (compSeq μ n m t) := by
  induction m generalizing n t with
  | zero => rfl
  | succ m ih =>
    rw [compSeq_succ_apply, ih (n + 1), compSeq_succ_apply, show n + 1 + m = n + (m + 1) by omega]

lemma logSlopeNorm_compSeq_le {μ : ℕ → I ≃o I}
    (hμ : ∀ n, logSlopeNorm (μ n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) (n m : ℕ) :
    logSlopeNorm (compSeq μ n m) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := by
  induction m generalizing n with
  | zero => simp [compSeq]
  | succ m ih =>
    calc logSlopeNorm (compSeq μ n (m + 1))
        ≤ logSlopeNorm (μ n) + logSlopeNorm (compSeq μ (n + 1) m) := logSlopeNorm_trans _ _
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) + ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (n + 1)) :=
          add_le_add (hμ n) (ih (n + 1))
      _ = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

end unitInterval

private lemma ofReal_half_pow (n : ℕ) : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = 1 / 2 ^ n := by
  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat, one_div, ENNReal.inv_pow]

private lemma tendsto_ofReal_two_mul_half_pow :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  refine ENNReal.tendsto_ofReal ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul 2

private lemma exists_ofReal_exp_sub_one_lt {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r > 0, ENNReal.ofReal (Real.exp r - 1) < ε := by
  have hT : Tendsto (fun r ↦ ENNReal.ofReal (Real.exp r - 1)) (𝓝[>] 0) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.comp
      (by fun_prop : Continuous fun r : ℝ ↦ Real.exp r - 1)).tendsto 0
    simp only [Function.comp_apply, Real.exp_zero, sub_self, ENNReal.ofReal_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨r, hr, hr0⟩ := ((hT.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  exact ⟨r, hr0, hr⟩

/-! ### The Skorokhod space with Billingsley's metric -/

namespace SkorokhodSpace

/-- The Skorokhod space `D([0, 1], E)` equipped with Billingsley's metric `d°`
(`billingsleyEDist`) instead of the Skorokhod `J₁` metric. The two metrics induce the same
topology (`SkorokhodSpace.homeomorphBillingsley`), and `d°` is complete when `E` is
([Billingsley, Theorem 12.2][billingsley1999]). -/
def Billingsley (E : Type*) [TopologicalSpace E] := SkorokhodSpace E

section TopologicalSpace

variable [TopologicalSpace E]

/-- The identity map from the Skorokhod space to its copy with Billingsley's metric. -/
def toBillingsley : SkorokhodSpace E ≃ Billingsley E := Equiv.refl _

namespace Billingsley

instance instFunLike : FunLike (Billingsley E) I E :=
  inferInstanceAs (FunLike (SkorokhodSpace E) I E)

@[simp]
lemma coe_toBillingsley (x : SkorokhodSpace E) : ⇑(toBillingsley x) = x := rfl

@[simp]
lemma coe_toBillingsley_symm (x : Billingsley E) : ⇑(toBillingsley.symm x) = x := rfl

lemma isCadlag (x : Billingsley E) : IsCadlag x := (toBillingsley.symm x).isCadlag

end Billingsley

end TopologicalSpace

namespace Billingsley

/-- Billingsley's pseudo extended metric `d°` on `D([0, 1], E)`. -/
noncomputable instance instPseudoEMetricSpace [PseudoEMetricSpace E] :
    PseudoEMetricSpace (Billingsley E) where
  edist x y := billingsleyEDist x y
  edist_self x := billingsleyEDist_self x
  edist_comm x y := billingsleyEDist_comm x y
  edist_triangle x y z := billingsleyEDist_triangle x y z

lemma edist_def [PseudoEMetricSpace E] (x y : Billingsley E) :
    edist x y = billingsleyEDist x y := rfl

/-- Billingsley's extended metric `d°` on `D([0, 1], E)`. -/
noncomputable instance instEMetricSpace [EMetricSpace E] : EMetricSpace (Billingsley E) where
  eq_of_edist_eq_zero h := toBillingsley.symm.injective <|
    eq_of_edist_eq_zero (α := SkorokhodSpace E)
      (skorokhodEDist_eq_zero_of_billingsleyEDist_eq_zero h)

/-- Billingsley's pseudometric `d°` on `D([0, 1], E)`. -/
noncomputable instance instPseudoMetricSpace [PseudoMetricSpace E] :
    PseudoMetricSpace (Billingsley E) :=
  PseudoEMetricSpace.toPseudoMetricSpace fun x y ↦
    billingsleyEDist_ne_top (toBillingsley.symm x).isBounded_range
      (toBillingsley.symm y).isBounded_range

/-- Billingsley's metric `d°` on `D([0, 1], E)`. -/
noncomputable instance instMetricSpace [MetricSpace E] : MetricSpace (Billingsley E) where
  eq_of_dist_eq_zero {x y} h := eq_of_edist_eq_zero <| by
    rw [edist_dist, h, ENNReal.ofReal_zero]

/-- **Billingsley, Theorem 12.2.** The Skorokhod space `D([0, 1], E)` is complete for
Billingsley's metric `d°` when `E` is complete. -/
instance instCompleteSpace [PseudoEMetricSpace E] [CompleteSpace E] :
    CompleteSpace (Billingsley E) := by
  refine EMetric.complete_of_convergent_controlled_sequences
    (fun n ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) (fun n ↦ ENNReal.ofReal_pos.2 (by positivity))
    fun u hu ↦ ?_
  have hu' (n : ℕ) : billingsleyEDist (u n) (u (n + 1)) < ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
    hu n n (n + 1) le_rfl (Nat.le_succ n)
  choose μ hμ hμxy using fun n ↦ exists_timeChange_of_billingsleyEDist_lt (hu' n)
  -- The compositions `μ (n + m - 1) ∘ ⋯ ∘ μ n` converge, as `m → ∞`, to a time change `λ n`.
  have hP (n m : ℕ) := logSlopeNorm_compSeq_le (fun n ↦ (hμ n).le) n m
  have hPb (n m : ℕ) (s t : I) (hst : s ≤ t) :=
    (logSlopeNorm_le_ofReal_iff (by positivity)).1 (hP n m) s t hst
  have hμd (k : ℕ) (t : I) : dist (μ k t) t ≤ 2 * (1 / 2 : ℝ) ^ k := by
    refine (dist_apply_le_of_logSlopeNorm_le (by positivity) (hμ k).le t).trans ?_
    have := Real.abs_exp_sub_one_le (x := (1 / 2 : ℝ) ^ k)
      (by rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num))
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k)] at this
    exact (le_abs_self _).trans this
  have hcauchy (n : ℕ) (t : I) : CauchySeq fun m ↦ compSeq μ n m t := by
    refine cauchySeq_of_le_geometric_two (C := 4 * (1 / 2 : ℝ) ^ n) fun m ↦ ?_
    rw [dist_comm, compSeq_succ_apply']
    refine (hμd (n + m) _).trans (le_of_eq ?_)
    rw [pow_add, one_div_pow (2 : ℝ) m]
    ring
  choose L hL using fun n t ↦ cauchySeq_tendsto_of_complete (hcauchy n t)
  have hLrec (n : ℕ) (t : I) : L n t = L (n + 1) (μ n t) :=
    tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).2 (hL n t)) (hL (n + 1) (μ n t))
  have hLb (n : ℕ) (s t : I) (hst : s ≤ t) :
      Real.exp (-(2 * (1 / 2 : ℝ) ^ n)) * ((t : ℝ) - s) ≤ (L n t : ℝ) - L n s ∧
        (L n t : ℝ) - L n s ≤ Real.exp (2 * (1 / 2 : ℝ) ^ n) * ((t : ℝ) - s) := by
    have hc (v : I) : Tendsto (fun m ↦ (compSeq μ n m v : ℝ)) atTop (𝓝 (L n v : ℝ)) :=
      (continuous_subtype_val.tendsto _).comp (hL n v)
    have hd := (hc t).sub (hc s)
    exact ⟨ge_of_tendsto hd (Eventually.of_forall fun m ↦ (hPb n m s t hst).1),
      le_of_tendsto hd (Eventually.of_forall fun m ↦ (hPb n m s t hst).2)⟩
  have hL0 (n : ℕ) : L n 0 = 0 := tendsto_nhds_unique (hL n 0)
    (tendsto_const_nhds.congr fun m ↦ ((compSeq μ n m).map_bot).symm)
  have hL1 (n : ℕ) : L n 1 = 1 := tendsto_nhds_unique (hL n 1)
    (tendsto_const_nhds.congr fun m ↦ ((compSeq μ n m).map_top).symm)
  choose lam hlam using fun n ↦ exists_orderIso_of_slope (hL0 n) (hL1 n) (hLb n)
  have hlamn (n : ℕ) : logSlopeNorm (lam n) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) :=
    (logSlopeNorm_le_ofReal_iff (by positivity)).2 fun s t hst ↦ by
      rw [hlam, hlam]; exact hLb n s t hst
  have hlamrec (n : ℕ) (t : I) : lam (n + 1) (μ n t) = lam n t := by
    rw [hlam, hlam, hLrec n t]
  -- The functions `u n ∘ (λ n)⁻¹` converge uniformly.
  set yy : ℕ → I → E := fun n s ↦ u n ((lam n).symm s)
  have hyy (n : ℕ) (s : I) : edist (yy n s) (yy (n + 1) s) ≤ 1 / 2 ^ n := by
    have : (lam (n + 1)).symm s = μ n ((lam n).symm s) := by
      rw [OrderIso.symm_apply_eq, hlamrec, OrderIso.apply_symm_apply]
    simp only [yy]
    rw [this, ← ofReal_half_pow]
    exact (hμxy n _).le
  choose Y hY using fun s ↦ cauchySeq_tendsto_of_complete
    (cauchySeq_of_edist_le_geometric_two 1 ENNReal.one_ne_top (hyy · s))
  have hYb (n : ℕ) (s : I) : edist (yy n s) (Y s) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := by
    refine (edist_le_of_edist_le_geometric_two_of_tendsto 1 (hyy · s) (hY s) n).trans_eq ?_
    rw [ENNReal.ofReal_mul (by norm_num), ofReal_half_pow, ENNReal.ofReal_ofNat, mul_one,
      mul_one_div]
  have hunif : TendstoUniformly yy Y atTop :=
    EMetric.tendstoUniformly_iff.2 fun ε hε ↦
      (tendsto_ofReal_two_mul_half_pow.eventually (gt_mem_nhds hε)).mono fun n hn s ↦ by
        rw [edist_comm]; exact (hYb n s).trans_lt hn
  have hYc : IsCadlag Y :=
    IsCadlag.of_tendstoUniformly (fun n ↦ (isCadlag (u n)).comp_orderIso (lam n).symm) hunif
  refine ⟨toBillingsley ⟨Y, hYc⟩, EMetric.tendsto_nhds.2 fun ε hε ↦ ?_⟩
  filter_upwards [tendsto_ofReal_two_mul_half_pow.eventually (gt_mem_nhds hε)] with n hn
  rw [edist_def]
  refine lt_of_le_of_lt (billingsleyEDist_le_of_forall (lam n) (hlamn n) fun t ↦ ?_) hn
  have : u n t = yy n (lam n t) := by simp [yy]
  rw [this]
  exact hYb n _

end Billingsley

/-- **Billingsley, Theorem 12.1.** The identity map from the Skorokhod space with the `J₁`
metric to the Skorokhod space with Billingsley's metric `d°` is a homeomorphism: the two metrics
are topologically equivalent. -/
noncomputable def homeomorphBillingsley [PseudoEMetricSpace E] :
    SkorokhodSpace E ≃ₜ Billingsley E where
  toEquiv := toBillingsley
  continuous_toFun := EMetric.continuous_iff.2 fun x ε hε ↦ by
    obtain ⟨δ, hδ, h⟩ := x.isCadlag.exists_billingsleyEDist_lt hε
    refine ⟨δ, hδ, fun y hy ↦ ?_⟩
    rw [Billingsley.edist_def, billingsleyEDist_comm]
    exact h y (by rw [skorokhodEDist_comm]; exact hy)
  continuous_invFun := EMetric.continuous_iff.2 fun x ε hε ↦ by
    obtain ⟨r, hr, hrε⟩ := exists_ofReal_exp_sub_one_lt hε
    exact ⟨ENNReal.ofReal r, ENNReal.ofReal_pos.2 hr,
      fun y hy ↦ (skorokhodEDist_le_of_billingsleyEDist_lt hr.le hy).trans_lt hrε⟩

@[simp]
lemma coe_homeomorphBillingsley [PseudoEMetricSpace E] :
    ⇑(homeomorphBillingsley : SkorokhodSpace E ≃ₜ Billingsley E) = toBillingsley := rfl

/-- The Skorokhod space `D([0, 1], E)` with the `J₁` topology is completely metrizable when
`E` is a complete (extended) metric space: Billingsley's metric `d°` is a compatible complete
metric. -/
instance instIsCompletelyMetrizableSpace [EMetricSpace E] [CompleteSpace E] :
    IsCompletelyMetrizableSpace (SkorokhodSpace E) :=
  homeomorphBillingsley.isClosedEmbedding.IsCompletelyMetrizableSpace

/-- **Billingsley, Theorem 12.2.** The Skorokhod space `D([0, 1], E)` with the `J₁` topology is
a Polish space when `E` is a complete separable (extended) metric space. -/
instance instPolishSpace [EMetricSpace E] [CompleteSpace E] [SeparableSpace E] :
    PolishSpace (SkorokhodSpace E) :=
  inferInstance

end SkorokhodSpace

example : PolishSpace (SkorokhodSpace ℝ) := inferInstance
