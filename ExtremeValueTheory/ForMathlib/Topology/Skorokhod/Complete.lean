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

PLACEHOLDER
-/

@[expose] public section

open Filter Set Topology Metric unitInterval
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
