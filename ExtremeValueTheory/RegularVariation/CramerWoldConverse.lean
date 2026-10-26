/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.CramerWoldConverse.WeightedLaw

/-!
# The converse Cramér–Wold device for non-integer indices

We prove Theorem 1.1 (i) of Basrak, Davis and Mikosch, *A characterization of multivariate
regular variation*, Ann. Appl. Probab. 12 (2002) [BDM02]: let `X` be a random vector in a
finite-dimensional real normed space `E` and `V` regularly varying with index `-α`, where `α > 0`
is **not an integer**. If `P(L X > x) / V(x) → w(L)` for every continuous linear functional `L`,
and `w` is not identically zero, then `X` is multivariate regularly varying with index `α`
(`isRegVarVector_of_tendsto_linear`, in the `IsRegVarVector` sense of
`RegularVariation/Multivariate.lean`). For integer `α` this fails in general (Hult and Lindskog,
Bernoulli 12 (2006) [HL06b]).

## The argument

Write `ν_x = P(X / x ∈ ·) / V(x)` (`scaledLaw`). We first replace `V` by the antitone function
`P(L₀ X > x)` with `w(L₀) ≠ 0` (it is regularly varying by `IsRegularlyVarying.of_tendsto_div`).

1. *Tail bounds.* Finitely many linear functionals dominate the norm
   (`exists_linear_family_norm`), so together with the Potter bounds for `V`,
   `ν_x {‖y‖ > t} ≤ K max (t ^ (-α / 2), t ^ (-3 α / 2))` whenever `x ≥ x₁` and `x t ≥ x₁`
   (`exists_tail_bound`).
2. *Compactness.* The weighted laws `min (1, ‖y‖) ^ (2 α) ν_x (dy)` (`weightedLaw`) have masses
   bounded above (`exists_weightedLaw_univ_le`, a Karamata-type estimate by the layer-cake
   formula) and below (`exists_le_weightedLaw_univ`) and are uniformly tight. By Prokhorov's
   theorem (`isCompact_closure_of_isTightMeasureSet`) every sequence `x_n → ∞` has a subsequence
   along which they converge weakly; dividing by the weight gives a measure `μ` on `E \ {0}` with
   `∫ f dν_{x_n} → ∫ f dμ` for bounded continuous `f` vanishing near the origin
   (`exists_subseq_tendsto`).
3. *Identification of limit points.* Every such limit point satisfies
   `μ {‖y‖ > t} ≤ W t ^ (-α)` (`exists_limit_tail_le`) and `μ {L > s} = w(L) s ^ (-α)`
   (`limit_halfSpace`, by the portmanteau theorem at all but countably many levels and
   monotonicity). By the uniqueness theorem `ext_of_halfSpace_of_tail` (which needs `α ∉ ℤ`) all
   limit points coincide, so `ν_x → μ` along `x → ∞` (`tendsto_of_subseq_tendsto`).
4. *Conclusion.* The same uniqueness theorem shows that `μ` is homogeneous of order `-α`, so
   spheres are `μ`-null (`measure_norm_eq_zero_of_map_smul`), `P(‖X‖ > x) / V(x) → κ =
   μ {‖y‖ > 1} > 0`, `P(‖X‖ > x)` is regularly varying, and `X` is regularly varying with exponent
   measure `κ⁻¹ μ` (`isRegVarVector_of_tendsto_linear_of_antitone`, which also records
   `κ⁻¹ μ {L > 1} = w(L) / κ`).

## File layout

* `ExtremeValueTheory.RegularVariation.CramerWoldConverse.WeightedLaw`: `scaledLaw`, the tail
  bounds and the weighted laws (step 1, mass bounds of step 2).
* this file: compactness, identification of limit points and the conclusion (steps 2–4).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal NNReal

namespace ExtremeValueTheory

namespace CramerWold

section Converse

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Ω → E}

/-- **Existence of limit points** (compactness): along every sequence `u n → ∞` there is a
subsequence along which the normalized laws `P(X / x ∈ ·) / V(x)` converge on sets bounded away
from the origin to a measure `μ` with no atom at the origin and finite away from it. The proof
applies Prokhorov's theorem to the normalized weighted laws
`min (1, ‖y‖) ^ (2 α) P(X / x ∈ dy) / V(x)`. -/
theorem exists_subseq_tendsto [IsProbabilityMeasure P] [FiniteDimensional ℝ E]
    (hX : Measurable X) {α : ℝ} {V : ℝ → ℝ}
    (hα : 0 < α) (hVa : Antitone V) (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    {L₀ : StrongDual ℝ E} (hL₀ : w L₀ ≠ 0) {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) :
    ∃ (φ : ℕ → ℕ) (μ : Measure E), StrictMono φ ∧ μ {0} = 0 ∧
      (∀ r > 0, μ {y | r < ‖y‖} < ∞) ∧
      ∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u (φ n))) atTop (𝓝 (∫ y, f y ∂μ)) := by
  obtain ⟨C, hC, x₂, hx₂, hmass⟩ := exists_weightedLaw_univ_le hX hα hVa hV hw
  obtain ⟨c, hc, hlow⟩ := exists_le_weightedLaw_univ (α := α) hX hV hw hL₀
  obtain ⟨x₁, K, hx₁, hK, hVpos, -, hT⟩ := exists_tail_bound (X := X) hα hVa hV hw
  obtain ⟨x₃, hx₃⟩ := eventually_atTop.1 hlow
  set x₀ := max (max x₁ x₂) x₃
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually_ge_atTop x₀)
  set v : ℕ → ℝ := fun n => u (n + N)
  have hv : ∀ n, x₀ ≤ v n := fun n => hN _ (Nat.le_add_left N n)
  have hv1 : ∀ n, x₁ ≤ v n := fun n => (le_max_left _ _).trans ((le_max_left _ _).trans (hv n))
  have hv2 : ∀ n, x₂ ≤ v n := fun n => (le_max_right _ _).trans ((le_max_left _ _).trans (hv n))
  have hv3 : ∀ n, x₃ ≤ v n := fun n => (le_max_right _ _).trans (hv n)
  have hv0 : ∀ n, 0 < v n := fun n => hx₁.trans_le (hv1 n)
  have hfin := fun n => isFiniteMeasure_weightedLaw (P := P) (X := X) hα V (v n)
  let π : ℕ → FiniteMeasure E := fun n => ⟨weightedLaw P X α V (v n), hfin n⟩
  have hπ : ∀ n, ((π n : FiniteMeasure E) : Measure E) = weightedLaw P X α V (v n) :=
    fun n => rfl
  set Cn : ℝ≥0 := C.toNNReal
  set cn : ℝ≥0 := c.toNNReal
  have hcn : 0 < cn := Real.toNNReal_pos.2 hc
  have hmass_le : ∀ n, (π n).mass ≤ Cn := fun n => by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, hπ, ENNReal.coe_toNNReal hC]
    exact hmass _ (hv2 n)
  have hmass_ge : ∀ n, cn ≤ (π n).mass := fun n => by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass, hπ]
    exact hx₃ _ (hv3 n)
  have hne : ∀ n, π n ≠ 0 := fun n =>
    (FiniteMeasure.mass_nonzero_iff _).1 (hcn.trans_le (hmass_ge n)).ne'
  let Q : ℕ → ProbabilityMeasure E := fun n => (π n).normalize
  -- tightness of the normalized weighted laws
  have hQle : ∀ n (R : ℝ), 1 ≤ R → ((Q n : ProbabilityMeasure E) : Measure E) {y | R < ‖y‖} ≤
      (cn : ℝ≥0∞)⁻¹ * ENNReal.ofReal (K * R ^ (-α + α / 2)) := fun n R hR => by
    rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (hne n), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul,
      ENNReal.coe_inv (FiniteMeasure.mass_nonzero_iff _ |>.2 (hne n)), hπ]
    gcongr
    · exact hmass_ge n
    · refine (weightedLaw_le hα V _ _).trans ?_
      have h := scaledLaw_norm_lt_le hX hVpos hT (hv1 n) (hv0 n) (one_pos.trans_le hR)
        ((hv1 n).trans (le_mul_of_one_le_right (hv0 n).le hR))
      rwa [max_rpow_eq_of_one_le hα hR] at h
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ range Q} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    have hlim : Tendsto (fun R : ℝ => (cn : ℝ≥0∞)⁻¹ * ENNReal.ofReal (K * R ^ (-α + α / 2)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => K * R ^ (-α + α / 2)) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (show 0 < α - α / 2 by linarith)).const_mul K
          |>.congr' (by
            filter_upwards [eventually_gt_atTop 0] with R hR
            congr 1; ring_nf)
      have h2 := ENNReal.Tendsto.const_mul (a := (cn : ℝ≥0∞)⁻¹) (ENNReal.tendsto_ofReal h1)
        (Or.inr (ENNReal.inv_ne_top.2 (by exact_mod_cast hcn.ne')))
      simpa [ENNReal.ofReal_zero] using h2
    obtain ⟨R, hR⟩ := eventually_atTop.1 ((hlim.eventually (gt_mem_nhds hε)).and
      (eventually_ge_atTop 1))
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
    rintro _ ⟨μ, ⟨n, rfl⟩, rfl⟩
    have hcompl : (Metric.closedBall (0 : E) R)ᶜ = {y | R < ‖y‖} := by
      ext y; simp
    rw [hcompl]
    exact (hQle n R (hR R le_rfl).2).trans (hR R le_rfl).1.le
  have hcomp : IsCompact (Icc cn Cn ×ˢ closure (range Q)) :=
    isCompact_Icc.prod (isCompact_closure_of_isTightMeasureSet htight)
  have hmem : ∀ n, ((π n).mass, Q n) ∈ Icc cn Cn ×ˢ closure (range Q) := fun n =>
    ⟨⟨hmass_ge n, hmass_le n⟩, subset_closure ⟨n, rfl⟩⟩
  obtain ⟨⟨m, Qlim⟩, hmQ, ψ, hψ, hlim⟩ := hcomp.tendsto_subseq hmem
  have hm_lim : Tendsto (fun n => (π (ψ n)).mass) atTop (𝓝 m) :=
    ((continuous_fst.tendsto _).comp hlim)
  have hQ_lim : Tendsto (fun n => Q (ψ n)) atTop (𝓝 Qlim) :=
    ((continuous_snd.tendsto _).comp hlim)
  set ρ : Measure E := m • (Qlim : Measure E)
  set μ : Measure E :=
    (ρ.restrict {0}ᶜ).withDensity fun y => ENNReal.ofReal (weight α y)⁻¹
  refine ⟨fun n => ψ n + N, μ, hψ.add_const N, ?_, ?_, ?_⟩
  · rw [withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_restrict
      (measurableSet_singleton 0), inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]
  · intro r hr
    have hm : MeasurableSet {y : E | r < ‖y‖} :=
      measurableSet_lt measurable_const continuous_norm.measurable
    rw [withDensity_apply _ hm]
    have hb : ∀ y ∈ {y : E | r < ‖y‖},
        ENNReal.ofReal (weight α y)⁻¹ ≤ ENNReal.ofReal ((min 1 r ^ (2 * α))⁻¹) := fun y hy => by
      refine ENNReal.ofReal_le_ofReal (inv_anti₀ (Real.rpow_pos_of_pos (lt_min one_pos hr) _) ?_)
      exact Real.rpow_le_rpow (lt_min one_pos hr).le (min_le_min le_rfl (le_of_lt hy))
        (by positivity)
    calc ∫⁻ y in {y | r < ‖y‖}, ENNReal.ofReal (weight α y)⁻¹ ∂ρ.restrict {0}ᶜ
        ≤ ∫⁻ _ in {y | r < ‖y‖}, ENNReal.ofReal ((min 1 r ^ (2 * α))⁻¹) ∂ρ.restrict {0}ᶜ :=
          setLIntegral_mono measurable_const hb
      _ < ∞ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  · intro f hf
    obtain ⟨h, hwh, hhw, h0⟩ := exists_bcf_div_weight hα f hf
    have hseq : ∀ n, ∫ y, f y ∂scaledLaw P X V (u (ψ n + N)) =
        (π (ψ n)).mass * ∫ y, h y ∂(Q (ψ n) : Measure E) := fun n => by
      have e1 : ∫ y, f y ∂scaledLaw P X V (u (ψ n + N)) =
          ∫ y, h y ∂(π (ψ n) : Measure E) := by
        rw [hπ, integral_weightedLaw]
        simp_rw [hwh]
        rfl
      rw [e1]
      conv_lhs => rw [FiniteMeasure.self_eq_mass_smul_normalize (π (ψ n))]
      rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure, NNReal.smul_def,
        smul_eq_mul]
      rfl
    have hlimit : ∫ y, f y ∂μ = m * ∫ y, h y ∂(Qlim : Measure E) := by
      have hmeas : Measurable fun y : E => ((weight α y)⁻¹).toNNReal :=
        ((continuous_weight hα).measurable.inv).real_toNNReal
      rw [show μ = (ρ.restrict {0}ᶜ).withDensity
          (fun y => (((weight α y)⁻¹).toNNReal : ℝ≥0∞)) from rfl,
        integral_withDensity_eq_integral_smul hmeas]
      have e2 : ∫ y in {0}ᶜ, ((weight α y)⁻¹).toNNReal • f y ∂ρ = ∫ y in {0}ᶜ, h y ∂ρ := by
        refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun y hy => ?_
        rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 (weight_nonneg α y)), smul_eq_mul,
          hhw y hy]
      rw [e2, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        simp only [mem_compl_iff, mem_singleton_iff, not_not] at hy
        rw [hy, h0]]
      rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    rw [hlimit]
    refine (((NNReal.continuous_coe.tendsto _).comp hm_lim).mul ?_).congr fun n => (hseq n).symm
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hQ_lim) h

theorem scaledLaw_real_norm_lt (hX : Measurable X) [IsFiniteMeasure P] {V : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hV : 0 ≤ V x) (t : ℝ) :
    (scaledLaw P X V x).real {y | t < ‖y‖} = (V x)⁻¹ * P.real {ω | x * t < ‖X ω‖} := by
  rw [measureReal_def, scaledLaw_norm_lt hX V hx, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 hV)]
  rfl

theorem scaledLaw_real_linear_lt (hX : Measurable X) [IsFiniteMeasure P] {V : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hV : 0 ≤ V x) (L : StrongDual ℝ E) (t : ℝ) :
    (scaledLaw P X V x).real {y | t < L y} = (V x)⁻¹ * P.real {ω | x * t < L (X ω)} := by
  rw [measureReal_def, scaledLaw_linear_lt hX V hx, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.2 hV)]
  rfl

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem vanishesNearZero_normCutoffBCF {t : ℝ} (ht : 0 < t) :
    VanishesNearZero (⇑(normCutoffBCF t : E →ᵇ ℝ)) :=
  ⟨t / 2, half_pos ht, fun y hy => by
    simp [normCutoff_eq_zero ht hy.le]⟩

omit [NormedSpace ℝ E] in
theorem integral_normCutoffBCF_le (ν : Measure E) [IsFiniteMeasure ν] {t : ℝ} (ht : 0 < t) :
    ∫ y, normCutoffBCF t y ∂ν ≤ ν.real {y | t / 2 < ‖y‖} := by
  have hm : MeasurableSet {y : E | t / 2 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_indicator_one hm]
  refine integral_mono ((normCutoffBCF t).integrable ν) ((integrable_const 1).indicator hm)
    fun y => ?_
  by_cases hy : t / 2 < ‖y‖
  · rw [indicator_of_mem (show y ∈ {y : E | t / 2 < ‖y‖} from hy), Pi.one_apply,
      normCutoffBCF_apply]
    exact_mod_cast normCutoff_le_one t y
  · rw [indicator_of_notMem (show y ∉ {y : E | t / 2 < ‖y‖} from hy), normCutoffBCF_apply,
      normCutoff_eq_zero ht (not_lt.1 hy)]
    simp

omit [NormedSpace ℝ E] in
/-- `μ {‖y‖ > t} ≤ ∫ normCutoff_t dμ` for a measure finite away from the origin. -/
theorem measure_lt_norm_le_integral_normCutoff {μ : Measure E}
    (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞) {t : ℝ} (ht : 0 < t) :
    μ {y | t < ‖y‖} ≤ ENNReal.ofReal (∫ y, normCutoffBCF t y ∂μ) := by
  have hm : MeasurableSet {y : E | t / 2 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hint : Integrable (fun y => normCutoffBCF t y) μ := by
    have hsupp : Function.support (fun y => normCutoffBCF t y) ⊆ {y : E | t / 2 < ‖y‖} :=
      fun y hy => by
        by_contra h'
        exact hy (by simp [normCutoff_eq_zero ht (not_lt.1 h')])
    exact (integrableOn_iff_integrable_of_support_subset hsupp).1
      (Measure.integrableOn_of_bounded (hμ _ (half_pos ht)).ne
        (normCutoffBCF t).continuous.aestronglyMeasurable (M := ‖normCutoffBCF t‖)
        (ae_of_all _ fun y => (normCutoffBCF t).norm_coe_le_norm y))
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => by
    simp only [normCutoffBCF_apply, Pi.zero_apply]; exact NNReal.coe_nonneg _)]
  rw [← lintegral_indicator_one (measurableSet_lt measurable_const continuous_norm.measurable)]
  refine lintegral_mono fun y => ?_
  by_cases hy : t < ‖y‖
  · rw [indicator_of_mem (show y ∈ {y : E | t < ‖y‖} from hy), Pi.one_apply,
      normCutoffBCF_apply, normCutoff_eq_one ht hy.le]
    simp
  · rw [indicator_of_notMem (show y ∉ {y : E | t < ‖y‖} from hy)]
    exact bot_le

/-- **Tail bound for limit points**: a limit point `μ` of the normalized laws satisfies
`μ {‖y‖ > t} ≤ W t ^ (-α)` for a finite constant `W` independent of the sequence. -/
theorem exists_limit_tail_le [IsProbabilityMeasure P] [FiniteDimensional ℝ E]
    (hX : Measurable X) {α : ℝ} {V : ℝ → ℝ} (hV : IsRegularlyVarying V (-α))
    {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L))) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ {u : ℕ → ℝ}, Tendsto u atTop atTop → ∀ {μ : Measure E},
      (∀ r > 0, μ {y | r < ‖y‖} < ∞) →
      (∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u n)) atTop (𝓝 (∫ y, f y ∂μ))) →
      ∀ t > 0, μ {y | t < ‖y‖} ≤ ENNReal.ofReal (t ^ (-α)) * W := by
  obtain ⟨ι, _, lf, hlf⟩ := exists_linear_family_norm (E := E)
  set S : ℝ := ∑ i, w (lf i)
  refine ⟨ENNReal.ofReal ((2 : ℝ) ^ α * S), ENNReal.ofReal_ne_top,
    fun {u} hu {μ} hμ hconv t ht => ?_⟩
  have ht2 : 0 < t / 2 := half_pos ht
  have hlim := hconv _ (vanishesNearZero_normCutoffBCF ht)
  have hR : Tendsto (fun n => ∑ i, P.real {ω | u n * (t / 2) < lf i (X ω)} / V (u n)) atTop
      (𝓝 (∑ i, w (lf i) * (t / 2) ^ (-α))) :=
    tendsto_finsetSum _ fun i _ => (tendsto_linear_mul hV hw (lf i) ht2).comp hu
  have hle : ∀ᶠ n in atTop, ∫ y, normCutoffBCF t y ∂scaledLaw P X V (u n) ≤
      ∑ i, P.real {ω | u n * (t / 2) < lf i (X ω)} / V (u n) := by
    filter_upwards [hu.eventually hV.eventually_pos, hu.eventually_gt_atTop 0] with n hVn hun
    refine (integral_normCutoffBCF_le _ ht).trans ?_
    rw [scaledLaw_real_norm_lt hX hun hVn.le, ← Finset.sum_div, inv_mul_eq_div]
    gcongr
    have hsub : {ω | u n * (t / 2) < ‖X ω‖} ⊆ ⋃ i, {ω | u n * (t / 2) < lf i (X ω)} :=
      fun ω hω => by
        obtain ⟨i, hi⟩ := hlf (X ω) _ (mul_pos hun ht2).le hω
        exact mem_iUnion.2 ⟨i, hi⟩
    exact (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)
  have hint_le := le_of_tendsto_of_tendsto hlim hR hle
  refine (measure_lt_norm_le_integral_normCutoff hμ ht).trans ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  refine ENNReal.ofReal_le_ofReal (hint_le.trans_eq ?_)
  rw [← Finset.sum_mul, Real.div_rpow ht.le zero_le_two, Real.rpow_neg zero_le_two,
    Real.rpow_neg ht.le]
  simp only [S]
  field_simp

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_halfSpace_subset_norm (L : StrongDual ℝ E) {t : ℝ} (ht : 0 < t) :
    ∃ r > 0, {y : E | t < L y} ⊆ {y | r < ‖y‖} :=
  ⟨(‖t⁻¹ • L‖ + 1)⁻¹, by positivity, by
    rw [setOf_lt_apply_eq ht L]; exact setOf_one_lt_apply_subset _⟩

/-- **Half-spaces for limit points**: a limit point `μ` of the normalized laws satisfies
`μ {L > s} = w (L) s ^ (-α)` for every continuous linear functional `L` and every `s > 0`. -/
theorem limit_halfSpace [IsProbabilityMeasure P] (hX : Measurable X) {α : ℝ} {V : ℝ → ℝ}
    (hα : 0 < α) (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {μ : Measure E}
    (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞)
    (hconv : ∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u n)) atTop (𝓝 (∫ y, f y ∂μ)))
    (L : StrongDual ℝ E) {s : ℝ} (hs : 0 < s) :
    μ {y | s < L y} = ENNReal.ofReal (w L * s ^ (-α)) := by
  have hfinL : ∀ t > 0, μ {y | t < L y} ≠ ∞ := fun t ht => by
    obtain ⟨r, hr, hsub⟩ := exists_halfSpace_subset_norm L ht
    exact ((measure_mono hsub).trans_lt (hμ r hr)).ne
  -- good levels
  have hgood : ∀ t > 0, μ {y | L y = t} = 0 → μ {y | t < L y} = ENNReal.ofReal (w L * t ^ (-α)) :=
    fun t ht hnull => by
      obtain ⟨r, hr, hsub⟩ := exists_halfSpace_subset_norm L ht
      have hAm : MeasurableSet {y : E | t < L y} := measurableSet_lt measurable_const L.measurable
      have hfr : μ (frontier {y : E | t < L y}) = 0 :=
        measure_mono_null ((frontier_lt_subset_eq continuous_const L.continuous).trans
          fun y (hy : t = L y) => (show L y = t from hy.symm)) hnull
      have key := tendsto_measureReal_of_vanishesNearZero (μs := fun n => scaledLaw P X V (u n))
        (fun n => inferInstance) hμ hconv hAm hr (fun y hy => (show r < ‖y‖ from hsub hy).le) hfr
      have hlim : Tendsto (fun n => (scaledLaw P X V (u n)).real {y | t < L y}) atTop
          (𝓝 (w L * t ^ (-α))) := by
        refine ((tendsto_linear_mul hV hw L ht).comp hu).congr' ?_
        filter_upwards [hu.eventually hV.eventually_pos, hu.eventually_gt_atTop 0] with n hVn hun
        rw [scaledLaw_real_linear_lt hX hun hVn.le, Function.comp_apply, inv_mul_eq_div]
      have hreal := tendsto_nhds_unique key hlim
      rw [← ofReal_measureReal (hfinL t ht), hreal]
  -- the countable set of bad levels above `s / 2`
  set ρ := μ.restrict {y | s / 2 < L y}
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.2 (hfinL _ (half_pos hs))
  have hcount := Measure.countable_meas_level_set_pos (μ := ρ) L.measurable
  have hnull : ∀ t, s / 2 < t → t ∉ {t : ℝ | 0 < ρ {y | L y = t}} → μ {y | L y = t} = 0 :=
    fun t ht hN => by
      simp only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] at hN
      rw [Measure.restrict_apply (measurableSet_eq_fun L.measurable measurable_const)] at hN
      rwa [inter_eq_left.2 (show {x : E | L x = t} ⊆ {y | s / 2 < L y} from
        fun y (hy : L y = t) => (show s / 2 < L y by rw [hy]; exact ht))] at hN
  have hdense := hcount.dense_compl ℝ
  have hex : ∀ k : ℕ, ∃ t ∈ {t : ℝ | 0 < ρ {y | L y = t}}ᶜ,
      t ∈ Ioo s (s + 1 / ((k : ℝ) + 1)) := fun k =>
    hdense.exists_between (lt_add_of_pos_right s (by positivity))
  choose t htN ht using hex
  have ht_pos : ∀ k, 0 < t k := fun k => hs.trans (ht k).1
  have hval : ∀ k, μ {y | t k < L y} = ENNReal.ofReal (w L * t k ^ (-α)) := fun k =>
    hgood _ (ht_pos k) (hnull _ (by linarith [(ht k).1]) (htN k))
  have hwL : 0 ≤ w L := limit_nonneg hV hw L
  have ht_lim : Tendsto t atTop (𝓝 s) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun k => (ht k).1.le) (fun k => (ht k).2.le)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add s
  have hval_lim : Tendsto (fun k => ENNReal.ofReal (w L * t k ^ (-α))) atTop
      (𝓝 (ENNReal.ofReal (w L * s ^ (-α)))) :=
    ENNReal.tendsto_ofReal (((Real.continuousAt_rpow_const _ _ (Or.inl hs.ne')).tendsto.comp
      ht_lim).const_mul _)
  refine le_antisymm ?_ ?_
  · -- upper bound by continuity from below
    have hU : {y : E | s < L y} = ⋃ k : ℕ, {y | s + 1 / ((k : ℝ) + 1) < L y} := by
      ext y
      simp only [mem_ofPred_eq, mem_iUnion]
      refine ⟨fun hy => ?_, fun ⟨k, hk⟩ => lt_trans (by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith) hk⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨k, by linarith⟩
    have hmono : Monotone fun k : ℕ => {y : E | s + 1 / ((k : ℝ) + 1) < L y} := by
      intro i j hij y hy
      simp only [mem_ofPred_eq] at hy ⊢
      refine lt_of_le_of_lt ?_ hy
      gcongr
    rw [hU]
    refine le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) fun k => ?_
    calc μ {y | s + 1 / ((k : ℝ) + 1) < L y} ≤ μ {y | t k < L y} :=
          measure_mono fun y (hy : _ < _) => lt_trans (ht k).2 hy
      _ = ENNReal.ofReal (w L * t k ^ (-α)) := hval k
      _ ≤ ENNReal.ofReal (w L * s ^ (-α)) := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs (ht k).1.le
            (by linarith)) hwL)
  · refine le_of_tendsto' hval_lim fun k => ?_
    rw [← hval k]
    exact measure_mono fun y (hy : _ < _) => lt_trans (ht k).1 hy

/-- Spheres are null for a measure homogeneous of order `-α` and finite away from the origin. -/
theorem measure_norm_eq_zero_of_map_smul {μ : Measure E} {α : ℝ}
    (hhom : ∀ t > 0, μ.map (fun y => t • y) = ENNReal.ofReal (t ^ α) • μ)
    (hμ : ∀ r > 0, μ {y | r < ‖y‖} < ∞) {c : ℝ} (hc : 0 < c) : μ {y | ‖y‖ = c} = 0 := by
  have hr : 0 < c / 4 := by positivity
  have hfin : IsFiniteMeasure (μ.restrict {y | c / 4 < ‖y‖}) :=
    isFiniteMeasure_restrict.2 (hμ _ hr).ne
  have hcount := Measure.countable_meas_level_set_pos (μ := μ.restrict {y | c / 4 < ‖y‖})
    (continuous_norm.measurable (α := E))
  obtain ⟨t, ht, hct⟩ := (hcount.dense_compl ℝ).exists_between (show c / 2 < c by linarith)
  have ht0 : 0 < t := lt_trans (half_pos hc) hct.1
  have hνt : μ.restrict {y | c / 4 < ‖y‖} {y | ‖y‖ = t} = 0 := by
    simpa using ht
  have hμt : μ {y | ‖y‖ = t} = 0 := by
    rw [Measure.restrict_apply (measurableSet_eq_fun continuous_norm.measurable
      measurable_const)] at hνt
    rwa [inter_eq_left.2 (show {y : E | ‖y‖ = t} ⊆ {y | c / 4 < ‖y‖} from
      fun y (hy : ‖y‖ = t) => (show c / 4 < ‖y‖ by rw [hy]; linarith [hct.1]))] at hνt
  have hpre : {y : E | ‖y‖ = c} = (fun y => (t / c) • y) ⁻¹' {y | ‖y‖ = t} := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos ht0 hc)]
    rw [div_mul_eq_mul_div, div_eq_iff hc.ne']
    exact ⟨fun hy => by rw [hy], fun hy => mul_left_cancel₀ ht0.ne' hy⟩
  have := congrArg (fun ν : Measure E => ν {y | ‖y‖ = t}) (hhom _ (div_pos ht0 hc))
  simp only [Measure.map_apply (measurable_const_smul _)
    (measurableSet_eq_fun continuous_norm.measurable measurable_const), Measure.smul_apply,
    smul_eq_mul, hμt, mul_zero] at this
  rw [hpre, this]

/-- **The converse Cramér–Wold device for non-integer indices**, normalized form
([BDM02, Theorem 1.1 (i)]). Let `X` be a random vector in a finite-dimensional real normed space
and `V` an antitone function regularly varying with index `-α`, `α > 0` not an integer, such that
`P(L X > x) / V(x) → w(L)` for every continuous linear functional `L`, with `w(L₀) ≠ 0` for some
`L₀`. Then `X` is regularly varying with index `α`; moreover
`P(‖X‖ > x) / V(x) → κ > 0` and the exponent measure gives mass `w(L) / κ` to `{L > 1}`. -/
theorem isRegVarVector_of_tendsto_linear_of_antitone [IsProbabilityMeasure P]
    [FiniteDimensional ℝ E] (hX : Measurable X) {α : ℝ} (hα : 0 < α) (hαZ : ∀ k : ℤ, α ≠ k)
    {V : ℝ → ℝ} (hVa : Antitone V) (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    {L₀ : StrongDual ℝ E} (hL₀ : w L₀ ≠ 0) :
    ∃ (μ : Measure E) (κ : ℝ), 0 < κ ∧ IsRegVarVector P X α μ ∧
      Tendsto (fun x => P.real {ω | x < ‖X ω‖} / V x) atTop (𝓝 κ) ∧
      ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ENNReal.ofReal (w L / κ) := by
  obtain ⟨W, hW, htail⟩ := exists_limit_tail_le hX hV hw
  -- any two limit points coincide
  have huniq : ∀ {u u' : ℕ → ℝ}, Tendsto u atTop atTop → Tendsto u' atTop atTop →
      ∀ {μ μ' : Measure E}, μ {0} = 0 → μ' {0} = 0 →
      (∀ r > 0, μ {y | r < ‖y‖} < ∞) → (∀ r > 0, μ' {y | r < ‖y‖} < ∞) →
      (∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u n)) atTop (𝓝 (∫ y, f y ∂μ))) →
      (∀ f : E →ᵇ ℝ, VanishesNearZero f →
        Tendsto (fun n => ∫ y, f y ∂scaledLaw P X V (u' n)) atTop (𝓝 (∫ y, f y ∂μ'))) →
      μ = μ' := by
    intro u u' hu hu' μ μ' h0 h0' hfin hfin' hc hc'
    refine ext_of_halfSpace_of_tail hα hαZ hW hW (htail hu hfin hc) (htail hu' hfin' hc') h0 h0'
      fun L => ?_
    rw [limit_halfSpace hX hα hV hw hu hfin hc L one_pos,
      limit_halfSpace hX hα hV hw hu' hfin' hc' L one_pos]
  -- a limit point along `n ↦ n`
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨φ, μ, hφ, hμ0, hμfin, hμconv⟩ :=
    exists_subseq_tendsto hX hα hVa hV hw hL₀ hnat
  have hφu : Tendsto (fun n => ((φ n : ℕ) : ℝ)) atTop atTop := hnat.comp hφ.tendsto_atTop
  -- full convergence
  have hconv : ∀ f : E →ᵇ ℝ, VanishesNearZero f →
      Tendsto (fun x => ∫ y, f y ∂scaledLaw P X V x) atTop (𝓝 (∫ y, f y ∂μ)) := by
    intro f hf
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ψ, μ', hψ, hμ'0, hμ'fin, hμ'conv⟩ :=
      exists_subseq_tendsto hX hα hVa hV hw hL₀ hns
    have : μ' = μ := huniq (hns.comp hψ.tendsto_atTop) hφu hμ'0 hμ0 hμ'fin hμfin hμ'conv hμconv
    exact ⟨ψ, this ▸ hμ'conv f hf⟩
  have hμhalf : ∀ L : StrongDual ℝ E, ∀ s > 0, μ {y | s < L y} = ENNReal.ofReal (w L * s ^ (-α)) :=
    fun L s hs => limit_halfSpace hX hα hV hw hφu hμfin hμconv L hs
  have hμt := htail hφu hμfin hμconv
  -- homogeneity
  have hhom : ∀ t > 0, μ.map (fun y => t • y) = ENNReal.ofReal (t ^ α) • μ := by
    intro t ht
    have hsm : Measurable fun y : E => t • y := measurable_const_smul t
    have hpre : ∀ s : ℝ, (fun y : E => t • y) ⁻¹' {y | s < ‖y‖} = {y | s / t < ‖y‖} := fun s => by
      ext y
      simp only [mem_preimage, mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      rw [div_lt_iff₀ ht, mul_comm]
    refine ext_of_halfSpace_of_tail hα hαZ (C := ENNReal.ofReal (t ^ α) * W)
      (C' := ENNReal.ofReal (t ^ α) * W) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW) (fun s hs => ?_) (fun s hs => ?_) ?_ ?_
      fun L => ?_
    · rw [Measure.map_apply hsm (measurableSet_lt measurable_const continuous_norm.measurable),
        hpre]
      refine (hμt _ (div_pos hs ht)).trans_eq ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
      congr 2
      rw [Real.div_rpow hs.le ht.le, Real.rpow_neg ht.le, div_inv_eq_mul]
    · rw [Measure.smul_apply, smul_eq_mul, mul_comm (ENNReal.ofReal (s ^ (-α))), mul_assoc]
      exact mul_le_mul_right (by rw [mul_comm]; exact hμt s hs) _
    · rw [Measure.map_apply hsm (measurableSet_singleton 0)]
      convert hμ0 using 2
      ext y; simp [ht.ne']
    · rw [Measure.smul_apply, hμ0, smul_zero]
    · have hpre' : (fun y : E => t • y) ⁻¹' {y | 1 < L y} = {y | t⁻¹ < L y} := by
        ext y
        simp only [mem_preimage, mem_ofPred_eq, map_smul, smul_eq_mul]
        rw [inv_lt_iff_one_lt_mul₀' ht]
      rw [Measure.map_apply hsm (measurableSet_lt measurable_const L.measurable), hpre',
        hμhalf L _ (inv_pos.2 ht), Measure.smul_apply, smul_eq_mul,
        hμhalf L 1 one_pos, Real.one_rpow, mul_one, ← ENNReal.ofReal_mul
          (Real.rpow_nonneg ht.le _), Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv,
        mul_comm]
  -- the norm tail
  have hsphere : μ {y | ‖y‖ = 1} = 0 := measure_norm_eq_zero_of_map_smul hhom hμfin one_pos
  have hA : MeasurableSet {y : E | 1 < ‖y‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hfr : μ (frontier {y : E | 1 < ‖y‖}) = 0 :=
    measure_mono_null ((frontier_lt_subset_eq continuous_const continuous_norm).trans
      fun y (hy : 1 = ‖y‖) => (show ‖y‖ = 1 from hy.symm)) hsphere
  set κ := μ.real {y | 1 < ‖y‖}
  have hκlim : Tendsto (fun x => P.real {ω | x < ‖X ω‖} / V x) atTop (𝓝 κ) := by
    have key := tendsto_measureReal_of_vanishesNearZero (μs := fun x => scaledLaw P X V x)
      (fun x => inferInstance) hμfin hconv hA one_pos (fun y (hy : 1 < ‖y‖) => hy.le) hfr
    refine key.congr' ?_
    filter_upwards [hV.eventually_pos, eventually_gt_atTop 0] with x hVx hx
    rw [scaledLaw_real_norm_lt hX hx hVx.le, mul_one, inv_mul_eq_div]
  set a : ℝ := (‖L₀‖ + 1)⁻¹
  have ha : 0 < a := by positivity
  have hwL : 0 < w (a • L₀) := by
    rw [limit_smul hV hw L₀ ha]
    exact mul_pos (Real.rpow_pos_of_pos ha _)
      (lt_of_le_of_ne (limit_nonneg hV hw L₀) (Ne.symm hL₀))
  have hLn : ‖a • L₀‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, inv_mul_le_iff₀ (by positivity)]
    linarith
  have hsub : {y : E | 1 < (a • L₀) y} ⊆ {y | 1 < ‖y‖} := fun y (hy : 1 < (a • L₀) y) => by
    show 1 < ‖y‖
    calc 1 < (a • L₀) y := hy
      _ ≤ ‖a • L₀‖ * ‖y‖ := (le_abs_self _).trans (by simpa using (a • L₀).le_opNorm y)
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
      _ = ‖y‖ := one_mul _
  have hκ : 0 < κ := by
    have h1 : ENNReal.ofReal (w (a • L₀)) ≤ μ {y | 1 < ‖y‖} := by
      have := hμhalf (a • L₀) 1 one_pos
      rw [Real.one_rpow, mul_one] at this
      rw [← this]
      exact measure_mono hsub
    have h2 := ENNReal.toReal_mono (hμfin 1 one_pos).ne h1
    rw [ENNReal.toReal_ofReal hwL.le] at h2
    exact hwL.trans_le h2
  have hRV : IsRegularlyVarying (fun x => P.real {ω | x < ‖X ω‖}) (-α) :=
    IsRegularlyVarying.of_tendsto_div hV hκlim hκ
  refine ⟨ENNReal.ofReal κ⁻¹ • μ, κ, hκ, ⟨hRV, by rw [Measure.smul_apply, hμ0, smul_zero],
    fun r hr => by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμfin r hr), fun f hf => ?_⟩, hκlim,
    fun L => ?_⟩
  · rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hκ.le), smul_eq_mul]
    have hinv := hκlim.inv₀ hκ.ne'
    refine (hinv.mul (hconv f hf)).congr' ?_
    filter_upwards [hV.eventually_pos, hRV.eventually_pos] with x hVx hPx
    rw [integral_scaledLaw hX hVx.le f.continuous.measurable, inv_div]
    field_simp
  · rw [Measure.smul_apply, smul_eq_mul, hμhalf L 1 one_pos, Real.one_rpow, mul_one,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hκ.le), inv_mul_eq_div]

/-- **The converse Cramér–Wold device for non-integer indices** ([BDM02, Theorem 1.1 (i)];
[BL09]). Let `X` be a random vector in a finite-dimensional real normed space and suppose that
for some function `V` regularly varying with index `-α`, `α > 0` **not an integer**, the tails of
all linear combinations satisfy `P(L X > x) / V(x) → w(L)` for every continuous linear functional
`L`, with `w` not identically zero. Then `X` is multivariate regularly varying with index `α`.
For integer `α` the statement fails in general ([HL06b]). -/
theorem isRegVarVector_of_tendsto_linear [IsProbabilityMeasure P] [FiniteDimensional ℝ E]
    (hX : Measurable X) {α : ℝ} (hα : 0 < α) (hαZ : ∀ k : ℤ, α ≠ k)
    {V : ℝ → ℝ} (hV : IsRegularlyVarying V (-α)) {w : StrongDual ℝ E → ℝ}
    (hw : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V x) atTop (𝓝 (w L)))
    (hw0 : ∃ L, w L ≠ 0) : ∃ μ : Measure E, IsRegVarVector P X α μ := by
  obtain ⟨L₀, hL₀⟩ := hw0
  have hpos : 0 < w L₀ := lt_of_le_of_ne (limit_nonneg hV hw L₀) (Ne.symm hL₀)
  set V₀ : ℝ → ℝ := fun x => P.real {ω | x < L₀ (X ω)}
  have hV₀a : Antitone V₀ := fun x y hxy =>
    measureReal_mono fun ω (hω : y < L₀ (X ω)) => lt_of_le_of_lt hxy hω
  have hV₀ : IsRegularlyVarying V₀ (-α) := IsRegularlyVarying.of_tendsto_div hV (hw L₀) hpos
  have hw₀ : ∀ L : StrongDual ℝ E,
      Tendsto (fun x => P.real {ω | x < L (X ω)} / V₀ x) atTop (𝓝 (w L / w L₀)) := fun L => by
    refine ((hw L).div (hw L₀) hpos.ne').congr' ?_
    filter_upwards [hV.eventually_pos] with x hVx
    simp only [V₀, Pi.div_apply]
    rw [div_div_div_cancel_right₀ hVx.ne']
  obtain ⟨μ, -, -, hμ, -⟩ := isRegVarVector_of_tendsto_linear_of_antitone hX hα hαZ hV₀a hV₀ hw₀
    (L₀ := L₀) (by rw [div_self hpos.ne']; exact one_ne_zero)
  exact ⟨μ, hμ⟩

end Converse

end CramerWold

end ExtremeValueTheory
