/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.EchoConditionA
import ExtremeValueTheory.Dependence.MDependent

/-!
# Strong mixing does not give `θ = ϑ`: anticlustering is an independent hypothesis

`HasSpectralTailProcess.hasExtremalIndex_of_isMDependent` proves `θ = ϑ` for stationary
`m`-dependent series. The natural generalization replaces `m`-dependence by strong mixing with a
rate. The block condition `𝒜(uₙ)` does follow from mixing (`conditionA_of_alphaMixing`), so the
general theorem holds **if anticlustering is kept as a hypothesis**
(`HasSpectralTailProcess.hasExtremalIndex_abs_of_alphaMixing`). We show that anticlustering
**cannot** be derived from mixing, even with a geometric rate: the logarithmic echo process is
strongly mixing with `α(h) ≤ C e^(-α h)`, regularly varying, stationary, with spectral tail process
`Θ_t = 1{t = 0}` (`ϑ = 1`), but its extremal index is `θ = 1/2`
(`logEcho_alphaMixing_theta_ne_vartheta`).

## The mixing bound

For the echo process `X_t = max(Z_t, max {Z_i : i < t, i + L(Z_i) = t})` and a lag `h ≥ 1`, the
past `σ(X_t : t ≤ s)` is contained in `σ(Z_i : i ≤ s)`. The future `σ(X_t : t ≥ s + h)` coincides,
on the event `G` that no innovation `Z_i`, `i ≤ s`, echoes at or after time `s + h`, with a
sub-σ-algebra of `σ(Z_i : i > s)`: every future event `B` agrees on `G` with some event `B'` of
`σ(Z_i : i > s)` (`exists_inter_echoGood_eq`, a good-sets argument). Independence of
`σ(Z_i : i ≤ s)` and `σ(Z_i : i > s)` then gives `|P(A ∩ B) - P(A) P(B)| ≤ 2 P(Gᶜ)` and
`P(Gᶜ) ≤ ∑_{m ≥ 0} P(L(Z) ≥ h + m)` (`alphaMixing_echoProcess_le`). For `L(z) = ⌊log z⌋₊ + 1` the
tail sum is geometric (`alphaMixing_logEchoProcess_le`).

This uses only measurability of `L`, independence and the common Pareto law of the innovations,
and summability of the tail of `L(Z)`; not `L ≥ 1` nor `L → ∞`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section EchoMixing

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {α : ℝ} {Z : ℤ → Ω → ℝ}
  {L : ℝ → ℕ}

/-- The innovations up to time `s`, replaced by `0` after `s`. -/
noncomputable def truncPast (Z : ℤ → Ω → ℝ) (s : ℤ) (i : ℤ) (ω : Ω) : ℝ :=
  if i ≤ s then Z i ω else 0

/-- The innovations after time `s`, replaced by `0` up to `s`. -/
noncomputable def truncFuture (Z : ℤ → Ω → ℝ) (s : ℤ) (i : ℤ) (ω : Ω) : ℝ :=
  if s < i then Z i ω else 0

/-- `σ(Z_i : i ≤ s)`. -/
@[instance_reducible]
def innovationPast (Z : ℤ → Ω → ℝ) (s : ℤ) : MeasurableSpace Ω :=
  ⨆ i ∈ {i : ℤ | i ≤ s}, MeasurableSpace.comap (Z i) inferInstance

/-- `σ(Z_i : i > s)`. -/
@[instance_reducible]
def innovationFuture (Z : ℤ → Ω → ℝ) (s : ℤ) : MeasurableSpace Ω :=
  ⨆ i ∈ {i : ℤ | s < i}, MeasurableSpace.comap (Z i) inferInstance

/-- The *good event*: no innovation at a time `s - m ≤ s` echoes at or after time `s + h`. -/
def echoGood (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (s : ℤ) (h : ℕ) : Set Ω :=
  {ω | ∀ m : ℕ, L (Z (s - m) ω) < h + m}

theorem measurable_truncPast (s i : ℤ) : Measurable[innovationPast Z s] (truncPast Z s i) := by
  by_cases h : i ≤ s
  · have : truncPast Z s i = Z i := funext fun ω => by simp [truncPast, h]
    rw [this]
    exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ {i : ℤ | i ≤ s}) =>
      MeasurableSpace.comap (Z i) inferInstance) i h)
  · have : truncPast Z s i = fun _ => 0 := funext fun ω => by simp [truncPast, h]
    rw [this]
    exact measurable_const

theorem measurable_truncFuture (s i : ℤ) :
    Measurable[innovationFuture Z s] (truncFuture Z s i) := by
  by_cases h : s < i
  · have : truncFuture Z s i = Z i := funext fun ω => by simp [truncFuture, h]
    rw [this]
    exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ {i : ℤ | s < i}) =>
      MeasurableSpace.comap (Z i) inferInstance) i h)
  · have : truncFuture Z s i = fun _ => 0 := funext fun ω => by simp [truncFuture, h]
    rw [this]
    exact measurable_const

/-- The echo process up to time `s` only reads the innovations up to time `s`. -/
theorem echoProcess_truncPast {s t : ℤ} (ht : t ≤ s) :
    echoProcess L (truncPast Z s) t = echoProcess L Z t := by
  funext ω
  have h1 : ∀ j : ℕ, t - (j + 1) ≤ s := fun j => by omega
  simp only [echoProcess, echoTerm, truncPast, ht, h1, ite_true]

/-- On the good event, the echo process after time `s + h` only reads the innovations after `s`. -/
theorem echoProcess_truncFuture {s : ℤ} {h : ℕ} (hh : 1 ≤ h) {t : ℤ} (ht : s + h ≤ t) {ω : Ω}
    (hω : ω ∈ echoGood L Z s h) :
    echoProcess L (truncFuture Z s) t ω = echoProcess L Z t ω := by
  have hst : s < t := by omega
  simp only [echoProcess, truncFuture, hst, ite_true]
  congr 1
  refine iSup_congr fun j => ?_
  simp only [echoTerm, truncFuture]
  by_cases hi : s < t - (j + 1)
  · simp only [hi, ite_true]
  · have hL : L (Z (t - (j + 1)) ω) ≠ j + 1 := by
      have := hω (s - (t - (j + 1))).toNat
      have e : s - (((s - (t - (j + 1))).toNat : ℕ) : ℤ) = t - (j + 1) := by omega
      rw [e] at this
      intro hc
      rw [hc] at this
      omega
    simp only [hi, ite_false, hL, ite_self]

/-- **Coupling of the future**: every event of the future `σ(X_t : t ≥ s + h)` of the echo process
agrees, on the good event, with an event of `σ(Z_i : i > s)`. -/
theorem exists_inter_echoGood_eq (hLm : Measurable L) {s h : ℕ} (hh : 1 ≤ h) {B : Set Ω}
    (hB : MeasurableSet[futureMeasurableSpace (fun k : ℕ => echoProcess L Z k) (s + h)] B) :
    ∃ B', MeasurableSet[innovationFuture Z s] B' ∧
      B ∩ echoGood L Z s h = B' ∩ echoGood L Z s h := by
  set G := echoGood L Z s h
  let m : MeasurableSpace Ω :=
    { MeasurableSet' := fun B => ∃ B', MeasurableSet[innovationFuture Z s] B' ∧ B ∩ G = B' ∩ G
      measurableSet_empty := ⟨∅, @MeasurableSet.empty _ (innovationFuture Z s), rfl⟩
      measurableSet_compl := fun B ⟨B', hB', e⟩ => by
        refine ⟨B'ᶜ, @MeasurableSet.compl _ _ (innovationFuture Z s) hB', ?_⟩
        ext ω
        simp only [mem_inter_iff, mem_compl_iff]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨fun h3 => h1 ?_, h2⟩
          have : ω ∈ B' ∩ G := ⟨h3, h2⟩
          rw [← e] at this
          exact this.1
        · rintro ⟨h1, h2⟩
          refine ⟨fun h3 => h1 ?_, h2⟩
          have : ω ∈ B ∩ G := ⟨h3, h2⟩
          rw [e] at this
          exact this.1
      measurableSet_iUnion := fun f hf => by
        choose g hg he using hf
        refine ⟨⋃ i, g i, @MeasurableSet.iUnion _ _ (innovationFuture Z s) _ _ hg, ?_⟩
        rw [iUnion_inter, iUnion_inter]
        exact iUnion_congr he }
  have hle : futureMeasurableSpace (fun k : ℕ => echoProcess L Z k) (s + h) ≤ m := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨S, hS, rfl⟩
    refine ⟨echoProcess L (truncFuture Z s) t ⁻¹' S,
      measurable_echoProcess (mΩ := innovationFuture Z s) (measurable_truncFuture s) hLm t hS, ?_⟩
    ext ω
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rwa [echoProcess_truncFuture hh (by omega) h2]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rwa [echoProcess_truncFuture hh (by omega) h2] at h1
  exact hle B hB

omit [MeasurableSpace Ω] in
theorem measureReal_le_of_inter_eq {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {A B G : Set Ω} (e : A ∩ G = B ∩ G) : μ.real A ≤ μ.real B + μ.real Gᶜ := by
  refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)).trans
    (measureReal_union_le B Gᶜ)
  by_cases hG : ω ∈ G
  · have : ω ∈ B ∩ G := e ▸ ⟨hω, hG⟩
    exact Or.inl this.1
  · exact Or.inr hG

variable [IsProbabilityMeasure P]

/-- The probability of the bad event: `P(Gᶜ) ≤ ∑_{m ≥ 0} P(L(Z) ≥ h + m)`. -/
theorem measureReal_compl_echoGood_le (hZ : ∀ t, Measurable (Z t))
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hLm : Measurable L) (s : ℤ) (h : ℕ)
    (hsum : Summable fun m : ℕ => (paretoMeasure 1 α).real {z | h + m ≤ L z}) :
    P.real (echoGood L Z s h)ᶜ ≤ ∑' m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ L z} := by
  have hD : ∀ m : ℕ, MeasurableSet {z : ℝ | h + m ≤ L z} := fun m =>
    hLm measurableSet_Ici
  have e : (echoGood L Z s h)ᶜ = ⋃ m : ℕ, Z (s - m) ⁻¹' {z | h + m ≤ L z} := by
    ext ω
    simp [echoGood]
  have he : ∀ m : ℕ, P.real (Z (s - m) ⁻¹' {z | h + m ≤ L z}) =
      (paretoMeasure 1 α).real {z | h + m ≤ L z} := fun m =>
    measureReal_preimage_eq hZ hlaw _ (hD m)
  rw [e]
  refine (measureReal_iUnion_le_tsum (by simp_rw [he]; exact hsum)).trans (le_of_eq ?_)
  simp_rw [he]

/-- **The strong mixing coefficients of the echo process**: for `h ≥ 1`,
`α(h) ≤ 2 ∑_{m ≥ 0} P(L(Z) ≥ h + m)`. -/
theorem alphaMixing_echoProcess_le (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hLm : Measurable L) {h : ℕ} (hh : 1 ≤ h)
    (hsum : Summable fun m : ℕ => (paretoMeasure 1 α).real {z | h + m ≤ L z}) :
    (alphaMixing (fun k : ℕ => echoProcess L Z k) P h).toReal ≤
      2 * ∑' m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ L z} := by
  set T := ∑' m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ L z}
  have hT0 : 0 ≤ T := tsum_nonneg fun _ => measureReal_nonneg
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (iSup_le fun s => ?_)
  -- independence of past and future innovations
  have hI : Indep (innovationPast Z s) (innovationFuture Z s) P :=
    indep_iSup_of_disjoint (m := fun i => MeasurableSpace.comap (Z i) inferInstance)
      (fun i => (hZ i).comap_le) hind.iIndep (by
        rw [Set.disjoint_left]
        intro i hi hi'
        simp only [mem_ofPred_eq] at hi hi'
        omega)
  -- the past of `X` is generated by past innovations
  have hpast : pastMeasurableSpace (fun k : ℕ => echoProcess L Z k) s ≤ innovationPast Z s := by
    refine iSup₂_le fun t ht => Measurable.comap_le ?_
    show Measurable[innovationPast Z s] (echoProcess L Z (t : ℤ))
    rw [← echoProcess_truncPast (L := L) (Z := Z) (s := (s : ℤ)) (t := (t : ℤ))
      (by exact_mod_cast ht)]
    exact measurable_echoProcess (mΩ := innovationPast Z s) (measurable_truncPast s) hLm t
  have hfut : innovationFuture Z s ≤ mΩ := iSup₂_le fun i _ => (hZ i).comap_le
  have hg := measureReal_compl_echoGood_le hZ hlaw hLm (s : ℤ) h hsum (P := P)
  refine iSup₂_le fun A hA => iSup₂_le fun B hB => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨B', hB', e⟩ := exists_inter_echoGood_eq hLm hh hB
  set G := echoGood L Z s h
  set g := P.real Gᶜ
  have hAB' : P.real (A ∩ B') = P.real A * P.real B' := by
    rw [measureReal_def, (Indep_iff _ _ P).1 hI A B' (hpast A hA) hB', ENNReal.toReal_mul]
    rfl
  have e2 : (A ∩ B) ∩ G = (A ∩ B') ∩ G := by rw [inter_assoc, e, ← inter_assoc]
  have h1 := measureReal_le_of_inter_eq (μ := P) e2
  have h2 := measureReal_le_of_inter_eq (μ := P) e2.symm
  have h3 := measureReal_le_of_inter_eq (μ := P) e
  have h4 := measureReal_le_of_inter_eq (μ := P) e.symm
  have hA0 : 0 ≤ P.real A := measureReal_nonneg
  have hA1 : P.real A ≤ 1 := measureReal_le_one
  have hg0 : 0 ≤ g := measureReal_nonneg
  have h5 : P.real A * P.real B ≤ P.real A * P.real B' + g := by nlinarith
  have h6 : P.real A * P.real B' ≤ P.real A * P.real B + g := by nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- **The logarithmic echo process is geometrically strongly mixing**: for `h ≥ 1`,
`α(h) ≤ 2 · 2^α e^α / (1 - e^(-α)) · e^(-α h)`. -/
theorem alphaMixing_logEchoProcess_le (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) {h : ℕ} (hh : 1 ≤ h) :
    (alphaMixing (fun k : ℕ => echoProcess logLag Z k) P h).toReal ≤
      2 * (2 ^ α * Real.exp α / (1 - Real.exp (-α))) * Real.exp (-α) ^ h := by
  set q := Real.exp (-α)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hle : ∀ m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ logLag z} ≤
      2 ^ α * q ^ (h - 1) * q ^ m := by
    intro m
    have e : {z | h + m ≤ logLag z} = {z | (h - 1 + m) + 1 ≤ logLag z} := by
      ext z; simp only [mem_ofPred_eq]; constructor <;> intro hz <;> omega
    rw [e]
    refine (measureReal_logLag_le hα _).trans (le_of_eq ?_)
    rw [pow_add]; ring
  have hgeom : Summable fun m : ℕ => 2 ^ α * q ^ (h - 1) * q ^ m :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hsum : Summable fun m : ℕ => (paretoMeasure 1 α).real {z | h + m ≤ logLag z} :=
    hgeom.of_nonneg_of_le (fun _ => measureReal_nonneg) hle
  refine (alphaMixing_echoProcess_le hZ hind hlaw measurable_logLag hh hsum).trans ?_
  have htsum : ∑' m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ logLag z} ≤
      2 ^ α * q ^ (h - 1) * (1 - q)⁻¹ := by
    refine (hsum.tsum_le_tsum hle hgeom).trans (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hqh : q ^ (h - 1) = Real.exp α * q ^ h := by
    have : q ^ h = q ^ (h - 1) * q := by rw [← pow_succ]; congr 1; omega
    rw [this, ← mul_assoc, mul_comm (Real.exp α), mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, mul_one]
  rw [hqh] at htsum
  have : 2 ^ α * (Real.exp α * q ^ h) * (1 - q)⁻¹ =
      2 ^ α * Real.exp α / (1 - q) * q ^ h := by ring
  rw [this] at htsum
  linarith

/-- The logarithmic echo process is strongly mixing. -/
theorem isStrongMixing_logEchoProcess (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) :
    IsStrongMixing (fun k : ℕ => echoProcess logLag Z k) P := by
  set C := 2 * (2 ^ α * Real.exp α / (1 - Real.exp (-α)))
  have hq0 : 0 ≤ Real.exp (-α) := (Real.exp_pos _).le
  have hq1 : Real.exp (-α) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hlim : Tendsto (fun h : ℕ => C * Real.exp (-α) ^ h) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hreal : Tendsto (fun h => (alphaMixing (fun k : ℕ => echoProcess logLag Z k) P h).toReal)
      atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (by filter_upwards [eventually_ge_atTop 1] with h hh
          exact alphaMixing_logEchoProcess_le hα hZ hind hlaw hh) hlim
  have := (ENNReal.tendsto_ofReal hreal)
  rw [ENNReal.ofReal_zero] at this
  refine this.congr fun h => ?_
  exact ENNReal.ofReal_toReal (alphaMixing_ne_top _)

end EchoMixing

/-! ### The general theorem keeps anticlustering -/

section General

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℤ → Ω → ℝ} {α : ℝ}
  {Q : Measure Ω'} [IsProbabilityMeasure Q] {Θ : ℤ → Ω' → ℝ}

/-- **`θ = ϑ` under strong mixing with a rate and anticlustering** ([BS09, §4], [KS20, §7.5]).
`m`-dependence in `hasExtremalIndex_of_isMDependent` can be replaced by strong mixing of `|X|`
with `(n / rₙ) α(lₙ) → 0`, `lₙ / rₙ → 0`, **provided forward anticlustering is assumed** along
every level sequence: the block condition then follows from `conditionA_of_alphaMixing`.
Anticlustering cannot be dropped: see `logEcho_alphaMixing_theta_ne_vartheta`. -/
theorem HasSpectralTailProcess.hasExtremalIndex_abs_of_alphaMixing (hα : 0 < α)
    (hX : ∀ t, Measurable (X t)) (hΘm : ∀ t, Measurable (Θ t))
    (hstat : HasShiftInvariantWindows P X) (h : HasSpectralTailProcess P X α Q Θ)
    {r l : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0))
    (hlr : Tendsto (fun n => (l n : ℝ) / r n) atTop (𝓝 0))
    (hmix : Tendsto (fun n : ℕ => (n : ℝ) / r n *
      (alphaMixing (fun k : ℕ => |X k|) P (l n)).toReal) atTop (𝓝 0))
    (hAC : ∀ τ > 0, ∀ u : ℕ → ℝ,
      Tendsto (fun n : ℕ => n * P.real {ω | u n < |X 0 ω|}) atTop (𝓝 τ) →
        ForwardAntiClusteringAt P X u r) :
    HasExtremalIndex (fun k : ℕ => |X k|) P (candidateExtremalIndex Q Θ α).toReal := by
  refine h.hasExtremalIndex_abs hα hX hΘm hstat hr hrn fun τ hτ u hu => ⟨hAC τ hτ u hu, ?_⟩
  refine conditionA_of_alphaMixing (hstat.isStationary_abs hX)
    (fun k => continuous_abs.measurable.comp (hX k)) hr hrn hlr hmix (C := τ + 1) ?_
  filter_upwards [hu.eventually (gt_mem_nhds (lt_add_one τ))] with n hn
  exact hn.le

end General

/-! ### The counterexample -/

namespace Minimality

section Counterexample

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ}

/-- **Geometric strong mixing does not give `θ = ϑ`; anticlustering does not follow from mixing.**
The logarithmic echo process (iid Pareto(`α`) innovations, `L(z) = ⌊log z⌋₊ + 1`) is
* strongly mixing, with `α(h) ≤ C e^(-α h)` for `h ≥ 1`;
* stationary, with spectral tail process `Θ_t = 1{t = 0}`, so `ϑ = 1`;
* of extremal index `θ = 1/2 ≠ ϑ`;
* in violation of forward anticlustering along every `n P(X_0 > uₙ) → τ > 0`, `rₙ / n → 0`,
  `log n = o(rₙ)`, although `𝒜(uₙ)` holds there (`conditionA_logEchoProcess`). -/
theorem logEcho_alphaMixing_theta_ne_vartheta (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α)
    (hpos : ∀ t ω, 0 ≤ Z t ω) :
    IsStrongMixing (fun k : ℕ => echoProcess logLag Z k) P ∧
      (∀ h : ℕ, 1 ≤ h → (alphaMixing (fun k : ℕ => echoProcess logLag Z k) P h).toReal ≤
        2 * (2 ^ α * Real.exp α / (1 - Real.exp (-α))) * Real.exp (-α) ^ h) ∧
      HasShiftInvariantWindows P (echoProcess logLag Z) ∧
      HasSpectralTailProcess P (echoProcess logLag Z) α (Measure.dirac ()) unitSpectral ∧
      (candidateExtremalIndex (Measure.dirac ()) unitSpectral α).toReal = 1 ∧
      HasExtremalIndex (fun k : ℕ => echoProcess logLag Z k) P (1 / 2) ∧
      (∀ (u : ℕ → ℝ) (τ : ℝ), 0 < τ →
        Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z 0 ω}) atTop (𝓝 τ) →
        ∀ r : ℕ → ℕ, Tendsto r atTop atTop → Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0) →
          Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0) →
          ConditionA (fun k : ℕ => |echoProcess logLag Z k|) P u r ∧
            ¬ ForwardAntiClusteringAt P (echoProcess logLag Z) u r) := by
  obtain ⟨hstat, hT, hϑ, hθ⟩ := logEchoProcess_theta_lt_vartheta hα hZ hind hlaw hpos
  refine ⟨isStrongMixing_logEchoProcess hα hZ hind hlaw,
    fun h hh => alphaMixing_logEchoProcess_le hα hZ hind hlaw hh, hstat, hT, hϑ, hθ,
    fun u τ hτ0 hτ r hr hrn hlogr => ⟨conditionA_logEchoProcess hα hZ hind hlaw hpos hτ hr hrn
      hlogr, (logEchoProcess_hasLateReturnMass_of_tendsto hα hZ hind hlaw hpos hτ0 hτ hr hrn
        hlogr).2.2⟩⟩

end Counterexample

end Minimality

end ExtremeValueTheory

/-! ### Deprecated names -/

namespace ExtremeValueTheory

@[deprecated (since := "2026-10-23")] alias logEcho_alphaMixing_theta_ne_vartheta := Minimality.logEcho_alphaMixing_theta_ne_vartheta

end ExtremeValueTheory
