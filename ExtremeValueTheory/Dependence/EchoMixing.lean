/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.BetaMixing
import ExtremeValueTheory.Dependence.EchoPowerLag
import ExtremeValueTheory.Minimality.DependenceMixing

/-!
# `β`-mixing of the echo process

The echo process `X_t = max(Z_t, max {Z_s : s < t, s + L(Z_s) = t})` (iid Pareto(`α`) shocks
`Z`, measurable lag `L`) is absolutely regular. We reuse the coupling of
`Minimality/DependenceMixing.lean`: on the good event `G` that no shock at a time `≤ s` echoes at
or after `s + h`, every future event agrees with an event of `σ(Z_i : i > s)`
(`exists_inter_echoGood_eq`), and `P(Gᶜ) ≤ ∑_{m ≥ 0} P(L(Z) ≥ h + m)`
(`measureReal_compl_echoGood_le`). For `β` the coupled events of a future partition must also be
disjoint; disjointifying them keeps the agreement on `G`, and summing over both partitions gives
`β(h) ≤ 2 P(Gᶜ)`.

## Main results

* `betaMixing_echoProcess_le`: `β(h) ≤ 2 ∑_{m ≥ 0} P(L(Z) ≥ h + m)` for `h ≥ 1` (the same bound
  as `alphaMixing_echoProcess_le` for `α(h)`).
* `isBetaMixing_echoProcess`: `E[L(Z)] < ∞` implies `β`-mixing.
* `betaMixing_logEchoProcess_le`: for `L(z) = ⌊log z⌋₊ + 1`,
  `β(h) ≤ 2 · 2^α e^α / (1 - e^(-α)) · e^(-α h)` (geometric `β`-mixing).
* `powEchoProcess_not_conditionA`, `powEchoProcess_not_conditionA_and_antiClustering`: for the
  power lag `⌊z^γ⌋₊ + 1`, `0 < γ < α`, along `n P(X_0 > uₙ) → τ > 0` and
  `log rₙ / log n → ρ ∈ (0, 1) \ {γ / α}`: the process is `β`-mixing, anticlustering holds iff
  `ρ < γ / α`, and `A(uₙ)` fails whenever anticlustering holds.
* `logEchoProcess_antiClusteringAt_short`: anticlustering of the logarithmic echo for
  `rₙ = o(log n)`.
* `logEchoProcess_betaMixing_incompatible`: geometric `β`-mixing of the logarithmic echo, and for
  all block lengths `rₙ → ∞` with `rₙ / log n → c ∈ [0, ∞]` (and `rₙ = o(n)` when `c = ∞`):
  anticlustering and `A(uₙ)` never hold together (`AC` holds and `A` fails for `c = 0`; `A`
  fails for `0 < c < ∞`; `A` holds and `AC` fails for `c = ∞`).

## Remarks

The general theorem "stationary + mixing + anticlustering ⇒ `θ = ϑ`"
(`HasSpectralTailProcess.hasExtremalIndex_abs_of_alphaMixing`) needs `A(uₙ)` and `AC` along a
common block length. The echo processes are as well mixing as one could want (geometrically
`β`-mixing in the logarithmic case), their tail process vanishes (`Θ_t = 1{t = 0}`), yet
`θ = 1/2 < 1 = ϑ`: the mixing route gives `A(uₙ)` only for blocks longer than the echo lag of
an exceedance, while anticlustering holds only for blocks shorter than it.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ExtremeValueTheory

section Partition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- For pairwise disjoint measurable `Cᵢ`, `∑ᵢ P(Cᵢ ∩ S) ≤ P(S)`. -/
theorem sum_measureReal_inter_le {k : ℕ} {C : Fin k → Set Ω} (hC : ∀ i, MeasurableSet (C i))
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) {S : Set Ω} (hS : MeasurableSet S) :
    ∑ i, P.real (C i ∩ S) ≤ P.real S := by
  rw [← measureReal_iUnion_fintype (μ := P)
    (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left)
    fun i => (hC i).inter hS]
  exact measureReal_mono (iUnion_subset fun i => inter_subset_right)

/-- For a finite measurable partition `(Cᵢ)` of `Ω`, `∑ᵢ P(Cᵢ ∩ S) = P(S)`. -/
theorem sum_measureReal_inter_eq {k : ℕ} {C : Fin k → Set Ω} (hC : ∀ i, MeasurableSet (C i))
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) (hu : (⋃ i, C i) = univ) {S : Set Ω}
    (hS : MeasurableSet S) : ∑ i, P.real (C i ∩ S) = P.real S := by
  rw [← measureReal_iUnion_fintype (μ := P)
    (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left)
    fun i => (hC i).inter hS, ← iUnion_inter, hu, univ_inter]

end Partition

section EchoBeta

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}

theorem measurableSet_echoGood (hZ : ∀ t, Measurable (Z t)) (hLm : Measurable L) (s : ℤ)
    (h : ℕ) : MeasurableSet (echoGood L Z s h) := by
  have : echoGood L Z s h = ⋂ m : ℕ, (fun ω => L (Z (s - m) ω)) ⁻¹' Iio (h + m) := by
    ext ω; simp [echoGood]
  rw [this]
  exact MeasurableSet.iInter fun m => (hLm.comp (hZ _)) measurableSet_Iio

/-- **The `β`-mixing coefficients of the echo process**: for `h ≥ 1`,
`β(h) ≤ 2 ∑_{m ≥ 0} P(L(Z) ≥ h + m)`. Only measurability of `L`, independence and the common
Pareto law of the innovations, and summability of the tail of `L(Z)` are used. -/
theorem betaMixing_echoProcess_le (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hLm : Measurable L) {h : ℕ} (hh : 1 ≤ h)
    (hsum : Summable fun m : ℕ => (paretoMeasure 1 α).real {z | h + m ≤ L z}) :
    (betaMixing (fun k : ℕ => echoProcess L Z k) P h).toReal ≤
      2 * ∑' m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ L z} := by
  set T := ∑' m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ L z}
  have hT0 : 0 ≤ T := tsum_nonneg fun _ => measureReal_nonneg
  have hX : ∀ t : ℕ, Measurable (echoProcess L Z t) := fun t => measurable_echoProcess hZ hLm t
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (iSup_le fun s => ?_)
  have hI : Indep (innovationPast Z s) (innovationFuture Z s) P :=
    indep_iSup_of_disjoint (m := fun i => MeasurableSpace.comap (Z i) inferInstance)
      (fun i => (hZ i).comap_le) hind.iIndep (by
        rw [Set.disjoint_left]
        intro i hi hi'
        simp only [mem_ofPred_eq] at hi hi'
        omega)
  have hpast : pastMeasurableSpace (fun k : ℕ => echoProcess L Z k) s ≤ innovationPast Z s := by
    refine iSup₂_le fun t ht => Measurable.comap_le ?_
    show Measurable[innovationPast Z s] (echoProcess L Z (t : ℤ))
    rw [← echoProcess_truncPast (L := L) (Z := Z) (s := (s : ℤ)) (t := (t : ℤ))
      (by exact_mod_cast ht)]
    exact measurable_echoProcess (mΩ := innovationPast Z s) (measurable_truncPast s) hLm t
  have hfut : innovationFuture Z s ≤ mΩ := iSup₂_le fun i _ => (hZ i).comap_le
  have hg := measureReal_compl_echoGood_le hZ hlaw hLm (s : ℤ) h hsum (P := P)
  set G := echoGood L Z s h
  have hG : MeasurableSet G := measurableSet_echoGood hZ hLm s h
  simp only [betaMixingCoeff, iSup_le_iff]
  intro k l A hA hdA huA B hB hdB huB
  refine ENNReal.ofReal_le_ofReal ?_
  have hAm : ∀ i, MeasurableSet (A i) := fun i => pastMeasurableSpace_le hX s _ (hA i)
  have hBm : ∀ j, MeasurableSet (B j) := fun j => futureMeasurableSpace_le hX _ _ (hB j)
  -- couple the future partition with a disjoint family of future-innovation events
  choose B' hB' e using fun j => exists_inter_echoGood_eq hLm hh (hB j)
  set B'' : Fin l → Set Ω := fun j => B' j \ ⋃ (i : Fin l) (_ : i < j), B' i
  have hB'' : ∀ j, MeasurableSet[innovationFuture Z s] (B'' j) := fun j =>
    (hB' j).diff (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hB' i)
  have hB''m : ∀ j, MeasurableSet (B'' j) := fun j => hfut _ (hB'' j)
  have hdB'' : Pairwise fun i j => Disjoint (B'' i) (B'' j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · refine Set.disjoint_left.2 fun ω h1 h2 => h2.2 ?_
      exact mem_iUnion₂.2 ⟨i, hlt, h1.1⟩
    · refine Set.disjoint_left.2 fun ω h1 h2 => h1.2 ?_
      exact mem_iUnion₂.2 ⟨j, hlt, h2.1⟩
  have e'' : ∀ j, B j ∩ G = B'' j ∩ G := by
    intro j
    ext ω
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : ω ∈ B' j ∩ G := e j ▸ ⟨h1, h2⟩
      refine ⟨⟨h3.1, fun hω => ?_⟩, h2⟩
      obtain ⟨i, hi, h4⟩ := mem_iUnion₂.1 hω
      have h5 : ω ∈ B i ∩ G := (e i).symm ▸ ⟨h4, h2⟩
      exact Set.disjoint_left.1 (hdB (ne_of_lt hi)) h5.1 h1
    · rintro ⟨h1, h2⟩
      have h3 : ω ∈ B j ∩ G := (e j).symm ▸ ⟨h1.1, h2⟩
      exact h3
  -- the pointwise bound
  have key : ∀ i j, |P.real (A i ∩ B j) - P.real (A i) * P.real (B j)| ≤
      P.real (A i ∩ (B j ∩ Gᶜ)) + P.real (A i ∩ (B'' j ∩ Gᶜ)) +
        P.real (A i) * (P.real (B j ∩ Gᶜ) + P.real (B'' j ∩ Gᶜ)) := by
    intro i j
    have hind' : P.real (A i ∩ B'' j) = P.real (A i) * P.real (B'' j) := by
      rw [measureReal_def, (Indep_iff _ _ P).1 hI _ _ (hpast _ (hA i)) (hB'' j),
        ENNReal.toReal_mul]
      rfl
    have split : ∀ S : Set Ω, MeasurableSet S → P.real S = P.real (S ∩ G) + P.real (S ∩ Gᶜ) :=
      fun S hS => (measureReal_inter_add_sdiff (s := S) hG).symm.trans (by rw [Set.sdiff_eq])
    have hAB := split _ ((hAm i).inter (hBm j))
    have hAB'' := split _ ((hAm i).inter (hB''m j))
    have hB1 := split _ (hBm j)
    have hB2 := split _ (hB''m j)
    have eG : A i ∩ B j ∩ G = A i ∩ B'' j ∩ G := by rw [inter_assoc, e'', ← inter_assoc]
    rw [eG] at hAB
    have r1 : A i ∩ B j ∩ Gᶜ = A i ∩ (B j ∩ Gᶜ) := inter_assoc _ _ _
    have r2 : A i ∩ B'' j ∩ Gᶜ = A i ∩ (B'' j ∩ Gᶜ) := inter_assoc _ _ _
    rw [r1] at hAB
    rw [r2] at hAB''
    have hBG : P.real (B j ∩ G) = P.real (B'' j ∩ G) := by rw [e'']
    have hA0 : 0 ≤ P.real (A i) := measureReal_nonneg
    have n1 : 0 ≤ P.real (A i ∩ (B j ∩ Gᶜ)) := measureReal_nonneg
    have n2 : 0 ≤ P.real (A i ∩ (B'' j ∩ Gᶜ)) := measureReal_nonneg
    have n3 : 0 ≤ P.real (B j ∩ Gᶜ) := measureReal_nonneg
    have n4 : 0 ≤ P.real (B'' j ∩ Gᶜ) := measureReal_nonneg
    have hD : P.real (A i ∩ B j) - P.real (A i) * P.real (B j) =
        (P.real (A i ∩ (B j ∩ Gᶜ)) - P.real (A i ∩ (B'' j ∩ Gᶜ))) -
          P.real (A i) * (P.real (B j ∩ Gᶜ) - P.real (B'' j ∩ Gᶜ)) := by
      rw [hAB, hB1, hBG]
      rw [hAB''] at hind'
      rw [hB2] at hind'
      linarith
    rw [hD, abs_le]
    constructor <;> nlinarith
  have hGc : MeasurableSet Gᶜ := hG.compl
  have s1 : ∑ i, ∑ j, P.real (A i ∩ (B j ∩ Gᶜ)) = P.real Gᶜ := by
    rw [Finset.sum_comm]
    simp_rw [sum_measureReal_inter_eq hAm hdA huA ((hBm _).inter hGc)]
    exact sum_measureReal_inter_eq hBm hdB huB hGc
  have s2 : ∑ i, ∑ j, P.real (A i ∩ (B'' j ∩ Gᶜ)) ≤ P.real Gᶜ := by
    rw [Finset.sum_comm]
    simp_rw [sum_measureReal_inter_eq hAm hdA huA ((hB''m _).inter hGc)]
    exact sum_measureReal_inter_le hB''m hdB'' hGc
  have s3 : ∑ i, P.real (A i) = 1 := by
    have := sum_measureReal_inter_eq (P := P) hAm hdA huA MeasurableSet.univ
    simpa using this
  have s4 : ∑ j, P.real (B j ∩ Gᶜ) = P.real Gᶜ := sum_measureReal_inter_eq hBm hdB huB hGc
  have s5 : ∑ j, P.real (B'' j ∩ Gᶜ) ≤ P.real Gᶜ := sum_measureReal_inter_le hB''m hdB'' hGc
  calc 2⁻¹ * ∑ i, ∑ j, |P.real (A i ∩ B j) - P.real (A i) * P.real (B j)|
      ≤ 2⁻¹ * ∑ i, ∑ j, (P.real (A i ∩ (B j ∩ Gᶜ)) + P.real (A i ∩ (B'' j ∩ Gᶜ)) +
          P.real (A i) * (P.real (B j ∩ Gᶜ) + P.real (B'' j ∩ Gᶜ))) := by
        gcongr with i _ j _
        exact key i j
    _ = 2⁻¹ * (∑ i, ∑ j, P.real (A i ∩ (B j ∩ Gᶜ)) + ∑ i, ∑ j, P.real (A i ∩ (B'' j ∩ Gᶜ)) +
          (∑ i, P.real (A i)) * (∑ j, P.real (B j ∩ Gᶜ) + ∑ j, P.real (B'' j ∩ Gᶜ))) := by
        simp only [Finset.sum_add_distrib, Finset.sum_mul]
        congr 2
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ 2⁻¹ * (P.real Gᶜ + P.real Gᶜ + 1 * (P.real Gᶜ + P.real Gᶜ)) := by
        rw [s1, s3, s4]
        gcongr
    _ ≤ 2 * T := by linarith

end EchoBeta

section EchoBetaRates

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : ℝ} {Z : ℤ → Ω → ℝ} {L : ℝ → ℕ}

/-- **Every echo process with `E[L(Z)] < ∞` is `β`-mixing**: `β(h) ≤ 2 ∑_{j ≥ h} P(L(Z) ≥ j)`,
the tail of a convergent series. -/
theorem isBetaMixing_echoProcess (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
    (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hLm : Measurable L)
    (hLsum : Summable fun j : ℕ => (paretoMeasure 1 α).real {z | j + 1 ≤ L z}) :
    IsBetaMixing (fun k : ℕ => echoProcess L Z k) P := by
  set f : ℕ → ℝ := fun j => (paretoMeasure 1 α).real {z | j ≤ L z}
  have hf : Summable f := (summable_nat_add_iff 1).1 (by simpa [f] using hLsum)
  have hsum : ∀ h : ℕ, Summable fun m : ℕ => (paretoMeasure 1 α).real {z | h + m ≤ L z} :=
    fun h => ((summable_nat_add_iff h).2 hf).congr fun m => by simp only [f, add_comm]
  have htail : Tendsto (fun h : ℕ => 2 * ∑' m : ℕ, (paretoMeasure 1 α).real {z | h + m ≤ L z})
      atTop (𝓝 0) := by
    have := (tendsto_sum_nat_add f).const_mul 2
    rw [mul_zero] at this
    exact this.congr fun h => by simp only [f, add_comm]
  have hX : ∀ t : ℕ, Measurable (echoProcess L Z t) := fun t => measurable_echoProcess hZ hLm t
  have hreal : Tendsto (fun h => (betaMixing (fun k : ℕ => echoProcess L Z k) P h).toReal)
      atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (by filter_upwards [eventually_ge_atTop 1] with h hh
          exact betaMixing_echoProcess_le hZ hind hlaw hLm hh (hsum h)) htail
  have := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at this
  exact this.congr fun h => ENNReal.ofReal_toReal (betaMixing_ne_top hX h)

/-- **The logarithmic echo process is geometrically `β`-mixing**: for `h ≥ 1`,
`β(h) ≤ 2 · 2^α e^α / (1 - e^(-α)) · e^(-α h)`. -/
theorem betaMixing_logEchoProcess_le (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) {h : ℕ} (hh : 1 ≤ h) :
    (betaMixing (fun k : ℕ => echoProcess logLag Z k) P h).toReal ≤
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
  refine (betaMixing_echoProcess_le hZ hind hlaw measurable_logLag hh hsum).trans ?_
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

end EchoBetaRates

/-! ### Mixing, the block condition and anticlustering never meet -/

section Incompatible

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α γ : ℝ} {Z : ℤ → Ω → ℝ}
  (hα : 0 < α) (hZ : ∀ t, Measurable (Z t)) (hind : iIndepFun Z P)
  (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω)

include hα hZ hind hlaw hpos in
/-- **For the power-lag echo process the block condition fails for short blocks.** With
`n P(X_0 > uₙ) → τ > 0` and `log rₙ / log n → ρ ∈ (0, γ / α)`, `A(uₙ)` fails along `rₙ`:
anticlustering holds there, so the escape mass is `0`, whereas `A(uₙ)` together with `θ = 1/2`
would force it to be `ϑ - θ = 1/2`. -/
theorem powEchoProcess_not_conditionA (hγ : 0 < γ) (hγα : γ < α) {u : ℕ → ℝ} {τ : ℝ}
    (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess (powLag γ) Z 0 ω}) atTop (𝓝 τ))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < γ / α) {r : ℕ → ℕ}
    (hr : Tendsto (fun n : ℕ => Real.log (r n) / Real.log n) atTop (𝓝 ρ)) :
    ¬ ConditionA (fun k : ℕ => |echoProcess (powLag γ) Z k|) P u r := by
  intro hA
  have hρ1 : ρ < 1 := hρ.trans ((div_lt_one hα).2 hγα)
  obtain ⟨hstat, hT, -, hθ⟩ := powEchoProcess_theta_lt_vartheta hα hZ hind hlaw hpos hγ hγα
    (P := P)
  obtain ⟨hu, hnb, hlu⟩ := echoProcess_levels hα hZ hind hlaw hpos (measurable_powLag γ)
    (one_le_powLag γ) (tendsto_powLag hγ) hτ0 hτ
  obtain ⟨hrr, hrb, -⟩ := polyBlocks_scales (γ := γ) hα hu hlu hρ0 hρ1 hr
  have hAC := ((powEchoProcess_polyBlocks hα hZ hind hlaw hpos hγ hγα hτ0 hτ hρ0 hρ1 hr).1 hρ).2
  have hτ' : Tendsto (fun n : ℕ => n * P.real {ω | u n < |echoProcess (powLag γ) Z 0 ω|})
      atTop (𝓝 τ) := by
    simpa [abs_of_nonneg (echoProcess_nonneg hpos _ _)] using hτ
  have hθ' : HasExtremalIndex (fun k : ℕ => |echoProcess (powLag γ) Z k|) P (1 / 2) := by
    convert hθ using 3 with k
    funext ω
    exact abs_of_nonneg (echoProcess_nonneg hpos _ _)
  -- `rₙ / n → 0`
  have hrn : Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0) := by
    have := hrb.div hnb (by positivity)
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [hu.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hun hn
    have hb : 0 < u n ^ (-α) := Real.rpow_pos_of_pos hun _
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Pi.div_apply]
    field_simp
  have h := hT.hasEscapeMass_of_hasExtremalIndex hα (measurable_echoProcess hZ (measurable_powLag γ))
    measurable_unitSpectral hstat hθ' hτ' hτ0 hrr hrn hA
  rw [candidateExtremalIndex_unitSpectral hα] at h
  have := h.unique (hAC.forward.hasEscapeMass_zero hrr)
  norm_num at this

include hα hZ hind hlaw hpos in
/-- **The power-lag echo process: mixing, anticlustering and the block condition.**
For `0 < γ < α` the power-lag echo process is stationary and `β`-mixing, with `ϑ = 1` and
`θ = 1/2`. Along `n P(X_0 > uₙ) → τ > 0` and block lengths with `log rₙ / log n → ρ ∈ (0, 1)`,
`ρ ≠ γ / α`, anticlustering and the block condition `A(uₙ)` never hold together:
anticlustering holds iff `ρ < γ / α`, and then `A(uₙ)` fails. -/
theorem powEchoProcess_not_conditionA_and_antiClustering (hγ : 0 < γ) (hγα : γ < α)
    {u : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess (powLag γ) Z 0 ω}) atTop (𝓝 τ))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρ : ρ ≠ γ / α) {r : ℕ → ℕ}
    (hr : Tendsto (fun n : ℕ => Real.log (r n) / Real.log n) atTop (𝓝 ρ)) :
    IsBetaMixing (fun k : ℕ => echoProcess (powLag γ) Z k) P ∧
      (AntiClusteringAt P (echoProcess (powLag γ) Z) u r ↔ ρ < γ / α) ∧
      ¬ (ConditionA (fun k : ℕ => |echoProcess (powLag γ) Z k|) P u r ∧
        AntiClusteringAt P (echoProcess (powLag γ) Z) u r) := by
  have hpb := powEchoProcess_polyBlocks hα hZ hind hlaw hpos hγ hγα hτ0 hτ hρ0 hρ1 hr
  have hiff : AntiClusteringAt P (echoProcess (powLag γ) Z) u r ↔ ρ < γ / α := by
    refine ⟨fun hAC => ?_, fun hlt => (hpb.1 hlt).2⟩
    by_contra hge
    exact (hpb.2 (lt_of_le_of_ne (not_lt.1 hge) (Ne.symm hρ))).2 hAC.forward
  refine ⟨isBetaMixing_echoProcess hZ hind hlaw (measurable_powLag γ)
    (summable_powLag hα hγ hγα), hiff, fun ⟨hA, hAC⟩ => ?_⟩
  exact powEchoProcess_not_conditionA hα hZ hind hlaw hpos hγ hγα hτ0 hτ hρ0 (hiff.1 hAC) hr hA

include hα hZ hind hlaw hpos in
/-- **Anticlustering of the logarithmic echo process for blocks `rₙ = o(log n)`.** -/
theorem logEchoProcess_antiClusteringAt_short {u : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z 0 ω}) atTop (𝓝 τ))
    {r : ℕ → ℕ} (hrlog : Tendsto (fun n : ℕ => (r n : ℝ) / Real.log n) atTop (𝓝 0)) :
    AntiClusteringAt P (echoProcess logLag Z) u r := by
  obtain ⟨hu, hnb, hlu⟩ := logEchoProcess_levels hα hZ hind hlaw hpos hτ0 hτ
  have hrb := tendsto_mul_rpow_of_tendsto_div_log hnb hrlog
  have hq : Tendsto (fun n => (r n : ℝ) / Real.log (u n)) atTop (𝓝 0) := by
    have := hrlog.div hlu (one_div_ne_zero hα.ne')
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 1, hu.eventually_gt_atTop 1] with n hn hun
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hl : Real.log n ≠ 0 := (Real.log_pos hn').ne'
    have hl' : Real.log (u n) ≠ 0 := (Real.log_pos hun).ne'
    simp only [Pi.div_apply]
    field_simp
  refine antiClusteringAt_echoProcess hα hZ hind hlaw hpos measurable_logLag one_le_logLag hu
    hrb ?_
  filter_upwards [hq.eventually (gt_mem_nhds one_pos), hu.eventually_gt_atTop 1]
    with n hn hun z hz
  have hl : 0 < Real.log (u n) := Real.log_pos hun
  rw [div_lt_one hl] at hn
  have h1 : r n ≤ ⌊Real.log (u n)⌋₊ := Nat.le_floor hn.le
  have h2 := logLag_mono (by linarith) hz
  simp only [logLag] at h2 ⊢
  omega

include hα hZ hind hlaw hpos in
/-- **The logarithmic echo process: geometric `β`-mixing, yet anticlustering and the block
condition never hold together.** It is stationary with `ϑ = 1`, `θ = 1/2` and
`β(h) ≤ C e^(-α h)`. Along `n P(X_0 > uₙ) → τ > 0`:
* for `rₙ → ∞`, `rₙ = o(log n)`: anticlustering holds, `A(uₙ)` fails;
* for `rₙ / log n → c ∈ (0, ∞)`: `A(uₙ)` fails;
* for `log n = o(rₙ)`, `rₙ = o(n)`: `A(uₙ)` holds, forward anticlustering fails.
So the mixing route to `𝒜(uₙ)` needs blocks longer than the echo lag `(1/α) log n`, while
anticlustering needs blocks shorter than it. -/
theorem logEchoProcess_betaMixing_incompatible :
    (∀ h : ℕ, 1 ≤ h → (betaMixing (fun k : ℕ => echoProcess logLag Z k) P h).toReal ≤
        2 * (2 ^ α * Real.exp α / (1 - Real.exp (-α))) * Real.exp (-α) ^ h) ∧
      IsBetaMixing (fun k : ℕ => echoProcess logLag Z k) P ∧
      ∀ (u : ℕ → ℝ) (τ : ℝ), 0 < τ →
        Tendsto (fun n : ℕ => n * P.real {ω | u n < echoProcess logLag Z 0 ω}) atTop (𝓝 τ) →
        ∀ r : ℕ → ℕ, Tendsto r atTop atTop →
          (Tendsto (fun n : ℕ => (r n : ℝ) / Real.log n) atTop (𝓝 0) →
            AntiClusteringAt P (echoProcess logLag Z) u r ∧
              ¬ ConditionA (fun k : ℕ => |echoProcess logLag Z k|) P u r) ∧
          (∀ c : ℝ, 0 < c → Tendsto (fun n : ℕ => (r n : ℝ) / Real.log n) atTop (𝓝 c) →
            ¬ ConditionA (fun k : ℕ => |echoProcess logLag Z k|) P u r) ∧
          (Tendsto (fun n => (r n : ℝ) / n) atTop (𝓝 0) →
            Tendsto (fun n : ℕ => Real.log n / r n) atTop (𝓝 0) →
            ConditionA (fun k : ℕ => |echoProcess logLag Z k|) P u r ∧
              ¬ ForwardAntiClusteringAt P (echoProcess logLag Z) u r) :=
  ⟨fun _ hh => betaMixing_logEchoProcess_le hα hZ hind hlaw hh,
    isBetaMixing_echoProcess hZ hind hlaw measurable_logLag (summable_logLag hα),
    fun _ _ hτ0 hτ _ hr => ⟨fun hrlog =>
      ⟨logEchoProcess_antiClusteringAt_short hα hZ hind hlaw hpos hτ0 hτ hrlog,
        logEchoProcess_not_conditionA hα hZ hind hlaw hpos hτ0 hτ hr le_rfl hrlog⟩,
      fun _ hc hrlog => logEchoProcess_not_conditionA hα hZ hind hlaw hpos hτ0 hτ hr hc.le hrlog,
      fun hrn hlogr => ⟨conditionA_logEchoProcess hα hZ hind hlaw hpos hτ hr hrn hlogr,
        (logEchoProcess_hasEscapeMass_of_tendsto hα hZ hind hlaw hpos hτ0 hτ hr hrn
          hlogr).2.2⟩⟩⟩

end Incompatible

end ExtremeValueTheory
