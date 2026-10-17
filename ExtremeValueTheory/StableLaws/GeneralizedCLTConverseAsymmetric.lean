/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.StableLaws.LevyMeasureLimit

/-!
# The converse of the generalized central limit theorem (general case)

WIP
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ExtremeValueTheory

namespace GCLTConverse

open GCLT Subexp

section NormSeq

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}

/-- The canonical normalizing sequence `aₙ = inf {x : P(|X| > x) ≤ 1 / n}`. -/
noncomputable def normSeq (μ : Measure ℝ) (n : ℕ) : ℝ :=
  sInf {x : ℝ | absTail μ x ≤ (n : ℝ)⁻¹}

/-- `P(|X| > x)` is right-continuous: if `P(|X| > y) ≤ c` for all `y > x`, then
`P(|X| > x) ≤ c`. -/
theorem absTail_le_of_forall_gt {x c : ℝ} (h : ∀ y, x < y → absTail μ y ≤ c) :
    absTail μ x ≤ c := by
  have hU : {y : ℝ | x < |y|} = ⋃ k : ℕ, {y : ℝ | x + 1 / ((k : ℝ) + 1) < |y|} := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun k : ℕ => {y : ℝ | x + 1 / ((k : ℝ) + 1) < |y|} := by
    intro i j hij y (hy : x + 1 / ((i : ℝ) + 1) < |y|)
    show x + 1 / ((j : ℝ) + 1) < |y|
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
    linarith
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [← hU] at hlim
  have hlim' : Tendsto (fun k : ℕ => absTail μ (x + 1 / ((k : ℝ) + 1))) atTop
      (𝓝 (absTail μ x)) := by
    have := (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hlim
    exact this.congr fun k => by simp [absTail, measureReal_def, Function.comp]
  exact le_of_tendsto hlim' (Eventually.of_forall fun k => h _ (by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith))

/-- `P(|X| > x) → 0` as `x → ∞`. -/
theorem tendsto_absTail_zero : Tendsto (absTail μ) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun x : ℝ => {y : ℝ | x < |y|})
    (fun x => (measurableSet_abs_gt x).nullMeasurableSet)
    (fun x x' hxx' y (hy : x' < |y|) => (lt_of_le_of_lt hxx' hy : x < |y|))
    ⟨0, measure_ne_top μ _⟩
  have hempty : (⋂ x : ℝ, {y : ℝ | x < |y|}) = ∅ := by
    ext y
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact ⟨|y|, le_rfl⟩
  rw [hempty, measure_empty] at h
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  exact this.congr fun x => by simp [absTail, measureReal_def, Function.comp]

variable (hRV : IsRegularlyVarying (absTail μ) (-α))
include hRV

theorem absTail_pos (x : ℝ) : 0 < absTail μ x :=
  IsRegularlyVarying.pos_of_antitone absTail_antitone hRV.1 x

/-- For `n` large the set `{x : P(|X| > x) ≤ 1 / n}` is the half-line above `aₙ`, contains
`aₙ`, and lies above any given `M`. -/
theorem normSeq_spec (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, M ≤ normSeq μ n ∧ absTail μ (normSeq μ n) ≤ (n : ℝ)⁻¹ ∧
      ∀ x, x < normSeq μ n → (n : ℝ)⁻¹ < absTail μ x := by
  have hpos := absTail_pos hRV
  have h0 : Tendsto (absTail μ) atTop (𝓝 0) := tendsto_absTail_zero
  filter_upwards [(tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds (hpos M)), eventually_gt_atTop 0] with n hn hn0
  simp only [Function.comp] at hn
  set S := {x : ℝ | absTail μ x ≤ (n : ℝ)⁻¹}
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  obtain ⟨x₁, hx₁⟩ : S.Nonempty := by
    obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 ((tendsto_order.1 h0).2 _ hninv)
    exact ⟨x₁, (hx₁ x₁ le_rfl).le⟩
  have hlow : ∀ x ∈ S, M < x := by
    intro x hx
    by_contra h
    exact absurd ((absTail_antitone (not_lt.1 h)).trans hx) (not_le.2 hn)
  have hbdd : BddBelow S := ⟨M, fun x hx => (hlow x hx).le⟩
  have hup : ∀ y, sInf S < y → y ∈ S := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt ⟨x₁, hx₁⟩ hy
    exact (absTail_antitone hsy.le).trans hs
  refine ⟨le_csInf ⟨x₁, hx₁⟩ fun x hx => (hlow x hx).le,
    absTail_le_of_forall_gt fun y hy => hup y hy, fun x hx => ?_⟩
  by_contra h
  exact absurd (csInf_le hbdd (not_lt.1 h)) (not_le.2 hx)

theorem tendsto_normSeq : Tendsto (normSeq μ) atTop atTop :=
  tendsto_atTop.2 fun M => (normSeq_spec hRV M).mono fun _ h => h.1

/-- **Normalizing sequences**: if `P(|X| > ·)` is regularly varying with index `-α`, `α > 0`,
then `aₙ = inf {x : P(|X| > x) ≤ 1 / n}` satisfies `n P(|X| > aₙ) → 1`. -/
theorem tendsto_mul_absTail_normSeq :
    Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (normSeq μ n)) atTop (𝓝 1) := by
  have hpos := absTail_pos hRV
  have hatop := tendsto_normSeq hRV
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower bound: `n G(aₙ) ≥ G(aₙ) / G(r aₙ) → r ^ α` for `r < 1`
    obtain ⟨r, hr0, hr1, hbr⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ b < r ^ α := by
      have hc : Tendsto (fun r : ℝ => r ^ α) (𝓝[<] 1) (𝓝 1) := by
        have := (Real.continuousAt_rpow_const 1 α (Or.inl one_ne_zero)).tendsto
        rw [Real.one_rpow] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h1 := (hc.eventually (lt_mem_nhds hb)).and (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos))
      obtain ⟨r, hr, hr'⟩ := h1.exists
      exact ⟨r, hr'.1, hr'.2, hr⟩
    have hlim := (hRV.2 r hr0).comp hatop
    have hlim' : Tendsto (fun n => absTail μ (normSeq μ n) / absTail μ (r * normSeq μ n)) atTop
        (𝓝 (r ^ α)) := by
      have := hlim.inv₀ (Real.rpow_pos_of_pos hr0 _).ne'
      rw [Real.rpow_neg hr0.le, inv_inv] at this
      exact this.congr fun n => by simp [Function.comp, inv_div]
    filter_upwards [(tendsto_order.1 hlim').1 b hbr, normSeq_spec hRV 1,
      eventually_gt_atTop 0] with n hn hs hn0'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn0'
    obtain ⟨h1, -, h3⟩ := hs
    have hlt := h3 (r * normSeq μ n) (by nlinarith)
    refine hn.trans_le ?_
    rw [div_le_iff₀ (hpos _)]
    calc absTail μ (normSeq μ n) = (n : ℝ) * absTail μ (normSeq μ n) * (n : ℝ)⁻¹ := by
          field_simp
      _ ≤ (n : ℝ) * absTail μ (normSeq μ n) * absTail μ (r * normSeq μ n) :=
          mul_le_mul_of_nonneg_left hlt.le (mul_nonneg hn0.le (hpos _).le)
  · filter_upwards [normSeq_spec hRV 0, eventually_gt_atTop 0] with n hn hn0
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    calc (n : ℝ) * absTail μ (normSeq μ n) ≤ (n : ℝ) * (n : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hn.2.1 this.le
      _ = 1 := by field_simp
      _ < b := hb

omit hRV in
/-- A positive version of a sequence, equal to it eventually when it tends to `∞`. -/
theorem exists_pos_eventuallyEq {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    ∃ a' : ℕ → ℝ, (∀ n, 0 < a' n) ∧ a' =ᶠ[atTop] a := by
  refine ⟨fun n => if 0 < a n then a n else 1, fun n => ?_, ?_⟩
  · dsimp only; split_ifs with h
    · exact h
    · exact one_pos
  · filter_upwards [ha.eventually_gt_atTop 0] with n hn
    simp [hn]

/-- **Generalized CLT with the canonical normalization** (symmetric case): if `μ` is symmetric
and `P(|X| > ·)` is regularly varying with index `-α`, `0 < α < 2`, then with
`aₙ = inf {x : P(|X| > x) ≤ 1 / n}` the laws of `Sₙ / aₙ` converge weakly to the symmetric
`α`-stable law with characteristic function `exp (-C_α |t| ^ α)`. -/
theorem tendsto_map_convPow_normSeq (hsymm : μ.map (fun x => -x) = μ) (hα0 : 0 < α)
    (hα2 : α < 2) :
    ∃ ν : ProbabilityMeasure ℝ, IsSymmStable α (StableIntegral.stableConst α) (ν : Measure ℝ) ∧
      Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map ((normSeq μ n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν) := by
  obtain ⟨a', ha', hea⟩ := exists_pos_eventuallyEq (tendsto_normSeq hRV)
  have hna : Tendsto (fun n : ℕ => (n : ℝ) * absTail μ (a' n)) atTop (𝓝 1) :=
    (tendsto_mul_absTail_normSeq hRV).congr' (hea.mono fun n hn => by simp [hn])
  obtain ⟨ν, hν, hlim⟩ := tendsto_map_convPow_of_isRegularlyVarying hsymm hα0 hα2 hRV ha' hna
  refine ⟨ν, hν, hlim.congr' (hea.mono fun n hn => ?_)⟩
  exact Subtype.ext (by simp only [hn])

end NormSeq

section FellerIff

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}

/-- **Feller's criterion for the domain of attraction of a symmetric stable law**
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2], symmetric case). Let `μ` be
symmetric and `0 < α < 2`. There are `aₙ > 0` such that `Sₙ / aₙ` converges weakly to a
symmetric `α`-stable law `SαS(c)`, `c > 0`, if and only if `P(|X| > ·)` is regularly varying with
index `-α`; and then `aₙ = inf {x : P(|X| > x) ≤ 1 / n}` works, with limit `SαS(C_α)`
(`tendsto_map_convPow_normSeq`). -/
theorem domainOfAttraction_isSymmStable_iff (hsymm : μ.map (fun x => -x) = μ) (hα0 : 0 < α)
    (hα2 : α < 2) :
    (∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ ∃ c > 0, ∃ ν : ProbabilityMeasure ℝ,
      IsSymmStable α c (ν : Measure ℝ) ∧ Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
        ⟨(convPow μ n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop (𝓝 ν)) ↔
      IsRegularlyVarying (absTail μ) (-α) := by
  refine ⟨fun h => (isRegularlyVarying_truncSecondMoment_of_domainOfAttraction hsymm hα0 hα2
    h).2, fun hRV => ?_⟩
  obtain ⟨a', ha', hea⟩ := exists_pos_eventuallyEq (tendsto_normSeq hRV)
  obtain ⟨ν, hν, hlim⟩ := tendsto_map_convPow_normSeq hRV hsymm hα0 hα2
  refine ⟨a', ha', _, StableIntegral.stableConst_pos hα0 hα2, ν, hν,
    hlim.congr' (hea.mono fun n hn => ?_)⟩
  exact Subtype.ext (by simp only [hn])

end FellerIff

section Symmetrization

/-- The symmetrization of `μ`: the law of `X - X'`, with `X, X'` independent with law `μ`. -/
noncomputable def symmLaw (μ : Measure ℝ) : Measure ℝ := (μ.prod μ).map (fun p => p.1 - p.2)

theorem measurable_fst_sub_snd : Measurable (fun p : ℝ × ℝ => p.1 - p.2) :=
  measurable_fst.sub measurable_snd

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

instance : IsProbabilityMeasure (symmLaw μ) := by
  unfold symmLaw; infer_instance

theorem symmLaw_map_neg : (symmLaw μ).map (fun x => -x) = symmLaw μ := by
  rw [symmLaw, Measure.map_map measurable_neg measurable_fst_sub_snd]
  conv_rhs => rw [← Measure.prod_swap]
  rw [Measure.map_map measurable_fst_sub_snd measurable_swap]
  congr 1
  funext p
  simp

theorem charFun_symmLaw (t : ℝ) :
    charFun (symmLaw μ) t = ((Complex.normSq (charFun μ t) : ℝ) : ℂ) := by
  rw [charFun_apply_real, symmLaw,
    integral_map measurable_fst_sub_snd.aemeasurable (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, Complex.exp (t * ((p.1 - p.2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (t * (p.1 : ℂ) * Complex.I) *
        Complex.exp (((-t : ℝ) : ℂ) * (p.2 : ℂ) * Complex.I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => Complex.exp (t * (x : ℂ) * Complex.I))
    (fun y : ℝ => Complex.exp (((-t : ℝ) : ℂ) * (y : ℂ) * Complex.I)),
    ← charFun_apply_real, ← charFun_apply_real, charFun_neg, Complex.mul_conj]

/-- The symmetrization of a law which is not a Dirac mass is not `δ₀`. -/
theorem symmLaw_ne_dirac {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h : ∀ x, ν ≠ Measure.dirac x) : symmLaw ν ≠ Measure.dirac 0 := by
  intro hd
  have hS : MeasurableSet ({0}ᶜ : Set ℝ) := (measurableSet_singleton 0).compl
  have h0 : symmLaw ν {0}ᶜ = 0 := by rw [hd]; simp
  rw [symmLaw, Measure.map_apply measurable_fst_sub_snd hS,
    Measure.prod_apply (measurable_fst_sub_snd hS)] at h0
  rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left (measurable_fst_sub_snd hS))] at h0
  obtain ⟨x, hx⟩ := h0.exists
  have hx' : ν {x}ᶜ = 0 := by
    convert hx using 2
    ext y
    simp [sub_eq_zero, eq_comm]
  apply h x
  have h1 : ν {x} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton x)).1 hx'
  rw [← Measure.restrict_eq_self_of_ae_mem (μ := ν) (s := {x}) (by
    rw [ae_iff]; convert hx' using 2), Measure.restrict_singleton, h1, one_smul]

/-- If `(Sₙ - bₙ) / aₙ → ν`, then the symmetrized sums `(Sₙ - S'ₙ) / aₙ` converge to the
symmetrization of `ν`. -/
theorem tendsto_map_convPow_symmLaw {a b : ℕ → ℝ} {ν : ProbabilityMeasure ℝ}
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow (symmLaw μ) n).map ((a n)⁻¹ * ·), inferInstance⟩) atTop
      (𝓝 ⟨symmLaw (ν : Measure ℝ), inferInstance⟩) := by
  have hcf := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hconv
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  have h := ((Complex.continuous_ofReal.comp Complex.continuous_normSq).tendsto _).comp
    (hcf t)
  simp only [ProbabilityMeasure.coe_mk, charFun_symmLaw] at h ⊢
  refine h.congr fun n => ?_
  simp only [Function.comp]
  have hf : (fun x => (a n)⁻¹ * (x - b n)) = fun x => (a n)⁻¹ * x + (-((a n)⁻¹ * b n)) := by
    funext x; ring
  rw [hf, charFun_map_mul_add, charFun_map_mul, charFun_convPow, charFun_convPow,
    charFun_symmLaw, map_mul, map_pow, Complex.normSq_eq_norm_sq (Complex.exp _),
    show (((-((a n)⁻¹ * b n) : ℝ) : ℂ) * (t : ℂ) * Complex.I) =
      ((-((a n)⁻¹ * b n) * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]
  push_cast
  ring

omit [IsProbabilityMeasure μ] in
theorem absTail_symmLaw (r : ℝ) :
    absTail (symmLaw μ) r = (μ.prod μ).real {p : ℝ × ℝ | r < |p.1 - p.2|} := by
  rw [absTail, symmLaw, measureReal_def, measureReal_def,
    Measure.map_apply measurable_fst_sub_snd (measurableSet_abs_gt r)]
  rfl

theorem measureReal_prod_prod (A B : Set ℝ) :
    (μ.prod μ).real (A ×ˢ B) = μ.real A * μ.real B := by
  rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]; rfl

theorem measurableSet_abs_le' (u : ℝ) : MeasurableSet {y : ℝ | |y| ≤ u} :=
  measurableSet_le continuous_abs.measurable measurable_const

/-- **Weak symmetrization inequality, lower bound**: `2 P(|X| > s + u) P(|X| ≤ u) ≤
P(|X - X'| > s)`. -/
theorem two_mul_absTail_mul_le_absTail_symmLaw {s u : ℝ} (hs : 0 ≤ s) :
    2 * absTail μ (s + u) * (1 - absTail μ u) ≤ absTail (symmLaw μ) s := by
  set A := {y : ℝ | s + u < |y|}
  set B := {y : ℝ | |y| ≤ u}
  have hA : MeasurableSet A := measurableSet_abs_gt _
  have hB : MeasurableSet B := measurableSet_abs_le' _
  have hBc : μ.real B = 1 - absTail μ u := by
    have : B = {y : ℝ | u < |y|}ᶜ := by ext y; simp [B]
    rw [this, probReal_compl_eq_one_sub (measurableSet_abs_gt u)]; rfl
  have hdisj : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, -⟩ ⟨hx', -⟩
    simp only [A, B, mem_ofPred_eq] at hx hx'
    linarith
  have hsub : A ×ˢ B ∪ B ×ˢ A ⊆ {p : ℝ × ℝ | s < |p.1 - p.2|} := by
    rintro ⟨x, y⟩ (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> simp only [A, B, mem_ofPred_eq] at hx hy ⊢
    · have := abs_sub_abs_le_abs_sub x y; linarith
    · have := abs_sub_abs_le_abs_sub y x; rw [abs_sub_comm] at this; linarith
  rw [absTail_symmLaw]
  calc 2 * absTail μ (s + u) * (1 - absTail μ u)
      = (μ.prod μ).real (A ×ˢ B ∪ B ×ˢ A) := by
        rw [measureReal_union hdisj (hB.prod hA), measureReal_prod_prod, measureReal_prod_prod,
          hBc]
        simp only [absTail, A]; ring
    _ ≤ _ := measureReal_mono hsub

/-- **Weak symmetrization inequality, upper bound** (one big jump): `P(|X - X'| > s + u) ≤
2 P(|X| > s) + P(|X| > u)²`. -/
theorem absTail_symmLaw_le {s u : ℝ} :
    absTail (symmLaw μ) (s + u) ≤ 2 * absTail μ s + absTail μ u ^ 2 := by
  set A := {y : ℝ | s < |y|}
  set C := {y : ℝ | u < |y|}
  have hsub : {p : ℝ × ℝ | s + u < |p.1 - p.2|} ⊆
      (A ×ˢ univ ∪ univ ×ˢ A) ∪ C ×ˢ C := by
    rintro ⟨x, y⟩ h
    simp only [A, C, mem_ofPred_eq, mem_union, mem_prod, mem_univ, and_true, true_and] at h ⊢
    by_contra hc
    push Not at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have h4 := abs_sub x y
    rcases le_or_gt |x| u with h5 | h5
    · linarith
    · linarith [h3 h5]
  rw [absTail_symmLaw]
  calc _ ≤ (μ.prod μ).real ((A ×ˢ univ ∪ univ ×ˢ A) ∪ C ×ˢ C) := measureReal_mono hsub
    _ ≤ (μ.prod μ).real (A ×ˢ univ) + (μ.prod μ).real (univ ×ˢ A) +
        (μ.prod μ).real (C ×ˢ C) :=
      (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ = _ := by
      rw [measureReal_prod_prod, measureReal_prod_prod, measureReal_prod_prod]
      simp only [probReal_univ, absTail, A, C]; ring

end Symmetrization

section TailComparison

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}

theorem tendsto_one_add_rpow (β : ℝ) :
    Tendsto (fun ε : ℝ => (1 + ε) ^ β) (𝓝[>] 0) (𝓝 1) := by
  have h : ContinuousAt (fun ε : ℝ => (1 + ε) ^ β) 0 :=
    (continuous_const.add continuous_id).continuousAt.rpow_const (Or.inl (by norm_num))
  have := h.tendsto
  simp only [add_zero, Real.one_rpow] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- Choose `ε ∈ (0, 1)` with `(1 + ε) ^ β` close to `1`. -/
theorem exists_one_add_rpow_mem {β : ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 (1 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1 + ε) ^ β ∈ U := by
  obtain ⟨ε, h1, h2⟩ := (((tendsto_one_add_rpow β).eventually hU).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos))).exists
  exact ⟨ε, h2.1, h2.2, h1⟩

/-- Eventually `P(|X| > 2x) ≤ P(|X - X'| > x)`. -/
theorem eventually_absTail_two_mul_le :
    ∀ᶠ x in atTop, absTail μ (2 * x) ≤ absTail (symmLaw μ) x := by
  filter_upwards [(tendsto_order.1 (tendsto_absTail_zero (μ := μ))).2 (1 / 2) (by norm_num),
    eventually_ge_atTop 0] with x hx hx0
  have h := two_mul_absTail_mul_le_absTail_symmLaw (μ := μ) (s := x) (u := x) hx0
  rw [show x + x = 2 * x by ring] at h
  have h0 : 0 ≤ absTail μ (2 * x) := measureReal_nonneg
  nlinarith

/-- **Tails of the symmetrization**: if `P(|X - X'| > ·)` is regularly varying with index
`-α`, `α > 0`, then `P(|X| > x) / P(|X - X'| > x) → 1 / 2`. -/
theorem tendsto_absTail_div_absTail_symmLaw
    (hRV : IsRegularlyVarying (absTail (symmLaw μ)) (-α)) :
    Tendsto (fun x => absTail μ x / absTail (symmLaw μ) x) atTop (𝓝 (1 / 2)) := by
  have hGs : ∀ x, 0 < absTail (symmLaw μ) x := absTail_pos hRV
  have hG0 := tendsto_absTail_zero (μ := μ)
  have hGs0 := tendsto_absTail_zero (μ := symmLaw μ)
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower bound, from `P(|X - X'| > (1 + ε) x) ≤ 2 P(|X| > x) + P(|X| > ε x)²`
    obtain ⟨ε, hε0, -, hε⟩ := exists_one_add_rpow_mem (β := -α)
      (Ioi_mem_nhds (show 2 * b < 1 by linarith))
    have hε : 2 * b < (1 + ε) ^ (-α) := hε
    have hsq : Tendsto (fun x => absTail μ (ε * x) ^ 2 / absTail (symmLaw μ) x) atTop (𝓝 0) := by
      have hup : Tendsto (fun x => absTail (symmLaw μ) (ε / 2 * x) *
          (absTail (symmLaw μ) (ε / 2 * x) / absTail (symmLaw μ) x)) atTop
          (𝓝 (0 * (ε / 2) ^ (-α))) :=
        (hGs0.comp (tendsto_id.const_mul_atTop (by positivity))).mul
          (hRV.2 _ (by positivity))
      rw [zero_mul] at hup
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (hGs x).le) ?_
      filter_upwards [(tendsto_id.const_mul_atTop (show 0 < ε / 2 by positivity)).eventually
        (eventually_absTail_two_mul_le (μ := μ))] with x hx
      simp only [id] at hx
      rw [show 2 * (ε / 2 * x) = ε * x by ring] at hx
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right (hGs x), sq]
      exact mul_le_mul hx hx measureReal_nonneg (hGs _).le
    have hlim : Tendsto (fun x => (absTail (symmLaw μ) ((1 + ε) * x) / absTail (symmLaw μ) x -
        absTail μ (ε * x) ^ 2 / absTail (symmLaw μ) x) / 2) atTop
        (𝓝 (((1 + ε) ^ (-α) - 0) / 2)) :=
      ((hRV.2 _ (by positivity)).sub hsq).div_const 2
    filter_upwards [(tendsto_order.1 hlim).1 b (by linarith)] with x hx
    refine hx.trans_le ?_
    have h := absTail_symmLaw_le (μ := μ) (s := x) (u := ε * x)
    rw [show x + ε * x = (1 + ε) * x by ring] at h
    rw [div_le_div_iff₀ two_pos (hGs x), ← sub_div, div_mul_eq_mul_div,
      div_le_iff₀ (hGs x)]
    nlinarith [hGs x]
  · -- upper bound, from `2 P(|X| > x) P(|X| ≤ u) ≤ P(|X - X'| > x - u)`
    obtain ⟨ε, hε0, -, hε⟩ := exists_one_add_rpow_mem (β := α)
      (Iio_mem_nhds (show 1 < 2 * b by linarith))
    have hε : (1 + ε) ^ α < 2 * b := hε
    set c := (1 + ε)⁻¹ with hc
    have hc0 : 0 < c := by positivity
    have hlim : Tendsto (fun x => absTail (symmLaw μ) (c * x) / absTail (symmLaw μ) x /
        (2 * (1 - absTail μ (ε * c * x)))) atTop (𝓝 (c ^ (-α) / (2 * (1 - 0)))) :=
      (hRV.2 c hc0).div ((hG0.comp (tendsto_id.const_mul_atTop (by positivity))).const_sub 1
        |>.const_mul 2) (by norm_num)
    have hcα : c ^ (-α) = (1 + ε) ^ α := by
      rw [hc, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
    rw [hcα] at hlim
    filter_upwards [(tendsto_order.1 hlim).2 b (by linarith), eventually_ge_atTop 0,
      (tendsto_id.const_mul_atTop (show 0 < ε * c by positivity)).eventually
        ((tendsto_order.1 hG0).2 (1 / 2) (by norm_num))] with x hx hx0 hu
    simp only [id] at hu
    refine lt_of_le_of_lt ?_ hx
    have h := two_mul_absTail_mul_le_absTail_symmLaw (μ := μ) (s := c * x) (u := ε * c * x)
      (by positivity)
    rw [show c * x + ε * c * x = x by rw [hc]; field_simp] at h
    have h1 : 0 < 1 - absTail μ (ε * c * x) := by linarith
    rw [div_div, le_div_iff₀ (mul_pos (hGs x) (mul_pos two_pos h1)), div_mul_eq_mul_div, div_le_iff₀ (hGs x)]
    nlinarith [hGs x, hGs (c * x)]

/-- If the symmetrized tail is regularly varying with index `-α`, `α > 0`, so is the tail. -/
theorem isRegularlyVarying_absTail_of_symmLaw
    (hRV : IsRegularlyVarying (absTail (symmLaw μ)) (-α)) :
    IsRegularlyVarying (absTail μ) (-α) :=
  hRV.of_tendsto_div (tendsto_absTail_div_absTail_symmLaw hRV) (by norm_num)

theorem min_sq_sub_le_two (x a b : ℝ) :
    min (x ^ 2) ((a - b) ^ 2) ≤ 2 * min (x ^ 2) (a ^ 2) + 2 * min (x ^ 2) (b ^ 2) := by
  rcases le_total (x ^ 2) (a ^ 2) with h1 | h1 <;> rcases le_total (x ^ 2) (b ^ 2) with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2]; nlinarith [min_le_left (x ^ 2) ((a - b) ^ 2), sq_nonneg x]
  · rw [min_eq_left h1, min_eq_right h2]
    nlinarith [min_le_left (x ^ 2) ((a - b) ^ 2), sq_nonneg b]
  · rw [min_eq_right h1, min_eq_left h2]
    nlinarith [min_le_left (x ^ 2) ((a - b) ^ 2), sq_nonneg a]
  · rw [min_eq_right h1, min_eq_right h2]
    nlinarith [min_le_right (x ^ 2) ((a - b) ^ 2), sq_nonneg (a + b)]

/-- `E[min (x², (X - X')²)] ≤ 4 E[min (x², X²)]`. -/
theorem minSqMoment_symmLaw_le (x : ℝ) :
    minSqMoment (symmLaw μ) x ≤ 4 * minSqMoment μ x := by
  rw [minSqMoment, symmLaw, integral_map measurable_fst_sub_snd.aemeasurable (by fun_prop)]
  have hi : ∀ (f : ℝ × ℝ → ℝ), Measurable f →
      Integrable (fun p : ℝ × ℝ => min (x ^ 2) (f p ^ 2)) (μ.prod μ) := by
    intro f hf
    refine (integrable_const (x ^ 2)).mono' (by fun_prop) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg _))]
    exact min_le_left _ _
  calc ∫ p : ℝ × ℝ, min (x ^ 2) ((p.1 - p.2) ^ 2) ∂μ.prod μ
      ≤ ∫ p : ℝ × ℝ, (2 * min (x ^ 2) (p.1 ^ 2) + 2 * min (x ^ 2) (p.2 ^ 2)) ∂μ.prod μ :=
        integral_mono (hi _ measurable_fst_sub_snd)
          (((hi _ measurable_fst).const_mul 2).add ((hi _ measurable_snd).const_mul 2))
          fun p => min_sq_sub_le_two x p.1 p.2
    _ = 4 * minSqMoment μ x := by
        rw [integral_add ((hi _ measurable_fst).const_mul 2) ((hi _ measurable_snd).const_mul 2),
          integral_const_mul, integral_const_mul,
          integral_fun_fst (fun y : ℝ => min (x ^ 2) (y ^ 2)),
          integral_fun_snd (fun y : ℝ => min (x ^ 2) (y ^ 2))]
        simp only [probReal_univ, one_smul, minSqMoment]
        ring

/-- **The Gaussian case**: if `E[min (x², (X - X')²)]` is slowly varying, so is
`E[min (x², X²)]`. -/
theorem isRegularlyVarying_minSqMoment_of_symmLaw
    (hZs : IsRegularlyVarying (minSqMoment (symmLaw μ)) 0) :
    IsRegularlyVarying (minSqMoment μ) 0 := by
  have hZpos : ∀ᶠ x in atTop, 0 < minSqMoment μ x := by
    filter_upwards [hZs.1] with x hx
    linarith [minSqMoment_symmLaw_le (μ := μ) x]
  -- `x² P(|X| > x) / Z(x) → 0`
  have hr : Tendsto (fun x => x ^ 2 * absTail μ x / minSqMoment μ x) atTop (𝓝 0) := by
    have h1 := (tendsto_sq_mul_absTail_div_minSqMoment hZs).comp
      (tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
    have h2 := hZs.2 (1 / 2) (by norm_num)
    rw [zero_div] at h1
    have h3 : Tendsto (fun x => 16 * (((1 / 2 * x) ^ 2 * absTail (symmLaw μ) (1 / 2 * x) /
        minSqMoment (symmLaw μ) (1 / 2 * x)) * (minSqMoment (symmLaw μ) (1 / 2 * x) /
        minSqMoment (symmLaw μ) x))) atTop (𝓝 (16 * (0 * (1 / 2) ^ (0 : ℝ)))) :=
      (h1.mul h2).const_mul 16
    rw [zero_mul, mul_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3 ?_ ?_
    · filter_upwards [hZpos] with x hx
      exact div_nonneg (mul_nonneg (sq_nonneg _) measureReal_nonneg) hx.le
    · filter_upwards [hZpos, hZs.1, (tendsto_id.const_mul_atTop
        (show (0 : ℝ) < 1 / 2 by norm_num)).eventually hZs.1,
        (tendsto_id.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually
          (eventually_absTail_two_mul_le (μ := μ))] with x hx hxs hxs' hG
      simp only [id] at hxs' hG
      rw [show 2 * (1 / 2 * x) = x by ring] at hG
      have h4 := minSqMoment_symmLaw_le (μ := μ) x
      rw [div_mul_div_cancel₀ hxs'.ne', div_le_iff₀ hx]
      calc x ^ 2 * absTail μ x ≤ x ^ 2 * absTail (symmLaw μ) (1 / 2 * x) :=
            mul_le_mul_of_nonneg_left hG (sq_nonneg _)
        _ = 16 * ((1 / 2 * x) ^ 2 * absTail (symmLaw μ) (1 / 2 * x) /
              minSqMoment (symmLaw μ) x) * (minSqMoment (symmLaw μ) x / 4) := by
            field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (by norm_num) (div_nonneg (mul_nonneg (sq_nonneg _) measureReal_nonneg)
              hxs.le))
  -- hence `Z(l x) / Z(x) → 1` for `l ≥ 1`
  have hge : ∀ l : ℝ, 1 ≤ l →
      Tendsto (fun x => minSqMoment μ (l * x) / minSqMoment μ x) atTop (𝓝 1) := by
    intro l hl
    have hup : Tendsto (fun x => 1 + (l ^ 2 - 1) * (x ^ 2 * absTail μ x / minSqMoment μ x))
        atTop (𝓝 (1 + (l ^ 2 - 1) * 0)) := (hr.const_mul _).const_add 1
    rw [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hZpos, eventually_ge_atTop 0] with x hx hx0
      rw [le_div_iff₀ hx, one_mul]
      exact minSqMoment_mono hx0 (le_mul_of_one_le_left hx0 hl)
    · filter_upwards [hZpos, eventually_ge_atTop 0] with x hx hx0
      have := minSqMoment_sub_le (μ := μ) hx0 hl
      rw [div_le_iff₀ hx, add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hx.ne']
      nlinarith
  refine ⟨hZpos, fun l hl => ?_⟩
  rw [Real.rpow_zero]
  rcases le_total 1 l with h1 | h1
  · exact hge l h1
  · have h := (hge l⁻¹ (one_le_inv₀ hl |>.2 h1)).comp (tendsto_id.const_mul_atTop hl)
    have h' := h.inv₀ one_ne_zero
    rw [inv_one] at h'
    refine h'.congr' ?_
    filter_upwards with x
    simp only [Function.comp, id, inv_div]
    rw [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]

end TailComparison

section Converse

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {a b : ℕ → ℝ}

/-- The symmetrized form of the hypotheses: if `(Sₙ - bₙ) / aₙ → ν`, `ν` not a Dirac mass, then
there are `0 < α ≤ 2` and `K > 0` with `n E[min (1, (X - X')² / (aₙ x)²)] → K x ^ (-α)`. -/
theorem exists_tendsto_mul_sqRatio_symmLaw (ha : ∀ n, 0 < a n) {ν : ProbabilityMeasure ℝ}
    (hnd : ∀ x, (ν : Measure ℝ) ≠ Measure.dirac x)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 2 ∧ ∃ K > 0, ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => (n : ℝ) * sqRatio (symmLaw μ) (a n * x)) atTop
        (𝓝 (K * x ^ (-α))) :=
  exists_tendsto_mul_sqRatio_of_tendsto (ν := ⟨symmLaw (ν : Measure ℝ), inferInstance⟩)
    symmLaw_map_neg ha (symmLaw_ne_dirac hnd) (tendsto_map_convPow_symmLaw hconv)

/-- **Converse of the generalized central limit theorem, regular-variation part**
([Feller, Vol. II, §XVII.5, Theorem 2], [GK, §35, Theorem 2]). Let `aₙ > 0`, `bₙ ∈ ℝ`, and
suppose the laws of `(X₁ + ⋯ + Xₙ - bₙ) / aₙ` converge weakly to a law `ν` which is not a Dirac
mass. Then there is `0 < α ≤ 2` such that the truncated second moment
`U(x) = E[X² 1{|X| ≤ x}]` is regularly varying with index `2 - α`, and, if `α < 2`, the
two-sided tail `P(|X| > x)` is regularly varying with index `-α`. No symmetry is assumed: the
proof symmetrizes (`X - X'`), applies the symmetric converse, and transfers back with the weak
symmetrization inequalities. -/
theorem exists_isRegularlyVarying_of_tendsto_sub (ha : ∀ n, 0 < a n)
    {ν : ProbabilityMeasure ℝ} (hnd : ∀ x, (ν : Measure ℝ) ≠ Measure.dirac x)
    (hconv : Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ =>
      ⟨(convPow μ n).map (fun x => (a n)⁻¹ * (x - b n)), inferInstance⟩) atTop (𝓝 ν)) :
    ∃ α, 0 < α ∧ α ≤ 2 ∧ IsRegularlyVarying (truncSecondMoment μ) (2 - α) ∧
      (α < 2 → IsRegularlyVarying (absTail μ) (-α)) := by
  obtain ⟨α, hα0, hα2, K, hK, hL⟩ := exists_tendsto_mul_sqRatio_symmLaw ha hnd hconv
  have hZs := isRegularlyVarying_minSqMoment_of_tendsto_mul_sqRatio ha hK hL
  rcases lt_or_eq_of_le hα2 with hlt | heq
  · have hGs := isRegularlyVarying_absTail_of_minSqMoment (by linarith) hZs
    rw [show 2 - α - 2 = -α by ring] at hGs
    have hG := isRegularlyVarying_absTail_of_symmLaw hGs
    exact ⟨α, hα0, hα2, isRegularlyVarying_truncSecondMoment_of_absTail hα0 hlt hG,
      fun _ => hG⟩
  · subst heq
    refine ⟨2, hα0, le_rfl, ?_, fun h => absurd h (lt_irrefl _)⟩
    rw [sub_self] at hZs ⊢
    exact isRegularlyVarying_truncSecondMoment_of_minSqMoment (by norm_num)
      (isRegularlyVarying_minSqMoment_of_symmLaw hZs)

end Converse

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
  obtain ⟨hGs, -, hBs⟩ := isRegularlyVarying_of_tendsto_mul_sqRatio (μ := symmLaw μ) ha hK hα0
    hlt hL
  have hG := isRegularlyVarying_absTail_of_symmLaw hGs
  refine ⟨α, hα0, hα2, isRegularlyVarying_truncSecondMoment_of_absTail hα0 hlt hG,
    fun _ => ⟨hG, ?_⟩⟩
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
