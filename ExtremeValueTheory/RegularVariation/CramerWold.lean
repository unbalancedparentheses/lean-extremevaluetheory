/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.Multivariate
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Half-spaces determine homogeneous measures (converse Cramér–Wold, uniqueness part)
-/

open MeasureTheory Filter Topology Set Complex
open scoped ENNReal NNReal fwdDiff

namespace ExtremeValueTheory

namespace CramerWold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ ν : Measure E}

omit [MeasurableSpace E] [BorelSpace E] in
theorem setOf_lt_apply_eq {s : ℝ} (hs : 0 < s) (M : StrongDual ℝ E) :
    {y : E | s < M y} = {y | 1 < (s⁻¹ • M) y} := by
  ext y
  simp only [mem_ofPred_eq, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [lt_inv_mul_iff₀ hs, mul_one]

/-- If `μ` and `ν` agree (with finite values) on all half-spaces `{L > 1}`, the images of `μ` and
`ν` under any continuous linear functional agree on `(0, ∞)`. -/
theorem map_restrict_Ioi_eq (hfin : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} < ∞)
    (h : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ν {y | 1 < L y}) (M : StrongDual ℝ E) :
    (μ.map M).restrict (Ioi 0) = (ν.map M).restrict (Ioi 0) := by
  have hIoi : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1)) := by
    ext s
    simp only [mem_Ioi, mem_iUnion]
    refine ⟨fun hs => ?_, fun ⟨n, hn⟩ => lt_trans (by positivity) hn⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hs
    exact ⟨n, hn⟩
  have hval : ∀ (ρ : Measure E) {s : ℝ}, 0 < s → (ρ.map M) (Ioi s) = ρ {y | 1 < (s⁻¹ • M) y} :=
    fun ρ s hs => by
      rw [Measure.map_apply M.measurable measurableSet_Ioi, ← setOf_lt_apply_eq hs]; rfl
  rw [hIoi, Measure.restrict_iUnion_congr]
  intro n
  set c : ℝ := 1 / ((n : ℝ) + 1)
  have hc : 0 < c := by positivity
  have hval' : ∀ (ρ : Measure E) (a : ℝ), ((ρ.map M).restrict (Ioi c)) (Ioi a) =
      ρ {y | 1 < ((max a c)⁻¹ • M) y} := fun ρ a => by
    rw [Measure.restrict_apply measurableSet_Ioi, Ioi_inter_Ioi, hval ρ (lt_max_of_lt_right hc)]
  have : IsFiniteMeasure ((μ.map M).restrict (Ioi c)) :=
    ⟨by rw [Measure.restrict_apply_univ, hval μ hc]; exact hfin _⟩
  have : IsFiniteMeasure ((ν.map M).restrict (Ioi c)) :=
    ⟨by rw [Measure.restrict_apply_univ, hval ν hc, ← h]; exact hfin _⟩
  refine measure_ext_of_Ioi ?_ fun a => by rw [hval', hval', h]
  rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ, hval μ hc, hval ν hc, h]

/-- Integrals over a half-space `{M > 0}` of functions of `M y` agree. -/
theorem setIntegral_pos_eq (hfin : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} < ∞)
    (h : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ν {y | 1 < L y}) (M : StrongDual ℝ E)
    {G : ℝ → ℂ} (hG : Measurable G) :
    ∫ y in {y | 0 < M y}, G (M y) ∂μ = ∫ y in {y | 0 < M y}, G (M y) ∂ν := by
  have h1 : ∀ ρ : Measure E, ∫ y in {y | 0 < M y}, G (M y) ∂ρ = ∫ s in Ioi 0, G s ∂(ρ.map M) :=
    fun ρ => (setIntegral_map measurableSet_Ioi hG.aestronglyMeasurable
      M.measurable.aemeasurable).symm
  rw [h1, h1, map_restrict_Ioi_eq hfin h M]

/-- **Integrals of functions of linear functionals agree**: if `μ` and `ν` agree on all
half-spaces `{L > 1}`, then `∫ G (M y) dμ = ∫ G (M y) dν` for every continuous linear `M` and
every measurable `G` with `G 0 = 0` such that `G ∘ M` is integrable for both measures. -/
theorem integral_comp_eq (hfin : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} < ∞)
    (h : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ν {y | 1 < L y}) (M : StrongDual ℝ E)
    {G : ℝ → ℂ} (hG : Measurable G) (hG0 : G 0 = 0)
    (hμ : Integrable (fun y => G (M y)) μ) (hν : Integrable (fun y => G (M y)) ν) :
    ∫ y, G (M y) ∂μ = ∫ y, G (M y) ∂ν := by
  have key : ∀ ρ : Measure E, Integrable (fun y => G (M y)) ρ → ∫ y, G (M y) ∂ρ =
      ∫ y in {y | 0 < M y}, G (M y) ∂ρ +
        ∫ y in {y | 0 < (-M) y}, (fun s => G (-s)) ((-M) y) ∂ρ := fun ρ hρ => by
    have hm : MeasurableSet {y : E | 0 < M y} := measurableSet_lt measurable_const M.measurable
    rw [← integral_add_compl hm hρ]
    congr 1
    have hsub : {y : E | 0 < (-M) y} ⊆ {y | 0 < M y}ᶜ := fun y hy => by
      simp only [neg_apply, mem_ofPred_eq, Left.neg_pos_iff] at hy
      simp only [mem_compl_iff, mem_ofPred_eq, not_lt]; exact hy.le
    simp only [neg_apply, neg_neg]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hm.compl hsub ?_
    intro y ⟨hy1, hy2⟩
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt, Left.neg_pos_iff] at hy1 hy2
    rw [le_antisymm hy1 hy2, hG0]
  rw [key μ hμ, key ν hν, setIntegral_pos_eq hfin h M hG,
    setIntegral_pos_eq hfin h (-M) (G := fun s => G (-s)) (hG.comp measurable_neg)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] in
/-- If `f μ = f ν` for a finite measurable density `f`, then `μ` and `ν` agree on `{f ≠ 0}`. -/
theorem restrict_ne_zero_eq_of_withDensity_eq {f : E → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∀ y, f y ≠ ∞) (h : μ.withDensity f = ν.withDensity f) :
    μ.restrict {y | f y ≠ 0} = ν.restrict {y | f y ≠ 0} := by
  have hset : MeasurableSet {y | f y ≠ 0} := (hf (measurableSet_singleton 0)).compl
  have key : ∀ ρ : Measure E, ρ.restrict {y | f y ≠ 0} = (ρ.withDensity f).withDensity f⁻¹ :=
    fun ρ => by
      rw [← withDensity_mul ρ hf hf.inv, ← withDensity_indicator_one hset]
      congr 1
      funext y
      by_cases hy : f y = 0
      · simp [hy]
      · simp [hy, ENNReal.mul_inv_cancel hy (hfin y)]
  rw [key, key, h]

omit [MeasurableSpace E] [BorelSpace E] in
theorem cos_ne_one_or_cos_sqrt_two_ne_one {t : ℝ} (ht : t ≠ 0) :
    Real.cos t ≠ 1 ∨ Real.cos (√2 * t) ≠ 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff t).1 hc.1
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).1 hc.2
  have hn0 : (n : ℝ) ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hn; exact ht hn.symm
  refine irrational_sqrt_two.ne_rational m n ?_
  rw [eq_div_iff hn0]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  apply mul_right_cancel₀ hpi
  rw [mul_assoc, hn, hm]

variable [FiniteDimensional ℝ E]

/-- The coordinate functionals of a basis and their `√2`-multiples. -/
noncomputable def coordFamily (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : Fin (Module.finrank ℝ E) × Bool) : StrongDual ℝ E :=
  (if p.2 then √2 else 1) • LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord p.1)


omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_coordFamily_sin_ne_zero {y : E} (hy : y ≠ 0) :
    ∃ p, Real.sin (coordFamily E p y / 2) ≠ 0 := by
  set b := Module.finBasis ℝ E
  have : b.repr y ≠ 0 := by
    rwa [Ne, LinearEquiv.map_eq_zero_iff]
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 this
  have hc : ∀ q : Bool, coordFamily E (i, q) y = (if q then √2 else 1) * b.repr y i := fun q => by
    simp only [coordFamily, b]
    split_ifs <;> simp [Module.Basis.coord_apply]
  have hsin : ∀ t : ℝ, Real.sin (t / 2) = 0 → Real.cos t = 1 := fun t ht => by
    have h1 := Real.cos_sq (t / 2)
    have h2 := Real.sin_sq_add_cos_sq (t / 2)
    rw [ht, show 2 * (t / 2) = t by ring] at *
    linarith
  rcases cos_ne_one_or_cos_sqrt_two_ne_one hi with h1 | h2
  · exact ⟨(i, false), fun h0 => h1 (by simpa [hc] using hsin _ h0)⟩
  · exact ⟨(i, true), fun h0 => h2 (by simpa [hc] using hsin _ h0)⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Iterated forward differences of the exponential `x ↦ e^{ix}`. -/
theorem fwdDiff_iter_cexp (b a : ℝ) (N : ℕ) :
    Δ_[b]^[N] (fun x : ℝ => cexp (x * I)) a = (cexp (b * I) - 1) ^ N * cexp (a * I) := by
  have h1 : Δ_[b] (fun x : ℝ => cexp (x * I)) = (cexp (b * I) - 1) • fun x : ℝ => cexp (x * I) := by
    funext x
    simp only [fwdDiff, Pi.smul_apply, smul_eq_mul, ofReal_add, add_mul, Complex.exp_add]
    ring
  induction N generalizing a with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply, h1, fwdDiff_iter_const_smul, Pi.smul_apply, ih, smul_eq_mul]
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem cexp_sub_one_pow (b : ℝ) (m : ℕ) :
    (cexp (b * I) - 1) ^ (2 * m) =
      (-4 : ℂ) ^ m * ((Real.sin (b / 2) ^ (2 * m) : ℝ) : ℂ) * cexp ((m * b : ℝ) * I) := by
  have hsin : cexp (b * I) - 1 = 2 * I * Complex.sin (b / 2) * cexp ((b / 2 : ℝ) * I) := by
    have e1 : cexp (b * I) = cexp ((b / 2 : ℝ) * I) * cexp ((b / 2 : ℝ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : cexp (-((b / 2 : ℝ) : ℂ) * I) * cexp ((b / 2 : ℝ) * I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [Complex.sin, e1]
    push_cast at e2 ⊢
    linear_combination (-(I ^ 2)) * e2 + (cexp (↑b / 2 * I) ^ 2 - 1) * I_sq
  have hm : cexp ((m * b : ℝ) * I) = cexp ((b / 2 : ℝ) * I) ^ (2 * m) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hsin, hm, mul_pow, mul_pow, pow_mul, show (2 * I) ^ 2 = (-4 : ℂ) by
    rw [mul_pow, I_sq]; norm_num]
  push_cast
  ring



/-- **Half-spaces determine a measure** (abstract form). Let `g : ℝ → ℂ` be measurable with
`g 0 = 0` whose `2m`-th forward differences coincide with those of `x ↦ e^{ix}` (for instance
`g (x) = e^{ix} - P (x)` with `P` a polynomial of degree `< 2m`), and suppose `g ∘ M` is
integrable for `μ` and `ν` for every continuous linear `M`. If `μ` and `ν` have no atom at the
origin and agree (with finite values) on all half-spaces `{L > 1}`, then `μ = ν`.

The proof: the integrals `∫ g (M y)` agree (`integral_comp_eq`). Since
`Δ_b^{2m} e^{i·} (a) = (-4)^m sin (b / 2) ^ {2m} e^{i (a + m b)}`, the characteristic functions of
the finite measures `sin (v y / 2) ^ {2m} μ(dy)` and `sin (v y / 2) ^ {2m} ν(dy)` are finite
combinations of such integrals, so these measures are equal; `μ` and `ν` therefore agree on
`{sin (v y / 2) ≠ 0}` for every `v`, and finitely many such sets cover `E \ {0}`. -/
theorem ext_of_halfSpace {g : ℝ → ℂ} (m : ℕ) (hgm : Measurable g) (hg0 : g 0 = 0)
    (hid : ∀ a b : ℝ, Δ_[b]^[2 * m] g a = Δ_[b]^[2 * m] (fun x : ℝ => cexp (x * I)) a)
    (hμg : ∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) μ)
    (hνg : ∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) ν)
    (hμ0 : μ {0} = 0) (hν0 : ν {0} = 0)
    (hfin : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} < ∞)
    (h : ∀ L : StrongDual ℝ E, μ {y | 1 < L y} = ν {y | 1 < L y}) : μ = ν := by
  -- the combination of values of `g`
  let c : ℕ → ℤ := fun k => (-1 : ℤ) ^ ((2 * m) - k) * ((2 * m).choose k : ℤ)
  let Mk : StrongDual ℝ E → StrongDual ℝ E → ℕ → StrongDual ℝ E :=
    fun L v k => L + ((k : ℝ) - m) • v
  let S : StrongDual ℝ E → StrongDual ℝ E → E → ℂ :=
    fun L v y => ∑ k ∈ Finset.range ((2 * m) + 1), c k • g (Mk L v k y)
  have hpt : ∀ L v : StrongDual ℝ E, ∀ y : E,
      cexp (L y * I) * ((Real.sin (v y / 2) ^ (2 * m) : ℝ) : ℂ) = ((-4 : ℂ) ^ m)⁻¹ * S L v y := by
    intro L v y
    have h1 := hid (L y - m * v y) (v y)
    rw [fwdDiff_iter_cexp, cexp_sub_one_pow, fwdDiff_iter_eq_sum_shift] at h1
    have h4 : ((-4 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hS : S L v y = ∑ k ∈ Finset.range ((2 * m) + 1),
        ((-1 : ℤ) ^ ((2 * m) - k) * ((2 * m).choose k : ℤ)) • g (L y - m * v y + k • v y) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      simp only [Mk, add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul]
      ring
    have he : cexp ((m * v y : ℝ) * I) * cexp ((L y - m * v y : ℝ) * I) = cexp (L y * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hS, h1, show (-4 : ℂ) ^ m * ((Real.sin (v y / 2) ^ (2 * m) : ℝ) : ℂ) *
        cexp ((m * v y : ℝ) * I) * cexp ((L y - m * v y : ℝ) * I) =
        (-4 : ℂ) ^ m * (cexp (L y * I) * ((Real.sin (v y / 2) ^ (2 * m) : ℝ) : ℂ)) by
      rw [← he]; ring, ← mul_assoc, inv_mul_cancel₀ h4, one_mul]
  have hSint : ∀ ρ : Measure E, (∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) ρ) →
      ∀ L v, Integrable (S L v) ρ := fun ρ hρ L v =>
    integrable_finsetSum _ fun k _ => (hρ (Mk L v k)).smul (c k : ℂ) |>.congr
      (Eventually.of_forall fun y => by simp [zsmul_eq_mul])
  have hSeq : ∀ L v, ∫ y, S L v y ∂μ = ∫ y, S L v y ∂ν := fun L v => by
    simp only [S]
    rw [integral_finsetSum _ fun k _ => (hμg (Mk L v k)).smul (c k : ℂ) |>.congr
        (Eventually.of_forall fun y => by simp [zsmul_eq_mul]),
      integral_finsetSum _ fun k _ => (hνg (Mk L v k)).smul (c k : ℂ) |>.congr
        (Eventually.of_forall fun y => by simp [zsmul_eq_mul])]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [zsmul_eq_mul]
    rw [integral_const_mul, integral_const_mul,
      integral_comp_eq hfin h _ hgm hg0 (hμg _) (hνg _)]
  let w : StrongDual ℝ E → E → ℝ≥0 := fun v y => Real.toNNReal (Real.sin (v y / 2) ^ (2 * m))
  have hw_meas : ∀ v, Measurable (w v) := fun v =>
    (continuous_real_toNNReal.comp ((Real.continuous_sin.comp
      (v.continuous.div_const 2)).pow (2 * m))).measurable
  have hwnn : ∀ (v : StrongDual ℝ E) (y : E), 0 ≤ Real.sin (v y / 2) ^ (2 * m) := fun v y => by
    simp only [pow_mul]; positivity
  have hw_int : ∀ ρ : Measure E, (∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) ρ) →
      ∀ v : StrongDual ℝ E, Integrable (fun y => Real.sin (v y / 2) ^ (2 * m)) ρ := fun ρ hρ v => by
    refine ((hSint ρ hρ 0 v).const_mul ((-4 : ℂ) ^ m)⁻¹).re.congr
      (Eventually.of_forall fun y => ?_)
    simp only
    rw [← hpt 0 v y]
    simp only [zero_apply, ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    exact RCLike.ofReal_re _
  have hfinite : ∀ ρ : Measure E, (∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) ρ) →
      ∀ v, IsFiniteMeasure (ρ.withDensity fun y => (w v y : ℝ≥0∞)) := fun ρ hρ v =>
    isFiniteMeasure_withDensity_ofReal (hw_int ρ hρ v).2
  have hchar : ∀ ρ : Measure E, (∀ M : StrongDual ℝ E, Integrable (fun y => g (M y)) ρ) →
      ∀ v L : StrongDual ℝ E, charFunDual (ρ.withDensity fun y => (w v y : ℝ≥0∞)) L =
        ((-4 : ℂ) ^ m)⁻¹ * ∫ y, S L v y ∂ρ := fun ρ hρ v L => by
    rw [charFunDual_apply, integral_withDensity_eq_integral_smul (hw_meas v), ← integral_const_mul]
    congr 1
    funext y
    simp only [w]
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hwnn v y), Complex.real_smul, mul_comm, hpt]
  have hdens : ∀ v : StrongDual ℝ E, μ.restrict {y | (w v y : ℝ≥0∞) ≠ 0} =
      ν.restrict {y | (w v y : ℝ≥0∞) ≠ 0} := fun v => by
    have := hfinite μ hμg v
    have := hfinite ν hνg v
    refine restrict_ne_zero_eq_of_withDensity_eq (hw_meas v).coe_nnreal_ennreal
      (fun y => ENNReal.coe_ne_top) (Measure.ext_of_charFunDual (funext fun L => ?_))
    rw [hchar μ hμg, hchar ν hνg, hSeq]
  set U : Set E := ⋃ p, {y | (w (coordFamily E p) y : ℝ≥0∞) ≠ 0}
  have hU : Uᶜ ⊆ {0} := fun y hy => by
    by_contra hy0
    obtain ⟨p, hp⟩ := exists_coordFamily_sin_ne_zero hy0
    simp only [U, mem_compl_iff, mem_iUnion, not_exists, mem_ofPred_eq, not_not,
      ENNReal.coe_eq_zero, w, Real.toNNReal_eq_zero] at hy
    have := le_antisymm (hy p) (hwnn _ y)
    exact hp (eq_zero_of_pow_eq_zero this)
  have hself : ∀ ρ : Measure E, ρ {0} = 0 → ρ.restrict U = ρ := fun ρ hρ =>
    Measure.restrict_eq_self_of_ae_mem (measure_mono_null (fun y hy => hU hy) hρ)
  rw [← hself μ hμ0, ← hself ν hν0, Measure.restrict_iUnion_congr]
  exact fun p => hdens _

/-! ### The kernel `e^{is} - ∑_{k ≤ n} (is)^k / k!` -/

/-- The Taylor remainder of order `n` of `s ↦ e^{is}`. -/
noncomputable def expRem (n : ℕ) (s : ℝ) : ℂ :=
  cexp (s * I) - ∑ k ∈ Finset.range (n + 1), ((s : ℂ) * I) ^ k / (k.factorial : ℂ)

theorem continuous_expRem (n : ℕ) : Continuous (expRem n) := by
  unfold expRem
  fun_prop

@[simp] theorem expRem_zero (n : ℕ) : expRem n 0 = 0 := by
  simp [expRem, Finset.sum_range_succ']

/-- Forward differences of order `N` kill polynomials of degree `< N`. -/
theorem sum_shift_pow_eq_zero {k N : ℕ} (hk : k < N) (a b : ℝ) :
    ∑ j ∈ Finset.range (N + 1), ((-1 : ℤ) ^ (N - j) * (N.choose j : ℤ)) •
      (((a + j • b : ℝ) : ℂ) * I) ^ k = 0 := by
  have hdeg : ((Polynomial.C ((b : ℂ) * I) * Polynomial.X + Polynomial.C ((a : ℂ) * I)) ^
      k).natDegree < N := by
    refine lt_of_le_of_lt (Polynomial.natDegree_pow_le.trans ?_) hk
    calc k * _ ≤ k * 1 := Nat.mul_le_mul_left k Polynomial.natDegree_linear_le
      _ = k := mul_one k
  have := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift, Pi.zero_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, zero_add, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem fwdDiff_iter_expRem (n : ℕ) (a b : ℝ) :
    Δ_[b]^[2 * (n + 1)] (expRem n) a = Δ_[b]^[2 * (n + 1)] (fun x : ℝ => cexp (x * I)) a := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  simp only [expRem, smul_sub, Finset.sum_sub_distrib, sub_eq_self]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k < 2 * (n + 1) := by
    have := Finset.mem_range.1 hk; omega
  simp_rw [← smul_div_assoc, ← Finset.sum_div]
  rw [sum_shift_pow_eq_zero hk' a b, zero_div]

/-- The comparison function `min (u ^ (n + 1)) (u ^ n)`. -/
noncomputable def minPow (n : ℕ) (u : ℝ) : ℝ := min (u ^ (n + 1)) (u ^ n)

theorem minPow_nonneg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ minPow n u :=
  le_min (pow_nonneg hu _) (pow_nonneg hu _)

theorem minPow_mono (n : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : minPow n u ≤ minPow n v :=
  min_le_min (pow_le_pow_left₀ hu huv _) (pow_le_pow_left₀ hu huv _)

theorem minPow_mul_le (n : ℕ) {c u : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) :
    minPow n (c * u) ≤ (c ^ n + c ^ (n + 1)) * minPow n u := by
  have hK1 : c ^ (n + 1) ≤ c ^ n + c ^ (n + 1) := le_add_of_nonneg_left (pow_nonneg hc _)
  have hK2 : c ^ n ≤ c ^ n + c ^ (n + 1) := le_add_of_nonneg_right (pow_nonneg hc _)
  rw [minPow, minPow, mul_pow, mul_pow, mul_min_of_nonneg _ _ (by positivity)]
  exact min_le_min (mul_le_mul_of_nonneg_right hK1 (pow_nonneg hu _))
    (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hu _))

theorem norm_expRem_le (n : ℕ) (s : ℝ) : ‖expRem n s‖ ≤ (n + 2) * minPow n |s| := by
  have hx : ‖(s : ℂ) * I‖ = |s| := by simp
  rcases le_or_gt |s| 1 with hs | hs
  · have hmin : minPow n |s| = |s| ^ (n + 1) :=
      min_eq_left (pow_le_pow_of_le_one (abs_nonneg s) hs (Nat.le_succ n))
    have := Complex.exp_bound (x := (s : ℂ) * I) (by rw [hx]; exact hs) (n := n + 1) n.succ_pos
    rw [hx] at this
    rw [expRem, hmin]
    refine this.trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (abs_nonneg s) _)
    have h1 : (1 : ℝ) ≤ ((n + 1).factorial * (n + 1) : ℝ) := by
      have := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero (n + 1))
      have h2 : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by exact_mod_cast this
      nlinarith
    calc (((n + 1).succ : ℕ) : ℝ) * (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))⁻¹
        ≤ (((n + 1).succ : ℕ) : ℝ) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          push_cast
          exact inv_le_one_of_one_le₀ h1
      _ = n + 2 := by push_cast; ring
  · have hmin : minPow n |s| = |s| ^ n :=
      min_eq_right (pow_le_pow_right₀ hs.le (Nat.le_succ n))
    rw [expRem, hmin]
    have hterm : ∀ k ∈ Finset.range (n + 1), ‖((s : ℂ) * I) ^ k / (k.factorial : ℂ)‖ ≤ |s| ^ n :=
      fun k hk => by
        rw [norm_div, norm_pow, hx, Complex.norm_natCast]
        refine (div_le_self (pow_nonneg (abs_nonneg s) _) ?_).trans
          (pow_le_pow_right₀ hs.le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
    calc ‖cexp (s * I) - ∑ k ∈ Finset.range (n + 1), ((s : ℂ) * I) ^ k / (k.factorial : ℂ)‖
        ≤ ‖cexp (s * I)‖ + ‖∑ k ∈ Finset.range (n + 1), ((s : ℂ) * I) ^ k / (k.factorial : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ 1 + (n + 1) * |s| ^ n := by
          rw [Complex.norm_exp_ofReal_mul_I]
          gcongr
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum hterm).trans ?_
          simp
      _ ≤ (n + 2) * |s| ^ n := by
          have : 1 ≤ |s| ^ n := one_le_pow₀ hs.le
          linarith

/-! ### Integrability from a power-law tail -/

theorem lintegral_rpow_mul_lt_top {S : Set ℝ} {s : ℝ} (hint : IntegrableOn (fun t : ℝ => t ^ s) S)
    {C : ℝ≥0∞} (hC : C ≠ ∞) : ∫⁻ t in S, ENNReal.ofReal (t ^ s) * C < ∞ := by
  rw [lintegral_mul_const' _ _ hC]
  exact ENNReal.mul_lt_top hint.lintegral_lt_top hC.lt_top

omit [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- If `μ {‖y‖ > t} ≤ C t ^ (-α)` with `n < α < n + 1`, then `min (‖y‖ ^ (n + 1), ‖y‖ ^ n)` is
`μ`-integrable. -/
theorem integrable_minPow_norm [OpensMeasurableSpace E] {α : ℝ} {n : ℕ} (hn : (n : ℝ) < α)
    (hn1 : α < n + 1) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (htail : ∀ t > 0, μ {y | t < ‖y‖} ≤ ENNReal.ofReal (t ^ (-α)) * C) :
    Integrable (fun y => minPow n ‖y‖) μ := by
  have hcont : Continuous fun y : E => minPow n ‖y‖ := by
    unfold minPow; fun_prop
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hnn : 0 ≤ᵐ[μ] fun y => minPow n ‖y‖ :=
    Eventually.of_forall fun y => minPow_nonneg n (norm_nonneg y)
  rw [hasFiniteIntegral_iff_ofReal hnn,
    lintegral_eq_lintegral_meas_lt μ hnn hcont.measurable.aemeasurable,
    ← Ioc_union_Ioi_eq_Ioi zero_le_one, lintegral_union measurableSet_Ioi
      (Ioc_disjoint_Ioi le_rfl)]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · -- small values: `{t < minPow} ⊆ {t ^ (1 / (n + 1)) < ‖y‖}`
    have hs : -1 < -α / ((n : ℝ) + 1) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    have hint : IntegrableOn (fun t : ℝ => t ^ (-α / ((n : ℝ) + 1))) (Ioc 0 1) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).2
        ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 hs)
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc fun t ht => ?_)
      (lintegral_rpow_mul_lt_top hint hC)
    have ht0 : 0 < t := ht.1
    set r : ℝ := t ^ (((n + 1 : ℕ) : ℝ)⁻¹)
    have hr : 0 < r := Real.rpow_pos_of_pos ht0 _
    have hsub : {y : E | t < minPow n ‖y‖} ⊆ {y | r < ‖y‖} := fun y hy => by
      by_contra hle
      simp only [mem_ofPred_eq, not_lt] at hle hy
      have h1 : ‖y‖ ^ (n + 1) ≤ r ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg y) hle _
      rw [Real.rpow_inv_natCast_pow ht0.le (Nat.succ_ne_zero n)] at h1
      exact absurd (lt_of_lt_of_le hy ((min_le_left _ _).trans h1)) (lt_irrefl t)
    refine (measure_mono hsub).trans ((htail r hr).trans_eq ?_)
    congr 2
    rw [← Real.rpow_mul ht0.le]
    congr 1
    push_cast
    field_simp
  · -- large values
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_)
        (show ∫⁻ t in Ioi (1 : ℝ), (0 : ℝ≥0∞) < ∞ by simp)
      have hempty : {y : E | t < minPow 0 ‖y‖} = ∅ := by
        ext y
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (min_le_right _ _).trans (by simpa using (le_of_lt (mem_Ioi.1 ht)))
      rw [hempty, measure_empty]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hs : -α / (n : ℝ) < -1 := by
      rw [div_lt_iff₀ hnR]; linarith
    have hint : IntegrableOn (fun t : ℝ => t ^ (-α / (n : ℝ))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt hs one_pos
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_)
      (lintegral_rpow_mul_lt_top hint hC)
    have ht0 : 0 < t := lt_trans one_pos ht
    set r : ℝ := t ^ ((n : ℝ)⁻¹)
    have hr : 0 < r := Real.rpow_pos_of_pos ht0 _
    have hsub : {y : E | t < minPow n ‖y‖} ⊆ {y | r < ‖y‖} := fun y hy => by
      by_contra hle
      simp only [mem_ofPred_eq, not_lt] at hle hy
      have h1 : ‖y‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg y) hle _
      rw [Real.rpow_inv_natCast_pow ht0.le hnpos.ne'] at h1
      exact absurd (lt_of_lt_of_le hy ((min_le_right _ _).trans h1)) (lt_irrefl t)
    refine (measure_mono hsub).trans ((htail r hr).trans_eq ?_)
    congr 2
    rw [← Real.rpow_mul ht0.le]
    congr 1
    field_simp

omit [BorelSpace E] [FiniteDimensional ℝ E] in
theorem integrable_expRem_comp [OpensMeasurableSpace E] {n : ℕ}
    (hμ : Integrable (fun y => minPow n ‖y‖) μ) (M : StrongDual ℝ E) :
    Integrable (fun y => expRem n (M y)) μ := by
  refine Integrable.mono' (hμ.const_mul ((n + 2) * (‖M‖ ^ n + ‖M‖ ^ (n + 1))))
    ((continuous_expRem n).comp M.continuous).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  refine (norm_expRem_le n (M y)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc minPow n |M y| ≤ minPow n (‖M‖ * ‖y‖) :=
        minPow_mono n (abs_nonneg _) (by simpa [Real.norm_eq_abs] using M.le_opNorm y)
    _ ≤ (‖M‖ ^ n + ‖M‖ ^ (n + 1)) * minPow n ‖y‖ :=
        minPow_mul_le n (norm_nonneg _) (norm_nonneg _)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Half-spaces `{L > 1}` are contained in `{‖y‖ > 1 / (‖L‖ + 1)}`. -/
theorem setOf_one_lt_apply_subset (L : StrongDual ℝ E) :
    {y : E | 1 < L y} ⊆ {y | (‖L‖ + 1)⁻¹ < ‖y‖} := fun y hy => by
  simp only [mem_ofPred_eq] at hy ⊢
  rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
  have h1 : L y ≤ ‖L‖ * ‖y‖ := (le_abs_self _).trans (by simpa using L.le_opNorm y)
  nlinarith [norm_nonneg y]

end CramerWold

end ExtremeValueTheory
