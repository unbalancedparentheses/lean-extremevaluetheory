/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Mixing coefficients and `m`-dependence

We define the strong mixing (`α`-mixing) and absolute regularity (`β`-mixing) coefficients of two
σ-algebras, and the corresponding coefficients of a discrete time process `X : ℕ → Ω → E`, between
the past `σ(X t : t ≤ s)` and the future `σ(X t : t ≥ s + h)`.

## Main definitions

* `ProbabilityTheory.strongMixingCoeff m₁ m₂ μ`:
  `α(m₁, m₂) = sup {|μ (A ∩ B) - μ A μ B| : A ∈ m₁, B ∈ m₂}`.
* `ProbabilityTheory.betaMixingCoeff m₁ m₂ μ`:
  `β(m₁, m₂) = sup (1/2) ∑ᵢ ∑ⱼ |μ (Aᵢ ∩ Bⱼ) - μ Aᵢ μ Bⱼ|`, the supremum over finite partitions
  `(Aᵢ) ⊆ m₁`, `(Bⱼ) ⊆ m₂` of `Ω`.
* `ProbabilityTheory.pastMeasurableSpace X s`, `ProbabilityTheory.futureMeasurableSpace X s`:
  `σ(X t : t ≤ s)` and `σ(X t : t ≥ s)`.
* `ProbabilityTheory.alphaMixing X μ h`, `ProbabilityTheory.betaMixing X μ h`: the mixing
  coefficients `sup_s α(σ(X t : t ≤ s), σ(X t : t ≥ s + h))` and similarly for `β`.
* `ProbabilityTheory.IsStrongMixing X μ`, `ProbabilityTheory.IsBetaMixing X μ`: the coefficients
  tend to `0`.
* `ProbabilityTheory.IsMDependent X m μ`: the past up to `s` and the future from `s + m + 1` are
  independent for every `s`.

## Main results

* `ProbabilityTheory.strongMixingCoeff_eq_zero_of_indep`,
  `ProbabilityTheory.betaMixingCoeff_eq_zero_of_indep`:
  independent σ-algebras have vanishing coefficients.
* `ProbabilityTheory.strongMixingCoeff_le_betaMixingCoeff`: `α ≤ β`.
* `ProbabilityTheory.IsMDependent.alphaMixing_eq_zero`: for an `m`-dependent process, `α(h) = 0`
  for `h > m`; hence `m`-dependent processes are strongly mixing (`IsMDependent.isStrongMixing`).
* `ProbabilityTheory.IsMDependent.betaMixing_eq_zero`,
  `ProbabilityTheory.IsMDependent.isBetaMixing`.
* `ProbabilityTheory.IsMDependent.indepFun`: `X s` and `X t` are independent for `t > s + m`.
* `ProbabilityTheory.IsMDependent.comp`: `m`-dependence is preserved by measurable maps applied
  coordinatewise.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Coefficients of two σ-algebras -/

section Coeff

/-- The **strong mixing coefficient** of two σ-algebras:
`α(m₁, m₂) = sup {|μ (A ∩ B) - μ A μ B| : A ∈ m₁, B ∈ m₂}`. -/
noncomputable def strongMixingCoeff (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) : ℝ≥0∞ :=
  ⨆ (A : Set Ω) (_ : MeasurableSet[m₁] A) (B : Set Ω) (_ : MeasurableSet[m₂] B),
    ENNReal.ofReal |μ.real (A ∩ B) - μ.real A * μ.real B|

/-- The **absolute regularity (`β`-mixing) coefficient** of two σ-algebras:
`β(m₁, m₂) = sup (1/2) ∑ᵢ ∑ⱼ |μ (Aᵢ ∩ Bⱼ) - μ Aᵢ μ Bⱼ|` over finite partitions `(Aᵢ)` of `Ω` into
`m₁`-measurable sets and `(Bⱼ)` into `m₂`-measurable sets. -/
noncomputable def betaMixingCoeff (m₁ m₂ : MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) : ℝ≥0∞ :=
  ⨆ (k : ℕ) (l : ℕ) (A : Fin k → Set Ω) (_ : ∀ i, MeasurableSet[m₁] (A i))
    (_ : Pairwise (fun i j => Disjoint (A i) (A j))) (_ : (⋃ i, A i) = univ)
    (B : Fin l → Set Ω) (_ : ∀ j, MeasurableSet[m₂] (B j))
    (_ : Pairwise (fun i j => Disjoint (B i) (B j))) (_ : (⋃ j, B j) = univ),
    ENNReal.ofReal (2⁻¹ * ∑ i, ∑ j, |μ.real (A i ∩ B j) - μ.real (A i) * μ.real (B j)|)

variable {m₁ m₂ m₃ m₄ : MeasurableSpace Ω}

theorem ofReal_le_strongMixingCoeff {A B : Set Ω} (hA : MeasurableSet[m₁] A)
    (hB : MeasurableSet[m₂] B) :
    ENNReal.ofReal |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ strongMixingCoeff m₁ m₂ μ :=
  le_iSup₂_of_le A hA (le_iSup₂_of_le (f := fun B (_ : MeasurableSet[m₂] B) =>
    ENNReal.ofReal |μ.real (A ∩ B) - μ.real A * μ.real B|) B hB le_rfl)

theorem strongMixingCoeff_mono (h₁ : m₁ ≤ m₃) (h₂ : m₂ ≤ m₄) :
    strongMixingCoeff m₁ m₂ μ ≤ strongMixingCoeff m₃ m₄ μ :=
  iSup₂_le fun A hA => iSup₂_le fun B hB => ofReal_le_strongMixingCoeff (h₁ A hA) (h₂ B hB)

theorem strongMixingCoeff_le_one [IsProbabilityMeasure μ] : strongMixingCoeff m₁ m₂ μ ≤ 1 := by
  refine iSup₂_le fun A _ => iSup₂_le fun B _ => ENNReal.ofReal_le_one.2 ?_
  have h1 : μ.real (A ∩ B) ≤ 1 := measureReal_le_one
  have h2 : μ.real A * μ.real B ≤ 1 :=
    (mul_le_mul measureReal_le_one measureReal_le_one measureReal_nonneg zero_le_one).trans_eq
      (one_mul 1)
  have h3 : 0 ≤ μ.real (A ∩ B) := measureReal_nonneg
  have h4 : 0 ≤ μ.real A * μ.real B := mul_nonneg measureReal_nonneg measureReal_nonneg
  rw [abs_le]
  constructor <;> linarith

theorem strongMixingCoeff_ne_top [IsProbabilityMeasure μ] : strongMixingCoeff m₁ m₂ μ ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top strongMixingCoeff_le_one

/-- The defining bound of the strong mixing coefficient, in real numbers. -/
theorem abs_measureReal_inter_sub_le_strongMixingCoeff [IsProbabilityMeasure μ] {A B : Set Ω}
    (hA : MeasurableSet[m₁] A) (hB : MeasurableSet[m₂] B) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ (strongMixingCoeff m₁ m₂ μ).toReal := by
  have := ENNReal.toReal_mono strongMixingCoeff_ne_top (ofReal_le_strongMixingCoeff hA hB (μ := μ))
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this

theorem strongMixingCoeff_eq_zero_of_indep (h : Indep m₁ m₂ μ) :
    strongMixingCoeff m₁ m₂ μ = 0 := by
  refine le_antisymm (iSup₂_le fun A hA => iSup₂_le fun B hB => ?_) bot_le
  rw [measureReal_def, measureReal_def, measureReal_def, (Indep_iff _ _ _).1 h A B hA hB,
    ENNReal.toReal_mul, sub_self, abs_zero, ENNReal.ofReal_zero]

theorem betaMixingCoeff_eq_zero_of_indep (h : Indep m₁ m₂ μ) :
    betaMixingCoeff m₁ m₂ μ = 0 := by
  refine le_antisymm ?_ bot_le
  simp only [betaMixingCoeff, iSup_le_iff]
  intro k l A hA _ _ B hB _ _
  have : ∀ i j, μ.real (A i ∩ B j) - μ.real (A i) * μ.real (B j) = 0 := fun i j => by
    rw [measureReal_def, measureReal_def, measureReal_def,
      (Indep_iff _ _ _).1 h _ _ (hA i) (hB j), ENNReal.toReal_mul, sub_self]
  simp [this]

/-- **`α ≤ β`**: the strong mixing coefficient is at most the `β`-mixing coefficient (in fact
`2 α ≤ β`), using the partitions `{A, Aᶜ}` and `{B, Bᶜ}`. -/
theorem strongMixingCoeff_le_betaMixingCoeff [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ)
    (h₂ : m₂ ≤ mΩ) : strongMixingCoeff m₁ m₂ μ ≤ betaMixingCoeff m₁ m₂ μ := by
  refine iSup₂_le fun A hA => iSup₂_le fun B hB => ?_
  set A' : Fin 2 → Set Ω := ![A, Aᶜ]
  set B' : Fin 2 → Set Ω := ![B, Bᶜ]
  have hA' : ∀ i, MeasurableSet[m₁] (A' i) := by
    intro i; fin_cases i
    · exact hA
    · exact hA.compl
  have hB' : ∀ j, MeasurableSet[m₂] (B' j) := by
    intro j; fin_cases j
    · exact hB
    · exact hB.compl
  have hdA : Pairwise fun i j => Disjoint (A' i) (A' j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [A', disjoint_compl_right,
      disjoint_compl_left]
  have hdB : Pairwise fun i j => Disjoint (B' i) (B' j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [B', disjoint_compl_right,
      disjoint_compl_left]
  have huA : ⋃ i, A' i = univ := by
    ext ω; simp only [mem_iUnion, Fin.exists_fin_two, mem_univ, iff_true, A']
    simp [em]
  have huB : ⋃ j, B' j = univ := by
    ext ω; simp only [mem_iUnion, Fin.exists_fin_two, mem_univ, iff_true, B']
    simp [em]
  have key : ENNReal.ofReal |μ.real (A ∩ B) - μ.real A * μ.real B| ≤
      ENNReal.ofReal (2⁻¹ * ∑ i, ∑ j,
        |μ.real (A' i ∩ B' j) - μ.real (A' i) * μ.real (B' j)|) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have mA : MeasurableSet[mΩ] A := h₁ A hA
    have mB : MeasurableSet[mΩ] B := h₂ B hB
    have e1 : μ.real (A ∩ Bᶜ) = μ.real A - μ.real (A ∩ B) := by
      have := measureReal_inter_add_sdiff (μ := μ) (s := A) mB
      rw [sdiff_eq] at this; linarith
    have e2 : μ.real (Aᶜ ∩ B) = μ.real B - μ.real (A ∩ B) := by
      have := measureReal_inter_add_sdiff (μ := μ) (s := B) mA
      rw [sdiff_eq, inter_comm B A, inter_comm B Aᶜ] at this; linarith
    have e3 : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real A - μ.real B + μ.real (A ∩ B) := by
      have := measureReal_inter_add_sdiff (μ := μ) (s := Aᶜ) mB
      rw [sdiff_eq, probReal_compl_eq_one_sub mA] at this; linarith
    simp only [Fin.sum_univ_two, A', B', Matrix.cons_val_zero, Matrix.cons_val_one,
      probReal_compl_eq_one_sub mA, probReal_compl_eq_one_sub mB, e1, e2, e3]
    set d := μ.real (A ∩ B) - μ.real A * μ.real B
    have : μ.real A - μ.real (A ∩ B) - μ.real A * (1 - μ.real B) = -d := by ring
    have h2 : μ.real B - μ.real (A ∩ B) - (1 - μ.real A) * μ.real B = -d := by ring
    have h3 : 1 - μ.real A - μ.real B + μ.real (A ∩ B) - (1 - μ.real A) * (1 - μ.real B) = d := by
      ring
    rw [this, h2, h3, abs_neg]
    linarith [abs_nonneg d]
  exact key.trans (le_iSup_of_le 2 (le_iSup_of_le 2 (le_iSup_of_le A' (le_iSup_of_le hA'
    (le_iSup_of_le hdA (le_iSup_of_le huA (le_iSup_of_le B' (le_iSup_of_le hB'
    (le_iSup_of_le hdB (le_iSup_of_le huB le_rfl))))))))))

end Coeff

/-! ### Mixing coefficients of a process -/

section Process

variable [mE : MeasurableSpace E] [mF : MeasurableSpace F] {X : ℕ → Ω → E} {m : ℕ}

/-- The past `σ(X t : t ≤ s)` of a process. -/
@[instance_reducible]
def pastMeasurableSpace (X : ℕ → Ω → E) (s : ℕ) : MeasurableSpace Ω :=
  ⨆ (t : ℕ) (_ : t ≤ s), mE.comap (X t)

/-- The future `σ(X t : t ≥ s)` of a process. -/
@[instance_reducible]
def futureMeasurableSpace (X : ℕ → Ω → E) (s : ℕ) : MeasurableSpace Ω :=
  ⨆ (t : ℕ) (_ : s ≤ t), mE.comap (X t)

theorem comap_le_pastMeasurableSpace {s t : ℕ} (h : t ≤ s) :
    mE.comap (X t) ≤ pastMeasurableSpace X s :=
  le_iSup₂_of_le (f := fun t (_ : t ≤ s) => mE.comap (X t)) t h le_rfl

theorem comap_le_futureMeasurableSpace {s t : ℕ} (h : s ≤ t) :
    mE.comap (X t) ≤ futureMeasurableSpace X s :=
  le_iSup₂_of_le (f := fun t (_ : s ≤ t) => mE.comap (X t)) t h le_rfl

theorem futureMeasurableSpace_anti {s s' : ℕ} (h : s ≤ s') :
    futureMeasurableSpace X s' ≤ futureMeasurableSpace X s :=
  iSup₂_le fun _ ht => comap_le_futureMeasurableSpace (h.trans ht)

theorem pastMeasurableSpace_le (hX : ∀ t, Measurable (X t)) (s : ℕ) :
    pastMeasurableSpace X s ≤ mΩ :=
  iSup₂_le fun t _ => (hX t).comap_le

theorem futureMeasurableSpace_le (hX : ∀ t, Measurable (X t)) (s : ℕ) :
    futureMeasurableSpace X s ≤ mΩ :=
  iSup₂_le fun t _ => (hX t).comap_le

/-- The strong mixing coefficients of a process:
`α(h) = sup_s α(σ(X t : t ≤ s), σ(X t : t ≥ s + h))`. -/
noncomputable def alphaMixing (X : ℕ → Ω → E) (μ : Measure Ω) (h : ℕ) : ℝ≥0∞ :=
  ⨆ s, strongMixingCoeff (pastMeasurableSpace X s) (futureMeasurableSpace X (s + h)) μ

/-- The `β`-mixing coefficients of a process:
`β(h) = sup_s β(σ(X t : t ≤ s), σ(X t : t ≥ s + h))`. -/
noncomputable def betaMixing (X : ℕ → Ω → E) (μ : Measure Ω) (h : ℕ) : ℝ≥0∞ :=
  ⨆ s, betaMixingCoeff (pastMeasurableSpace X s) (futureMeasurableSpace X (s + h)) μ

/-- A process is **strongly mixing** (`α`-mixing) if `α(h) → 0`. -/
def IsStrongMixing (X : ℕ → Ω → E) (μ : Measure Ω) : Prop :=
  Tendsto (alphaMixing X μ) atTop (𝓝 0)

/-- A process is **`β`-mixing** (absolutely regular) if `β(h) → 0`. -/
def IsBetaMixing (X : ℕ → Ω → E) (μ : Measure Ω) : Prop :=
  Tendsto (betaMixing X μ) atTop (𝓝 0)

/-- A process is **`m`-dependent** if for every `s` the past `σ(X t : t ≤ s)` and the future
`σ(X t : t ≥ s + m + 1)` are independent. -/
def IsMDependent (X : ℕ → Ω → E) (m : ℕ) (μ : Measure Ω) : Prop :=
  ∀ s, Indep (pastMeasurableSpace X s) (futureMeasurableSpace X (s + m + 1)) μ

theorem alphaMixing_le_one [IsProbabilityMeasure μ] (h : ℕ) : alphaMixing X μ h ≤ 1 :=
  iSup_le fun _ => strongMixingCoeff_le_one

theorem alphaMixing_ne_top [IsProbabilityMeasure μ] (h : ℕ) : alphaMixing X μ h ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (alphaMixing_le_one h)

theorem strongMixingCoeff_le_alphaMixing (s h : ℕ) :
    strongMixingCoeff (pastMeasurableSpace X s) (futureMeasurableSpace X (s + h)) μ ≤
      alphaMixing X μ h :=
  le_iSup (fun s => strongMixingCoeff (pastMeasurableSpace X s)
    (futureMeasurableSpace X (s + h)) μ) s

/-- The defining bound of `α(h)`: for events `A` of the past up to `s` and `B` of the future
from `s + h`, `|μ (A ∩ B) - μ A μ B| ≤ α(h)`. -/
theorem abs_measureReal_inter_sub_le_alphaMixing [IsProbabilityMeasure μ] {s h : ℕ}
    {A B : Set Ω} (hA : MeasurableSet[pastMeasurableSpace X s] A)
    (hB : MeasurableSet[futureMeasurableSpace X (s + h)] B) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ (alphaMixing X μ h).toReal :=
  (abs_measureReal_inter_sub_le_strongMixingCoeff hA hB).trans
    (ENNReal.toReal_mono (alphaMixing_ne_top h) (strongMixingCoeff_le_alphaMixing s h))

/-- `α ≤ β` for processes. -/
theorem alphaMixing_le_betaMixing [IsProbabilityMeasure μ] (hX : ∀ t, Measurable (X t))
    (h : ℕ) : alphaMixing X μ h ≤ betaMixing X μ h :=
  iSup_mono fun s => strongMixingCoeff_le_betaMixingCoeff (pastMeasurableSpace_le hX s)
    (futureMeasurableSpace_le hX _)

/-- `β`-mixing implies strong mixing. -/
theorem IsBetaMixing.isStrongMixing [IsProbabilityMeasure μ] (hX : ∀ t, Measurable (X t))
    (h : IsBetaMixing X μ) : IsStrongMixing X μ :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    (alphaMixing_le_betaMixing hX)

namespace IsMDependent

theorem indep_of_lt (hX : IsMDependent X m μ) {s h : ℕ} (hh : m < h) :
    Indep (pastMeasurableSpace X s) (futureMeasurableSpace X (s + h)) μ :=
  indep_of_indep_of_le_right (hX s) (futureMeasurableSpace_anti (by omega))

/-- **`m`-dependent processes have `α(h) = 0` for `h > m`.** -/
theorem alphaMixing_eq_zero (hX : IsMDependent X m μ) {h : ℕ} (hh : m < h) :
    alphaMixing X μ h = 0 :=
  ENNReal.iSup_eq_zero.2 fun _ => strongMixingCoeff_eq_zero_of_indep (hX.indep_of_lt hh)

/-- **`m`-dependent processes have `β(h) = 0` for `h > m`.** -/
theorem betaMixing_eq_zero (hX : IsMDependent X m μ) {h : ℕ} (hh : m < h) :
    betaMixing X μ h = 0 :=
  ENNReal.iSup_eq_zero.2 fun _ => betaMixingCoeff_eq_zero_of_indep (hX.indep_of_lt hh)

theorem isBetaMixing (hX : IsMDependent X m μ) : IsBetaMixing X μ :=
  tendsto_atTop_of_eventually_const (i₀ := m + 1) fun _ hh => hX.betaMixing_eq_zero (by omega)

theorem isStrongMixing (hX : IsMDependent X m μ) : IsStrongMixing X μ :=
  tendsto_atTop_of_eventually_const (i₀ := m + 1) fun _ hh => hX.alphaMixing_eq_zero (by omega)

/-- In an `m`-dependent process, `X s` and `X t` are independent when `t > s + m`. -/
theorem indepFun (hX : IsMDependent X m μ) {s t : ℕ} (hst : s + m < t) :
    IndepFun (X s) (X t) μ := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le (hX s) (comap_le_pastMeasurableSpace le_rfl)
    (comap_le_futureMeasurableSpace (by omega))

/-- `m`-dependence is preserved by applying a measurable map to each coordinate. -/
theorem comp (hX : IsMDependent X m μ) {f : E → F} (hf : Measurable f) :
    IsMDependent (fun t => f ∘ X t) m μ := by
  have hc : ∀ t, mF.comap (f ∘ X t) ≤ mE.comap (X t) := fun t => by
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hf.comap_le
  intro s
  refine indep_of_indep_of_le (hX s) (iSup₂_le fun t ht => (hc t).trans
    (comap_le_pastMeasurableSpace ht)) (iSup₂_le fun t ht => (hc t).trans
    (comap_le_futureMeasurableSpace ht))

end IsMDependent

end Process

end ProbabilityTheory
