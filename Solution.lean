import Mathlib
import ExtremeValueTheory

/-!
# The solution

Proves the statements of `Challenge.lean` from the library. The definitions in the first section
are copied from `Challenge.lean`: `lake comparator` fails unless they, and the statements at the end
of this file, are identical there and here.

The namespace `Solution` proves that each restated definition is the library's. Those lemmas are not
needed for the comparison; they say what `Challenge.lean` has to do with this library. The kernel
checks the proofs, so a reader who has read `Challenge.lean` does not have to read this file.
-/

open Filter Topology MeasureTheory ProbabilityTheory

namespace Challenge

structure IsDistributionFunction (F : ℝ → ℝ) : Prop where
  mono : Monotone F
  rightCont : ∀ x, ContinuousWithinAt F (Set.Ici x) x
  atBot : Tendsto F atBot (𝓝 0)
  atTop : Tendsto F atTop (𝓝 1)

def IsDegenerate (G : ℝ → ℝ) : Prop := ∀ x, G x = 0 ∨ G x = 1

def InDomainOfAttraction (F G : ℝ → ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, (∀ n, 0 < a n) ∧
    ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F (a n * x + b n) ^ n) atTop (𝓝 (G x))

def SameType (G H : ℝ → ℝ) : Prop := ∃ a b : ℝ, 0 < a ∧ ∀ x, G (a * x + b) = H x

noncomputable def gumbel (x : ℝ) : ℝ := Real.exp (-Real.exp (-x))

noncomputable def frechet (α x : ℝ) : ℝ := if x ≤ 0 then 0 else Real.exp (-(x ^ (-α)))

noncomputable def weibull (α x : ℝ) : ℝ := if x < 0 then Real.exp (-((-x) ^ α)) else 1

noncomputable def gev (ξ x : ℝ) : ℝ :=
  if ξ = 0 then Real.exp (-Real.exp (-x))
  else if 0 < 1 + ξ * x then Real.exp (-(1 + ξ * x) ^ (-1 / ξ))
  else if 0 < ξ then 0 else 1

noncomputable def gpdSurvival (ξ x : ℝ) : ℝ :=
  if ξ = 0 then Real.exp (-x) else (max (1 + ξ * x) 0) ^ (-(1 / ξ))

def toRightEndpoint (F : ℝ → ℝ) : Filter ℝ :=
  ⨅ x ∈ {x | F x < 1}, 𝓟 (Set.Ioi x ∩ {u | F u < 1})

def IsRegularlyVarying (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < f x) ∧ ∀ c : ℝ, 0 < c → Tendsto (fun x ↦ f (c * x) / f x) atTop (𝓝 (c ^ ρ))

noncomputable def orderStat {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x (Tuple.sort x (Fin.rev ⟨j, h⟩)) else 0

noncomputable def hill {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, (Real.log (orderStat x i) - Real.log (orderStat x k))

noncomputable def echoProcess {Ω : Type*} (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  max (Z t ω) (⨆ j : ℕ, if L (Z (t - (j + 1)) ω) = j + 1 then Z (t - (j + 1)) ω else 0)

noncomputable def powLag (γ z : ℝ) : ℕ := ⌊z ^ γ⌋₊ + 1

def AntiClustering {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℤ → Ω → ℝ) (a : ℕ → ℝ)
    (r : ℕ → ℕ) : Prop :=
  ∀ x : ℝ, 0 < x → ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ∀ᶠ n in atTop,
    P.real {ω | a n * x < |X 0 ω| ∧ ∃ t : ℤ, (m : ℤ) ≤ |t| ∧ |t| ≤ r n ∧ a n * x < |X t ω|} ≤
      ε * P.real {ω | a n * x < |X 0 ω|}

end Challenge

namespace Solution

open Challenge CumulativeDistributionFunction

/-! ## The restated definitions are the library's -/

/-- A function satisfying `IsDistributionFunction` as a c.d.f. of the library. -/
noncomputable def toCDF {F : ℝ → ℝ} (hF : IsDistributionFunction F) :
    CumulativeDistributionFunction where
  toFun := F
  mono' := hF.mono
  right_continuous' := hF.rightCont
  tendsto_atTop := hF.atTop
  tendsto_atBot := hF.atBot

theorem coe_toCDF {F : ℝ → ℝ} (hF : IsDistributionFunction F) : ⇑(toCDF hF) = F := rfl

theorem isDistributionFunction_coe (F : CumulativeDistributionFunction) :
    IsDistributionFunction F :=
  ⟨F.mono', F.right_continuous', F.tendsto_atBot, F.tendsto_atTop⟩

/-- `IsDistributionFunction` is the library's `CumulativeDistributionFunction`. -/
theorem isDistributionFunction_iff {F : ℝ → ℝ} :
    IsDistributionFunction F ↔ ∃ G : CumulativeDistributionFunction, ⇑G = F :=
  ⟨fun hF ↦ ⟨toCDF hF, rfl⟩, fun ⟨G, hG⟩ ↦ hG ▸ isDistributionFunction_coe G⟩

/-- `IsDegenerate` is the library's `CumulativeDistributionFunction.IsDegenerate`. -/
theorem isDegenerate_iff (G : CumulativeDistributionFunction) :
    Challenge.IsDegenerate G ↔ G.IsDegenerate := Iff.rfl

/-- The inverse of `mkOfCoefs` read as `x ↦ a x + b`: `(A • F) x = F (a x + b)`. -/
theorem smul_inv_mkOfCoefs_apply (F : CumulativeDistributionFunction) {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    ((AffineIncrEquiv.mkOfCoefs ha b)⁻¹ • F) x = F (a * x + b) := by
  rw [mulAction_apply_eq, inv_inv, AffineIncrEquiv.apply_eq, AffineIncrEquiv.coefs_fst_mkOfCoefs,
    AffineIncrEquiv.coefs_snd_mkOfCoefs]

/-- `(A • F) x = F (a x + b)` for the coefficients `a > 0`, `b` of `A⁻¹`. -/
theorem smul_apply_coefs (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) (x : ℝ) :
    (A • F) x = F (A⁻¹.coefs.1 * x + A⁻¹.coefs.2) := by
  rw [mulAction_apply_eq, AffineIncrEquiv.apply_eq]

/-- `InDomainOfAttraction` is the library's form with `AffineIncrEquiv`, the one in
`IsExtremeValueDistr`. -/
theorem inDomainOfAttraction_iff (F G : CumulativeDistributionFunction) :
    InDomainOfAttraction F G ↔ ∃ As : ℕ → AffineIncrEquiv,
      ∀ x, ContinuousAt G x → Tendsto (fun n ↦ ((As n • F) x) ^ n) atTop (𝓝 (G x)) := by
  constructor
  · rintro ⟨a, b, ha, h⟩
    refine ⟨fun n ↦ (AffineIncrEquiv.mkOfCoefs (ha n) (b n))⁻¹, fun x hx ↦ ?_⟩
    simpa only [smul_inv_mkOfCoefs_apply] using h x hx
  · rintro ⟨As, h⟩
    refine ⟨fun n ↦ (As n)⁻¹.coefs.1, fun n ↦ (As n)⁻¹.coefs.2,
      fun n ↦ (As n)⁻¹.coefs_fst_pos, fun x hx ↦ ?_⟩
    simpa only [smul_apply_coefs] using h x hx

/-- `SameType` is the library's: the two laws differ by the action of an `AffineIncrEquiv`. -/
theorem sameType_iff (G H : CumulativeDistributionFunction) :
    SameType G H ↔ ∃ A : AffineIncrEquiv, A • G = H := by
  constructor
  · rintro ⟨a, b, ha, h⟩
    refine ⟨(AffineIncrEquiv.mkOfCoefs ha b)⁻¹, ?_⟩
    ext x
    rw [smul_inv_mkOfCoefs_apply, h]
  · rintro ⟨A, rfl⟩
    exact ⟨A⁻¹.coefs.1, A⁻¹.coefs.2, A⁻¹.coefs_fst_pos, fun x ↦ (smul_apply_coefs G A x).symm⟩

/-- `gumbel` is the library's `standardGumbelCDF`. -/
theorem gumbel_eq : gumbel = ⇑standardGumbelCDF := rfl

/-- `frechet α` is the library's `standardFrechetCDF`. -/
theorem frechet_eq {α : ℝ} (hα : 0 < α) : frechet α = ⇑(standardFrechetCDF hα) := rfl

/-- `weibull α` is the library's `standardWeibullCDF`. -/
theorem weibull_eq {α : ℝ} (hα : 0 < α) : weibull α = ⇑(standardWeibullCDF hα) := rfl

/-- The library's Fisher–Tippett–Gnedenko, `IsExtremeValueDistr.classification`, in the form of the
challenge. -/
theorem fisher_tippett_gnedenko {F G : ℝ → ℝ} (hF : IsDistributionFunction F)
    (hG : IsDistributionFunction G) (hnd : ¬ Challenge.IsDegenerate G)
    (h : InDomainOfAttraction F G) :
    SameType G gumbel ∨ (∃ α > 0, SameType G (frechet α)) ∨ (∃ α > 0, SameType G (weibull α)) := by
  obtain ⟨As, hAs⟩ := (inDomainOfAttraction_iff (toCDF hF) (toCDF hG)).1 h
  have hEVD : (toCDF hG).IsExtremeValueDistr := ⟨hnd, toCDF hF, As, hAs⟩
  rcases hEVD.classification with ⟨A, hA⟩ | ⟨A, α, hα, hA⟩ | ⟨A, α, hα, hA⟩
  · exact Or.inl ((sameType_iff (toCDF hG) standardGumbelCDF).2 ⟨A, hA⟩)
  · exact Or.inr (Or.inl ⟨α, hα, (sameType_iff (toCDF hG) (standardFrechetCDF hα)).2 ⟨A, hA⟩⟩)
  · exact Or.inr (Or.inr ⟨α, hα, (sameType_iff (toCDF hG) (standardWeibullCDF hα)).2 ⟨A, hA⟩⟩)

/-! ## Pickands–Balkema–de Haan -/

/-- `gev ξ` is the library's `gevCDF ξ`. -/
theorem gev_eq (ξ : ℝ) : gev ξ = ⇑(ExtremeValueTheory.gevCDF ξ) :=
  (ExtremeValueTheory.coe_gevCDF ξ).symm

/-- `gpdSurvival ξ` is the library's `gpdSurvivalAll ξ 1`. -/
theorem gpdSurvival_eq (ξ : ℝ) : gpdSurvival ξ = ExtremeValueTheory.gpdSurvivalAll ξ 1 := by
  funext x
  simp [gpdSurvival, ExtremeValueTheory.gpdSurvivalAll]

/-- `toRightEndpoint` is the library's `upperEndpointFilter`. -/
theorem toRightEndpoint_eq (F : CumulativeDistributionFunction) :
    toRightEndpoint F = F.upperEndpointFilter := rfl

/-- The excess ratio of the challenge is the library's `excessSurvival`. -/
theorem excessSurvival_eq (F : ℝ → ℝ) (u x : ℝ) :
    ExtremeValueTheory.excessSurvival (fun y ↦ 1 - F y) u x = (1 - F (u + x)) / (1 - F u) := rfl

/-- The limits in `InDomainOfAttraction` do not change under the action of `A` on the limit. -/
theorem inDomainOfAttraction_smul {F G : CumulativeDistributionFunction} (A : AffineIncrEquiv)
    (h : InDomainOfAttraction F G) : InDomainOfAttraction F (A • G : CumulativeDistributionFunction) := by
  obtain ⟨As, hAs⟩ := (inDomainOfAttraction_iff F G).1 h
  refine (inDomainOfAttraction_iff F _).2 ⟨fun n ↦ A * As n, fun x hx ↦ ?_⟩
  have hG := affine_continuousAt_of_continuousAt hx A⁻¹
  simp only [inv_smul_smul] at hG
  exact hAs (A⁻¹ x) hG

theorem inDomainOfAttraction_smul_iff {F G : CumulativeDistributionFunction} (A : AffineIncrEquiv) :
    InDomainOfAttraction F (A • G : CumulativeDistributionFunction) ↔ InDomainOfAttraction F G :=
  ⟨fun h ↦ by simpa using inDomainOfAttraction_smul A⁻¹ h, inDomainOfAttraction_smul A⟩

/-- For a continuous limit, convergence at continuity points is convergence everywhere, the form of
the library's `IsInMDA…`. -/
theorem inDomainOfAttraction_iff_of_continuous (F : CumulativeDistributionFunction)
    {S : CumulativeDistributionFunction} (hS : Continuous S) :
    InDomainOfAttraction F S ↔ ∃ As : ℕ → AffineIncrEquiv,
      ∀ x, Tendsto (fun n ↦ ((As n • F) x) ^ n) atTop (𝓝 (S x)) := by
  rw [inDomainOfAttraction_iff]
  exact exists_congr fun As ↦ ⟨fun h x ↦ h x hS.continuousAt, fun h x _ ↦ h x⟩

theorem continuous_gumbel : Continuous (standardGumbelCDF : ℝ → ℝ) := by
  rw [← gumbel_eq]; unfold gumbel; fun_prop

theorem continuous_weibull {α : ℝ} (hα : 0 < α) : Continuous (standardWeibullCDF hα : ℝ → ℝ) := by
  have : (standardWeibullCDF hα : ℝ → ℝ) = fun x ↦ Real.exp (-((max (-x) 0) ^ α)) :=
    funext (standardWeibullAux_eq hα)
  rw [this]
  exact Real.continuous_exp.comp ((Real.continuous_rpow_const hα.le).comp
    (continuous_neg.max continuous_const)).neg

/-- `InDomainOfAttraction F (gev ξ)` is the library's `IsInMDAGEV ξ`. -/
theorem inDomainOfAttraction_gev_iff (F : CumulativeDistributionFunction) (ξ : ℝ) :
    InDomainOfAttraction F (gev ξ) ↔ F.IsInMDAGEV ξ := by
  rw [gev_eq]
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · rw [isInMDAGEV_iff_of_neg hξ, IsInMDAWeibull,
      ← inDomainOfAttraction_iff_of_continuous F (continuous_weibull _),
      ← ExtremeValueTheory.mkOfCoefs_smul_gevCDF_of_neg hξ, inDomainOfAttraction_smul_iff]
  · rw [isInMDAGEV_zero_iff, IsInMDAGumbel, ← inDomainOfAttraction_iff_of_continuous F continuous_gumbel,
      ExtremeValueTheory.gevCDF_zero]
  · rw [isInMDAGEV_iff_of_pos hξ, IsInMDAFrechet,
      ← inDomainOfAttraction_iff_of_continuous F (continuous_standardFrechetAux (one_div_pos.2 hξ)),
      ← ExtremeValueTheory.mkOfCoefs_smul_gevCDF_of_pos hξ, inDomainOfAttraction_smul_iff]

/-- The library's Pickands–Balkema–de Haan, `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival`,
in the form of the challenge. -/
theorem pickands_balkema_de_haan {F : ℝ → ℝ} (hF : IsDistributionFunction F) (ξ : ℝ) :
    InDomainOfAttraction F (gev ξ) ↔
      ∃ β : ℝ → ℝ, (∀ᶠ u in toRightEndpoint F, 0 < β u) ∧
        TendstoUniformlyOn (fun u x ↦ (1 - F (u + β u * x)) / (1 - F u)) (gpdSurvival ξ)
          (toRightEndpoint F) (Set.Ici 0) := by
  have h := (inDomainOfAttraction_gev_iff (toCDF hF) ξ).trans
    ((toCDF hF).isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival ξ)
  rw [gpdSurvival_eq]
  exact h

/-! ## The Hill estimator -/

/-- `IsRegularlyVarying` is the library's. -/
theorem isRegularlyVarying_iff (f : ℝ → ℝ) (ρ : ℝ) :
    Challenge.IsRegularlyVarying f ρ ↔ ExtremeValueTheory.IsRegularlyVarying f ρ := Iff.rfl

/-- `orderStat` is the library's. -/
theorem orderStat_eq {n : ℕ} (x : Fin n → ℝ) (j : ℕ) :
    Challenge.orderStat x j = ExtremeValueTheory.orderStat x j := rfl

/-- `hill` is the library's. -/
theorem hill_eq {n : ℕ} (x : Fin n → ℝ) (k : ℕ) :
    Challenge.hill x k = ExtremeValueTheory.hill x k := rfl

/-! ## The echo process -/

/-- `echoProcess` is the library's. -/
theorem echoProcess_eq {Ω : Type*} (L : ℝ → ℕ) (Z : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    Challenge.echoProcess L Z t ω = ExtremeValueTheory.echoProcess L Z t ω := rfl

/-- `powLag` is the library's. -/
theorem powLag_eq (γ z : ℝ) : Challenge.powLag γ z = ExtremeValueTheory.powLag γ z := rfl

/-- `AntiClustering` is the library's. -/
theorem antiClustering_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℤ → Ω → ℝ)
    (a : ℕ → ℝ) (r : ℕ → ℕ) :
    Challenge.AntiClustering P X a r ↔ ExtremeValueTheory.AntiClustering P X a r := Iff.rfl

end Solution

namespace Challenge

theorem fisher_tippett_gnedenko {F G : ℝ → ℝ} (hF : IsDistributionFunction F)
    (hG : IsDistributionFunction G) (hnd : ¬ IsDegenerate G) (h : InDomainOfAttraction F G) :
    SameType G gumbel ∨ (∃ α > 0, SameType G (frechet α)) ∨ (∃ α > 0, SameType G (weibull α)) :=
  Solution.fisher_tippett_gnedenko hF hG hnd h

theorem pickands_balkema_de_haan {F : ℝ → ℝ} (hF : IsDistributionFunction F) (ξ : ℝ) :
    InDomainOfAttraction F (gev ξ) ↔
      ∃ β : ℝ → ℝ, (∀ᶠ u in toRightEndpoint F, 0 < β u) ∧
        TendstoUniformlyOn (fun u x ↦ (1 - F (u + β u * x)) / (1 - F u)) (gpdSurvival ξ)
          (toRightEndpoint F) (Set.Ici 0) :=
  Solution.pickands_balkema_de_haan hF ξ

theorem hill_consistent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x ↦ (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n ↦ (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω ↦ hill (fun i : Fin n ↦ X i ω) (k n)) atTop (fun _ ↦ 1 / α) :=
  ExtremeValueTheory.tendstoInMeasure_hill hX hindep hident hα hRV hk hkn

theorem echo_anticlustering_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {α γ : ℝ} {Z : ℤ → Ω → ℝ} (hα : 0 < α) (hZ : ∀ t, Measurable (Z t))
    (hind : iIndepFun Z P) (hlaw : ∀ t, P.map (Z t) = paretoMeasure 1 α) (hpos : ∀ t ω, 0 ≤ Z t ω)
    (hγ : 0 < γ) (hγα : γ < α) {a : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : Tendsto (fun n : ℕ ↦ n * P.real {ω | a n < echoProcess (powLag γ) Z 0 ω}) atTop (𝓝 τ))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρ : ρ ≠ γ / α) {r : ℕ → ℕ}
    (hr : Tendsto (fun n : ℕ ↦ Real.log (r n) / Real.log n) atTop (𝓝 ρ)) :
    AntiClustering P (echoProcess (powLag γ) Z) a r ↔ ρ < γ / α :=
  ExtremeValueTheory.powEchoProcess_antiClustering_iff hα hZ hind hlaw hpos hγ hγα hτ0 hτ hρ0 hρ1 hρ hr

end Challenge
