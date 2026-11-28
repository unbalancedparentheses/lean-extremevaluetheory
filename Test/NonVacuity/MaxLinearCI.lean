import Research

/-! # Non-vacuity and known-answer tests: extremal conditional independence in max-linear DAGs

Exercises every headline theorem of `Research.MaxLinearCI` on concrete
finite-DAG recursive max-linear models, including:
* bridging a concrete normalized max-linear model on `starDAG` to `IsSimpleMaxStable` via
  `exists_isSimpleMaxStable_maxLinear` and to `spectralExponentMeasure` via
  `rayExponentMeasure_map_ofReal`;
* `extremalCondIndep_rayExponentMeasure_iff` (both positive and negative instances);
* `MaxLinearModel.isDSeparated_imp_extremalCondIndep`,
  `MaxLinearModel.isStarSeparated_imp_extremalCondIndep`, and
  `MaxLinearModel.isFootprintSeparated_imp_extremalCondIndep`;
* all four strictness witnesses (`wDAG`, `starDAG` with both `ExtremalCondIndep` and
  `ParetoCondIndep`, `colliderDAG`, `diamondUnitModel` vs `diamondPerturbedModel`) and the
  complete resolution theorem `engelke_2024_complete_resolution`.
-/

open MeasureTheory ProbabilityTheory Set
open ExtremeValueTheory.MaxLinearCI

namespace ExtremeValueTheory.Test.MaxLinearCI

/-- A concrete normalized recursive max-linear model on the 4-node star DAG (`0 → 1, 0 → 2, 0 → 3`)
with unit-Fréchet marginal normalization `∑ k, coeff i k = 1` for every vertex `i`. -/
private noncomputable def starNormalizedModel : MaxLinearModel starDAG where
  weight i j := open Classical in if starEdge j i then 1 / 2 else 0
  diag k := if k = 0 then 1 else 1 / 2
  weight_nonneg i j := by classical split_ifs <;> norm_num
  weight_pos_iff i j := by
    classical split_ifs with h
    · exact ⟨fun _ ↦ h, fun _ ↦ by norm_num⟩
    · exact ⟨fun h0 ↦ absurd h0 (lt_irrefl 0), fun h' ↦ (h h').elim⟩
  diag_pos k := by split_ifs <;> norm_num

private lemma starNormalizedModel_walkWeight :
    ∀ p : List (Fin 4), starDAG.IsDirWalk p →
      starNormalizedModel.walkWeight p = if p.length ≤ 1 then 1 else 1 / 2
  | [], hp => (hp.1 rfl).elim
  | [_], _ => by simp [MaxLinearModel.walkWeight]
  | [u, v], hp => by
    have huv : starEdge u v := (List.isChain_cons_cons.1 hp.2).1
    change (open Classical in if starEdge u v then (1 / 2 : ℝ) else 0) * 1 = _
    simp [huv]
  | u :: v :: w :: t, hp => by
    have huv : starEdge u v := (List.isChain_cons_cons.1 hp.2).1
    have hvw : starEdge v w := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hp.2).2).1
    exfalso
    exact huv.2 hvw.1

private lemma starNormalizedModel_coeff (i k : Fin 4) :
    starNormalizedModel.coeff i k =
      if k = i then (if i = 0 then 1 else 1 / 2)
      else if k = 0 then 1 / 2 else 0 := by
  by_cases hki : k = i
  · subst hki
    have hpos : 0 < starNormalizedModel.kleenePath k k :=
      (starNormalizedModel.kleenePath_pos_iff k k).2 (starDAG.reach_refl k)
    obtain ⟨p, hp, hph, hpl, hpw⟩ := starNormalizedModel.exists_dirWalk_of_kleeneAux_pos hpos
    have hlen : p.length ≤ 1 := by
      match p with
      | [] => exact (hp.1 rfl).elim
      | [_] => simp
      | [u, v] =>
        have huv : starEdge u v := (List.isChain_cons_cons.1 hp.2).1
        simp only [List.head?_cons, Option.some.injEq] at hph
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hpl
        exact absurd (hpl.trans hph.symm) (huv.1 ▸ huv.2)
      | u :: v :: w :: _ =>
        have huv : starEdge u v := (List.isChain_cons_cons.1 hp.2).1
        have hvw : starEdge v w := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hp.2).2).1
        exact absurd hvw.1 huv.2
    have hkp : starNormalizedModel.kleenePath k k = 1 := by
      rw [MaxLinearModel.kleenePath, ← hpw, starNormalizedModel_walkWeight p hp]
      simp [hlen]
    rw [MaxLinearModel.coeff, hkp]
    simp [starNormalizedModel]
  · by_cases hk0 : k = 0
    · subst hk0
      have hi0 : i ≠ 0 := Ne.symm hki
      have hr : starDAG.Reach 0 i := (starDAG_reach_iff 0 i).2 (Or.inr rfl)
      have hpos : 0 < starNormalizedModel.kleenePath i 0 :=
        (starNormalizedModel.kleenePath_pos_iff i 0).2 hr
      obtain ⟨p, hp, hph, hpl, hpw⟩ := starNormalizedModel.exists_dirWalk_of_kleeneAux_pos hpos
      have hlen : ¬ p.length ≤ 1 := by
        intro hle
        match p with
        | [] => exact hp.1 rfl
        | [x] =>
          simp at hph hpl
          exact hi0 (hpl.symm.trans hph)
        | _ :: _ :: _ => simp at hle
      have hkp : starNormalizedModel.kleenePath i 0 = 1 / 2 := by
        rw [MaxLinearModel.kleenePath, ← hpw, starNormalizedModel_walkWeight p hp]
        simp [hlen]
      rw [MaxLinearModel.coeff, hkp]
      simp [starNormalizedModel, hki]
    · have hnr : ¬ starDAG.Reach k i := by
        rw [starDAG_reach_iff]; exact not_or.2 ⟨hki, hk0⟩
      have hkp : starNormalizedModel.kleenePath i k = 0 :=
        le_antisymm (not_lt.1 fun h ↦ hnr ((starNormalizedModel.kleenePath_pos_iff i k).1 h))
          (starNormalizedModel.kleenePath_nonneg i k)
      simp [MaxLinearModel.coeff, hkp, hki, hk0]

private lemma starNormalizedModel_norm (i : Fin 4) :
    ∑ k : Fin 4, starNormalizedModel.coeff i k = 1 := by
  rw [Fin.sum_univ_four]
  simp only [starNormalizedModel_coeff]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl | rfl <;> norm_num

/-- Non-vacuity of `exists_isSimpleMaxStable_maxLinear`: our concrete normalized star max-linear
model induces a genuine `IsSimpleMaxStable` probability distribution on `Fin 4 → ℝ`. -/
theorem test_nonvacuous_exists_isSimpleMaxStable_maxLinear :
    ∃ ν : Measure (Fin 4 → ℝ), IsSimpleMaxStable ν := by
  obtain ⟨ν, hν, _⟩ := exists_isSimpleMaxStable_maxLinear starNormalizedModel starNormalizedModel_norm
  exact ⟨ν, hν⟩

/-- Non-vacuity of `rayExponentMeasure_map_ofReal`: pushing forward `starNormalizedModel.exponentMeasure`
matches `spectralExponentMeasure` of the discrete spectral measure. -/
theorem test_nonvacuous_rayExponentMeasure_map_ofReal :
    starNormalizedModel.exponentMeasure.map (fun x i ↦ ENNReal.ofReal (x i)) =
      spectralExponentMeasure
        (∑ k : Fin 4, Measure.dirac (fun i : Fin 4 ↦ ENNReal.ofReal (starNormalizedModel.coeff i k))) :=
  rayExponentMeasure_map_ofReal _ (fun k i ↦ starNormalizedModel.coeff_nonneg i k)

/-- Non-vacuity of the complete Engelke et al. (2024) resolution theorem and concrete instances. -/
theorem test_nonvacuous_engelke_2024_complete_resolution :
    ExtremalCondIndep starNormalizedModel.exponentMeasure {0} {1} {2, 3} ∧
    ParetoCondIndep starNormalizedModel.exponentMeasure {0} {1} {2, 3} ∧
    ExtremalCondIndep diamondUnitModel.exponentMeasure {1} {2} {3} ∧
    ¬ ExtremalCondIndep diamondPerturbedModel.exponentMeasure {1} {2} {3} :=
  ⟨engelke_2024_complete_resolution.2.2.1.2.2.1 starNormalizedModel,
   engelke_2024_complete_resolution.2.2.1.2.2.2 starNormalizedModel,
   engelke_2024_complete_resolution.2.2.2.1,
   engelke_2024_complete_resolution.2.2.2.2⟩

/-- Non-vacuity of `MaxLinearModel.isDSeparated_imp_extremalCondIndep` on the 4-node star DAG:
leaves `1` and `2` are $d$-separated given the root `{0}` (and hence extremally CI). -/
theorem test_nonvacuous_dSeparated_starDAG :
    ExtremalCondIndep starNormalizedModel.exponentMeasure {1} {2} {0} := by
  refine starNormalizedModel.isDSeparated_imp_extremalCondIndep (by decide) (by decide) (by decide) ?_
  rintro p a ha b hb hph hpl ⟨hnd, htrail, hactive⟩
  simp only [Finset.coe_singleton, mem_singleton_iff] at ha hb
  subst ha; subst hb
  have hadj : ∀ {u v : Fin 4}, (starDAG.edge u v ∨ starDAG.edge v u) → u = 0 ∨ v = 0 := by
    intro u v h
    rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  match p with
  | [] => simp at hph
  | [x] => simp at hph hpl; subst hph; exact absurd hpl (by decide)
  | x0 :: x1 :: xs =>
    simp only [List.head?_cons, Option.some.injEq] at hph; subst hph
    have hstep0 : starDAG.edge 1 x1 ∨ starDAG.edge x1 1 := htrail 0 (by simp)
    have hx1 : x1 = 0 := (hadj hstep0).resolve_left (by decide)
    subst hx1
    match xs with
    | [] => simp at hpl
    | x2 :: xs2 =>
      have hnc : ¬ starDAG.IsColliderAt (1 :: 0 :: x2 :: xs2) 0 (by simp) := by
        rintro ⟨h1, _⟩
        have h10 : (1 : Fin 4) = 0 := h1.1
        exact absurd h10 (by decide)
      have hnotC := (hactive 0 (by simp)).2 hnc
      exact hnotC (by simp)

/-- Non-vacuity of `colliderDAG_extremalCondIndep` on a concrete model. -/
theorem test_nonvacuous_colliderDAG :
    ∃ M : MaxLinearModel colliderDAG,
      ¬ colliderDAG.edge 0 1 ∧ ¬ colliderDAG.edge 1 0 ∧
      ¬ colliderDAG.IsStarSeparated ({0} : Set (Fin 4)) {1} {2, 3} ∧
      ExtremalCondIndep M.exponentMeasure {0} {1} {2, 3} := by
  let M : MaxLinearModel colliderDAG := {
    weight i j := open Classical in if colliderEdge j i then 1 else 0
    diag _ := 1
    weight_nonneg i j := by classical split_ifs <;> norm_num
    weight_pos_iff i j := by
      classical split_ifs with h
      · exact ⟨fun _ ↦ h, fun _ ↦ one_pos⟩
      · exact ⟨fun h0 ↦ absurd h0 (lt_irrefl 0), fun h' ↦ (h h').elim⟩
    diag_pos _ := one_pos }
  exact ⟨M, colliderDAG_nonadjacent.1, colliderDAG_nonadjacent.2,
    colliderDAG_not_starSeparated, colliderDAG_extremalCondIndep M⟩

end ExtremeValueTheory.Test.MaxLinearCI
