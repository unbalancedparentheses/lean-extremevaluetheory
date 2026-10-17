/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Dependence.ARMAX
import ExtremeValueTheory.Dependence.InfiniteMovingAverageTailProcess

/-!
# Markov tail chains

Let `X_{t+1} = f(X_t, V_t)` be a Markov chain driven by iid innovations (`RandomIteration`), and
suppose the transition is *asymptotically multiplicative*: there are measurable `a, b` with

  `|f(x, v) - a(v) x| ≤ b(v)`  for all states `x` in an invariant set `K`.

Then `f(x y, v) / x → a(v) y` as `x → ∞`, i.e. the law of `X_1 / x` given `X_0 = x` converges to
the law of `A = a(V_0)`: this is the regular-variation condition on the kernel of [Smith 1992],
[Perfekt 1994] and [Janssen–Segers 2014, "Markov tail chains"], in the random-function form of
[Segers 2007]. Examples are the ARMAX chain `max(φ x, v)` (`a ≡ φ`, `b(v) = |v|`, `K = [0, ∞)`)
and the random coefficient autoregression `A x + B` (`a(A, B) = A`, `b(A, B) = |B|`, `K = ℝ`).

**Theorem** (forward tail chain). If moreover the law of `X_0 / x` given `X_0 ∈ S_x` (e.g.
`S_x = (x, ∞)` or `{|X_0| > x}`) converges weakly to `μ₀`, then for every horizon `k` the law of
`(X_0 / x, …, X_k / x)` given `X_0 ∈ S_x` converges to the law of the **multiplicative random
walk**

  `Y_t = Y_0 A_1 ⋯ A_t`,  `Y_0 ~ μ₀`,  `A_{s+1} = a(V_s)` iid, independent of `Y_0`

(`tendstoLawCond_tailChain`, `tendstoLawCond_tailChain_iid`). The proof compares `X_t` with
`X_0 a(V_0) ⋯ a(V_{t-1})`: the difference is bounded by a random variable `errBound` of the
innovations alone, so after division by `x` it vanishes in conditional probability, while the
innovations are independent of the conditioning event.

## Main results

* `ExtremeValueTheory.RandomIteration.abs_iter_sub_tailWalk_le`: the deterministic comparison.
* `ExtremeValueTheory.RandomIteration.tendstoLawCond_tailChain`: the forward tail chain.
* `ExtremeValueTheory.RandomIteration.candidateExtremalIndex_tailWalk`: for a nonnegative tail
  chain with `Y_0` Pareto, the candidate extremal index of the spectral chain
  `Θ_t = A_1 ⋯ A_t` is `ϑ = P(sup_{t ≥ 1} Y_0 A_1 ⋯ A_t ≤ 1)` [Perfekt 1994,
  Janssen–Segers 2014].
* `ExtremeValueTheory.ARMAX.tendstoLawCond_tailChain`: the tail chain of ARMAX is
  `Y_t = Y_0 φ^t` with `Y_0` Pareto(`α`) (`A ≡ φ`).
* `ExtremeValueTheory.ARMAX.candidateExtremalIndex_tailChain`: its candidate extremal index is
  `ϑ = P(φ Y_0 ≤ 1) = 1 - φ^α`, and `ExtremeValueTheory.ARMAX.hasExtremalIndex_candidate`:
  **`θ = ϑ = 1 - φ^α`** for the stationary ARMAX chain.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Finset BoundedContinuousFunction
open scoped ENNReal

namespace ExtremeValueTheory

namespace RandomIteration

variable {F : Type*} [MeasurableSpace F] {f : ℝ → F → ℝ} {a b : F → ℝ}

/-- The multiplicative random walk `y a(v_0) ⋯ a(v_{t-1})`. -/
def tailWalk (a : F → ℝ) (y : ℝ) (v : ℕ → F) (t : ℕ) : ℝ := y * ∏ s ∈ range t, a (v s)

/-- The accumulated error `e_0 = 0`, `e_{t+1} = |a(v_t)| e_t + b(v_t)`. -/
def errBound (a b : F → ℝ) (v : ℕ → F) : ℕ → ℝ
  | 0 => 0
  | t + 1 => |a (v t)| * errBound a b v t + b (v t)

omit [MeasurableSpace F] in
theorem errBound_nonneg (hb : ∀ v, 0 ≤ b v) (v : ℕ → F) (t : ℕ) : 0 ≤ errBound a b v t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact add_nonneg (mul_nonneg (abs_nonneg _) ih) (hb _)

theorem measurable_errBound (ha : Measurable a) (hb : Measurable b) (t : ℕ) :
    Measurable fun v : ℕ → F => errBound a b v t := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact ((continuous_abs.measurable.comp (ha.comp (measurable_pi_apply t))).mul ih).add
      (hb.comp (measurable_pi_apply t))

theorem measurable_tailWalk (ha : Measurable a) (t : ℕ) :
    Measurable fun p : ℝ × (ℕ → F) => tailWalk a p.1 p.2 t :=
  measurable_fst.mul (Finset.measurable_prod _ fun s _ =>
    ha.comp ((measurable_pi_apply s).comp measurable_snd))

omit [MeasurableSpace F] in
/-- **Comparison with the multiplicative random walk.** If `K` is invariant under `f` and
`|f(x, v) - a(v) x| ≤ b(v)` on `K`, then `|x_t - x_0 a(v_0) ⋯ a(v_{t-1})| ≤ e_t`. -/
theorem abs_iter_sub_tailWalk_le {K : Set ℝ} (hK : ∀ x ∈ K, ∀ v, f x v ∈ K)
    (hfab : ∀ x ∈ K, ∀ v, |f x v - a v * x| ≤ b v) {x : ℝ} (hx : x ∈ K) (v : ℕ → F) (t : ℕ) :
    iter f x v t ∈ K ∧ |iter f x v t - tailWalk a x v t| ≤ errBound a b v t := by
  induction t with
  | zero => simpa [tailWalk, errBound] using hx
  | succ t ih =>
    refine ⟨hK _ ih.1 _, ?_⟩
    rw [iter_succ, errBound, tailWalk, Finset.prod_range_succ]
    have e : f (iter f x v t) (v t) - x * ((∏ s ∈ range t, a (v s)) * a (v t)) =
        (f (iter f x v t) (v t) - a (v t) * iter f x v t) +
          a (v t) * (iter f x v t - tailWalk a x v t) := by
      simp only [tailWalk]; ring
    rw [e]
    calc _ ≤ |f (iter f x v t) (v t) - a (v t) * iter f x v t| +
          |a (v t) * (iter f x v t - tailWalk a x v t)| := abs_add_le _ _
      _ ≤ b (v t) + |a (v t)| * errBound a b v t := by
          rw [abs_mul]
          gcongr
          · exact hfab _ ih.1 _
          · exact ih.2
      _ = _ := by ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

omit [MeasurableSpace F] in
/-- Under the conditional probability given an event of `X₀`, the variable `X₀` stays independent
of `W`, and `W` keeps its law. -/
theorem map_cond_prod {G : Type*} [MeasurableSpace G] {X₀ : Ω → ℝ} {W : Ω → G}
    (hX₀ : Measurable X₀) (hW : Measurable W) (hind : IndepFun X₀ W P) {S : Set ℝ}
    (hS : MeasurableSet S) [IsFiniteMeasure P] :
    (P[|X₀ ⁻¹' S]).map (fun ω => (X₀ ω, W ω)) = ((P[|X₀ ⁻¹' S]).map X₀).prod (P.map W) := by
  refine (Measure.prod_eq fun A B hA hB => ?_).symm
  rw [Measure.map_apply (hX₀.prodMk hW) (hA.prod hB), Measure.map_apply hX₀ hA,
    Measure.map_apply hW hB, cond_apply (hX₀ hS), cond_apply (hX₀ hS)]
  have e1 : X₀ ⁻¹' S ∩ (fun ω => (X₀ ω, W ω)) ⁻¹' (A ×ˢ B) = X₀ ⁻¹' (S ∩ A) ∩ W ⁻¹' B := by
    ext ω; simp [and_assoc]
  have e2 : X₀ ⁻¹' S ∩ X₀ ⁻¹' A = X₀ ⁻¹' (S ∩ A) := rfl
  rw [e1, e2, hind.measure_inter_preimage_eq_mul _ _ (hS.inter hA) hB, mul_assoc]

section TailChain

variable [IsProbabilityMeasure P] {X₀ : Ω → ℝ} {V : ℕ → Ω → F}

/-- **The forward tail chain of an asymptotically multiplicative Markov chain**
([Janssen–Segers 2014, Theorem 2.3], [Perfekt 1994], [Segers 2007], [KS20, Chapter 14]).
Let `X_{t+1} = f(X_t, V_t)` with `X₀` independent of the innovations `V`, `X₀ ∈ K` almost
surely for an `f`-invariant measurable set `K` on which `|f(x, v) - a(v) x| ≤ b(v)`. If the law of
`X_0 / x` given `X_0 ∈ S_x` converges weakly to `μ₀`, then for every `k` the law of
`(X_t / x)_{t ≤ k}` given `X_0 ∈ S_x` converges to the law of `(Y_0 a(V_0) ⋯ a(V_{t-1}))_{t ≤ k}`
with `Y_0 ~ μ₀` independent of `V`. -/
theorem tendstoLawCond_tailChain (hf : Measurable (Function.uncurry f)) (ha : Measurable a)
    (hb : Measurable b) {K : Set ℝ} (hKm : MeasurableSet K) (hK : ∀ x ∈ K, ∀ v, f x v ∈ K)
    (hfab : ∀ x ∈ K, ∀ v, |f x v - a v * x| ≤ b v) (hX₀ : Measurable X₀)
    (hX₀K : ∀ᵐ ω ∂P, X₀ ω ∈ K) (hV : ∀ n, Measurable (V n))
    (hind : IndepFun X₀ (fun ω n => V n ω) P) {S : ℝ → Set ℝ} (hS : ∀ x, MeasurableSet (S x))
    {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀]
    (hX0 : TendstoLawCond P (fun x => X₀ ⁻¹' S x) (fun x ω => X₀ ω / x) atTop μ₀) (k : ℕ) :
    TendstoLawCond P (fun x => X₀ ⁻¹' S x)
      (fun x ω (t : Fin (k + 1)) => chain f X₀ V t ω / x) atTop
      ((μ₀.prod (P.map fun ω n => V n ω)).map fun p (t : Fin (k + 1)) => tailWalk a p.1 p.2 t) := by
  set L := P.map fun ω n => V n ω
  have hVm : Measurable fun ω n => V n ω := Measurable.of_eval hV
  set Φ : ℝ × (ℕ → F) → (Fin (k + 1) → ℝ) := fun p t => tailWalk a p.1 p.2 t
  have hΦ : Measurable Φ := Measurable.of_eval fun t => measurable_tailWalk ha t
  have hΦc : ∀ v, Continuous fun y => Φ (y, v) := fun v =>
    continuous_pi fun t => by simp only [Φ, tailWalk]; exact continuous_id.mul continuous_const
  have hbabs : ∀ v, 0 ≤ b v := fun v => by
    rcases Set.eq_empty_or_nonempty K with hKe | ⟨x, hx⟩
    · -- `K` empty: then `X₀ ∈ K` cannot hold almost surely
      exfalso
      have : ∀ᵐ ω ∂P, False := hX₀K.mono fun ω h => by simp [hKe] at h
      simp [ae_iff] at this
    · exact (abs_nonneg _).trans (hfab x hx v)
  -- Step 1: the approximating multiplicative random walk
  have hA : TendstoLawCond P (fun x => X₀ ⁻¹' S x)
      (fun x ω => Φ (X₀ ω / x, fun n => V n ω)) atTop (Measure.map Φ (μ₀.prod L)) := by
    intro g
    have hgb : ∀ z, |g z| ≤ ‖g‖ := fun z => by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm z
    set h : ℝ → ℝ := fun y => ∫ v, g (Φ (y, v)) ∂L
    have hgΦ : Measurable fun p : ℝ × (ℕ → F) => g (Φ p) := g.continuous.measurable.comp hΦ
    have hcont : Continuous h := by
      refine continuous_of_dominated (bound := fun _ => ‖g‖) (fun y => ?_) (fun y => ?_)
        (integrable_const _) (Eventually.of_forall fun v => g.continuous.comp (hΦc v))
      · exact (hgΦ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      · exact Eventually.of_forall fun v => by simpa [Real.norm_eq_abs] using hgb _
    have hhb : ∀ y, |h y| ≤ ‖g‖ := fun y => by
      have := norm_integral_le_of_norm_le_const (μ := L) (C := ‖g‖) (f := fun v => g (Φ (y, v)))
        (Eventually.of_forall fun v => by simpa [Real.norm_eq_abs] using hgb _)
      simpa [Real.norm_eq_abs, L, measureReal_def] using this
    set hB : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨h, hcont⟩ (2 * ‖g‖) fun y y' => by
      rw [Real.dist_eq]
      have := hhb y; have := hhb y'
      calc |h y - h y'| ≤ |h y| + |h y'| := abs_sub _ _
        _ ≤ 2 * ‖g‖ := by linarith
    have key := hX0 hB
    have hlim : ∫ y, hB y ∂μ₀ = ∫ z, g z ∂(Measure.map Φ (μ₀.prod L)) := by
      rw [integral_map hΦ.aemeasurable g.continuous.aestronglyMeasurable,
        integral_prod _ (integrable_of_abs_le hgΦ fun p => hgb _)]
      rfl
    rw [← hlim]
    refine key.congr fun x => ?_
    set s := X₀ ⁻¹' S x
    have hmeas : Measurable fun p : ℝ × (ℕ → F) => g (Φ (p.1 / x, p.2)) :=
      hgΦ.comp ((measurable_fst.div_const x).prodMk measurable_snd)
    have e1 : ∫ ω, g (Φ (X₀ ω / x, fun n => V n ω)) ∂P[|s] =
        ∫ p, g (Φ (p.1 / x, p.2)) ∂((P[|s]).map fun ω => (X₀ ω, fun n => V n ω)) :=
      (integral_map (hX₀.prodMk hVm).aemeasurable hmeas.aestronglyMeasurable).symm
    rw [e1, map_cond_prod hX₀ hVm hind (hS x),
      integral_prod _ (integrable_of_abs_le hmeas fun p => hgb _),
      integral_map hX₀.aemeasurable]
    · rfl
    · exact (hcont.comp (continuous_id.div_const x)).aestronglyMeasurable
  -- Step 2: the chain is close to the random walk, uniformly off an event independent of `X₀`
  set M : Ω → ℝ := fun ω => ∑ t ∈ range (k + 1), errBound a b (fun n => V n ω) t
  have hMm : Measurable M := Finset.measurable_sum _ fun t _ =>
    (measurable_errBound ha hb t).comp hVm
  have hMt := (ARMAX.tendsto_survival (P := P) hMm)
  have hXm : ∀ t, Measurable (chain f X₀ V t) := measurable_chain hf hX₀ hV
  have hpos : ∀ᶠ x in atTop, 0 < P.real (X₀ ⁻¹' S x) := by
    filter_upwards [hX0.eventually_measure_ne_zero] with x hx
    exact ENNReal.toReal_pos hx (measure_ne_top _ _)
  refine tendstoLawCond_of_approx (Bm := fun _ => fun x => X₀ ⁻¹' S x)
    (Vm := fun _ x ω => Φ (X₀ ω / x, fun n => V n ω)) (νm := fun _ => Measure.map Φ (μ₀.prod L))
    (fun x => hX₀ (hS x)) (fun _ x => hX₀ (hS x))
    (fun x => Measurable.of_eval fun t => (hXm t).div_const x)
    (fun _ x => hΦ.comp ((hX₀.div_const x).prodMk hVm)) hpos
    (Eventually.of_forall fun _ => hA) (fun _ => tendsto_const_nhds) ?_
  intro ε hε η hη
  refine Eventually.of_forall fun _ => ?_
  have hεx : Tendsto (fun x : ℝ => ε * x) atTop atTop := tendsto_id.const_mul_atTop hε
  filter_upwards [eventually_gt_atTop 0, (hMt.comp hεx).eventually (gt_mem_nhds hη)]
    with x hx hMx
  set D := {ω | ε * x < M ω} ∪ X₀ ⁻¹' Kᶜ
  have hNull : P (X₀ ⁻¹' Kᶜ) = 0 := ae_iff.1 hX₀K
  refine ⟨D, (measurableSet_lt measurable_const hMm).union (hX₀ hKm.compl), fun ω hω => ?_, ?_⟩
  · simp only [D, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, Set.mem_preimage,
      Set.mem_compl_iff, not_not] at hω
    rw [dist_pi_le_iff hε.le]
    intro t
    have hb' := abs_iter_sub_tailWalk_le hK hfab hω.2 (fun n => V n ω) t
    have hle : errBound a b (fun n => V n ω) t ≤ M ω :=
      Finset.single_le_sum (f := fun t => errBound a b (fun n => V n ω) t)
        (fun t _ => errBound_nonneg hbabs _ t) (Finset.mem_range.2 t.2)
    rw [Real.dist_eq]
    show |chain f X₀ V t ω / x - tailWalk a (X₀ ω / x) (fun n => V n ω) t| ≤ ε
    have e : chain f X₀ V t ω / x - tailWalk a (X₀ ω / x) (fun n => V n ω) t =
        (iter f (X₀ ω) (fun n => V n ω) t - tailWalk a (X₀ ω) (fun n => V n ω) t) / x := by
      simp only [chain, tailWalk]; ring
    rw [e, abs_div, abs_of_pos hx, div_le_iff₀ hx]
    linarith [hb'.2]
  · simp only [sdiff_self, measureReal_empty, zero_add]
    have hD : P.real (X₀ ⁻¹' S x ∩ D) ≤ P.real (X₀ ⁻¹' S x ∩ {ω | ε * x < M ω}) := by
      rw [Set.inter_union_distrib_left]
      refine (measureReal_union_le _ _).trans ?_
      have : P.real (X₀ ⁻¹' S x ∩ X₀ ⁻¹' Kᶜ) = 0 := by
        rw [measureReal_def, measure_mono_null inter_subset_right hNull, ENNReal.toReal_zero]
      linarith
    have hindD : P.real (X₀ ⁻¹' S x ∩ {ω | ε * x < M ω}) =
        P.real (X₀ ⁻¹' S x) * P.real {ω | ε * x < M ω} := by
      have hC : MeasurableSet {v : ℕ → F | ε * x < ∑ t ∈ range (k + 1), errBound a b v t} :=
        measurableSet_lt measurable_const
          (Finset.measurable_sum _ fun t _ => measurable_errBound ha hb t)
      have := hind.measure_inter_preimage_eq_mul _ _ (hS x) hC
      simp only [measureReal_def]
      rw [← ENNReal.toReal_mul]
      exact congrArg ENNReal.toReal this
    have hMx' : P.real {ω | ε * x < M ω} < η := hMx
    calc P.real (X₀ ⁻¹' S x ∩ D) ≤ P.real (X₀ ⁻¹' S x) * P.real {ω | ε * x < M ω} :=
          hD.trans hindD.le
      _ ≤ P.real (X₀ ⁻¹' S x) * η := by gcongr
      _ = η * P.real (X₀ ⁻¹' S x) := mul_comm _ _

/-- **The forward tail chain for iid innovations**: `Y_t = Y_0 A_1 ⋯ A_t` with `Y_0 ~ μ₀` and
`A_{s+1} = a(V_s)` iid, independent of `Y_0`; the limit law is the image of `μ₀ ⊗ ν^⊗ℕ`. -/
theorem tendstoLawCond_tailChain_iid (hf : Measurable (Function.uncurry f)) (ha : Measurable a)
    (hb : Measurable b) {K : Set ℝ} (hKm : MeasurableSet K) (hK : ∀ x ∈ K, ∀ v, f x v ∈ K)
    (hfab : ∀ x ∈ K, ∀ v, |f x v - a v * x| ≤ b v) (hX₀ : Measurable X₀)
    (hX₀K : ∀ᵐ ω ∂P, X₀ ω ∈ K) (hV : ∀ n, Measurable (V n))
    (hind : IndepFun X₀ (fun ω n => V n ω) P) (hiid : iIndepFun V P) {ν : Measure F}
    (hlaw : ∀ n, P.map (V n) = ν) {S : ℝ → Set ℝ} (hS : ∀ x, MeasurableSet (S x))
    {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀]
    (hX0 : TendstoLawCond P (fun x => X₀ ⁻¹' S x) (fun x ω => X₀ ω / x) atTop μ₀) (k : ℕ) :
    TendstoLawCond P (fun x => X₀ ⁻¹' S x)
      (fun x ω (t : Fin (k + 1)) => chain f X₀ V t ω / x) atTop
      ((μ₀.prod (Measure.infinitePi fun _ : ℕ => ν)).map
        fun p (t : Fin (k + 1)) => tailWalk a p.1 p.2 t) := by
  rw [← map_path_eq_infinitePi hV hiid hlaw]
  exact tendstoLawCond_tailChain hf ha hb hKm hK hfab hX₀ hX₀K hV hind hS hX0 k

end TailChain

/-! ### The candidate extremal index of a multiplicative tail chain -/

/-- The spectral tail chain `Θ_t = a(v_0) ⋯ a(v_{t-1})` (for `t ≥ 0`; `Θ_t = 0` for `t < 0`). -/
noncomputable def spectralWalk (a : F → ℝ) (t : ℤ) (v : ℕ → F) : ℝ :=
  if 0 ≤ t then ∏ s ∈ range t.toNat, a (v s) else 0

/-- **The extremal index of a Markov tail chain** [Perfekt 1994], [Janssen–Segers 2014]: with
`Y_0` Pareto(`α`) independent of the multiplicative walk,
`ϑ = E[sup_{t ≥ 0} |Θ_t|^α - sup_{t ≥ 1} |Θ_t|^α] = P(sup_{t ≥ 1} Y_0 |A_1 ⋯ A_t| ≤ 1)`. -/
theorem candidateExtremalIndex_tailWalk {α : ℝ} (hα : 0 < α) (ha : Measurable a)
    (Q : Measure (ℕ → F)) [IsProbabilityMeasure Q] :
    candidateExtremalIndex Q (spectralWalk a) α =
      ((paretoMeasure 1 α).prod Q) {p | ∀ k : ℕ, p.1 * |∏ s ∈ range (k + 1), a (p.2 s)| ≤ 1} := by
  have hm : ∀ t, Measurable (spectralWalk a t) := fun t => by
    unfold spectralWalk
    split_ifs
    · exact Finset.measurable_prod _ fun s _ => ha.comp (measurable_pi_apply s)
    · exact measurable_const
  rw [candidateExtremalIndex_eq_measure hα hm (Eventually.of_forall fun v => by
    simp [spectralWalk])]
  congr 1

end RandomIteration

/-! ### The ARMAX tail chain -/

namespace ARMAX

variable {φ α : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X₀ : Ω → ℝ} {V : ℕ → Ω → ℝ}

theorem step_nonneg (hφ0 : 0 ≤ φ) {x : ℝ} (hx : 0 ≤ x) (v : ℝ) : 0 ≤ step φ x v :=
  (mul_nonneg hφ0 hx).trans (le_max_left _ _)

theorem abs_step_sub_le (hφ0 : 0 ≤ φ) {x : ℝ} (hx : 0 ≤ x) (v : ℝ) :
    |step φ x v - φ * x| ≤ |v| := by
  have h0 : 0 ≤ φ * x := mul_nonneg hφ0 hx
  rw [step, abs_of_nonneg (sub_nonneg.2 (le_max_left _ _))]
  rcases le_total (φ * x) v with h | h
  · rw [max_eq_right h]; linarith [le_abs_self v]
  · rw [max_eq_left h, sub_self]; exact abs_nonneg v

variable (hφ0 : 0 < φ) (hφ1 : φ < 1) (hα : 0 < α) (hX₀ : Measurable X₀)
  (hV : ∀ n, Measurable (V n)) (hind : IndepFun X₀ (fun ω n => V n ω) P)
  (hiid : iIndepFun V P) (hlaw : ∀ n, P.map (V n) = paretoMeasure 1 α)
  (hinv : ((P.map X₀).prod (paretoMeasure 1 α)).map (Function.uncurry (step φ)) = P.map X₀)
include hφ0 hφ1 hα hX₀ hinv

omit hφ1 in
/-- The stationary ARMAX marginal is positive almost surely. -/
theorem ae_pos : ∀ᵐ ω ∂P, 0 < X₀ ω := by
  have h := (survival_rec hφ0 hα hX₀ hinv 0).2 one_pos
  have hm : MeasurableSet {ω | 0 < X₀ ω} := measurableSet_lt measurable_const hX₀
  have hc := probReal_compl_eq_one_sub (μ := P) hm
  rw [show P.real {ω | 0 < X₀ ω} = 1 from h, sub_self] at hc
  rw [ae_iff]
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hc

end ARMAX

end ExtremeValueTheory
