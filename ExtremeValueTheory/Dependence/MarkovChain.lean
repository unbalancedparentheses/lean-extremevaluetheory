/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.ForMathlib.Probability.Process.Stationary
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.ProductMeasure

/-!
# Markov chains as random iterations

A (time-homogeneous) Markov chain on a measurable space `E` with transition kernel `K` can be
realized as a *random iteration* (iterated random function)

  `X_0 = X₀`, `X_{n+1} = f(X_n, V_n)`,

where `X₀` has the initial law `π`, `(V_n)_n` is an iid sequence of *innovations* with law `ν`
independent of `X₀`, and `K(x, ·)` is the law of `f(x, V_0)` (`noiseKernel f ν`). This is the
representation used in the extremal theory of Markov chains, e.g. for the max-autoregressive
chain `X_{n+1} = max(φ X_n, Z_{n+1})` (`Dependence/ARMAX.lean`) and for the random coefficient
autoregression `X_{n+1} = A_{n+1} X_n + B_{n+1}` [Smith 1992; Perfekt 1994; Janssen–Segers 2014;
KS20, Chapter 14]. (On standard Borel spaces every Markov kernel admits such a representation;
we do not need this.)

## Main definitions

* `ExtremeValueTheory.RandomIteration.iter f x v`: the deterministic iteration
  `x, f(x, v_0), f(f(x, v_0), v_1), …`.
* `ExtremeValueTheory.RandomIteration.chain f X₀ V`: the random iteration driven by `V`.
* `ExtremeValueTheory.RandomIteration.noiseKernel f ν`: its transition kernel
  `x ↦ law of f(x, V_0)`.

## Main results

* `ExtremeValueTheory.RandomIteration.isStationary_chain`: **stationarity**. If `X₀ ⊥ (V_n)_n`,
  the `V_n` are iid with law `ν`, and the initial law `π` is invariant,
  `law(f(X₀, V_0)) = π` (i.e. `(π ⊗ ν).map f = π`, equivalently `K ∘ₘ π = π`,
  `noiseKernel_comp_eq`), then the chain is (strictly) stationary in the sense of
  `ProbabilityTheory.IsStationary`.
* `ExtremeValueTheory.RandomIteration.isStationary_canonicalChain`: **existence**: the chain built
  on the canonical space `E × (ℕ → F)` with the product measure `π ⊗ ν^⊗ℕ` (Mathlib's
  `Measure.infinitePi`, i.e. the Ionescu-Tulcea construction for a product kernel) satisfies all
  hypotheses, hence is a stationary Markov chain with marginal `π`.
-/

open MeasureTheory ProbabilityTheory

namespace ExtremeValueTheory

namespace RandomIteration

variable {E F : Type*} {f : E → F → E}

/-- The deterministic iteration `x_0 = x`, `x_{n+1} = f(x_n, v_n)`. -/
def iter (f : E → F → E) (x : E) (v : ℕ → F) : ℕ → E
  | 0 => x
  | n + 1 => f (iter f x v n) (v n)

@[simp] theorem iter_zero (x : E) (v : ℕ → F) : iter f x v 0 = x := rfl

theorem iter_succ (x : E) (v : ℕ → F) (n : ℕ) : iter f x v (n + 1) = f (iter f x v n) (v n) :=
  rfl

/-- One step of the iteration followed by the iteration with the shifted inputs. -/
theorem iter_succ' (x : E) (v : ℕ → F) (n : ℕ) :
    iter f x v (n + 1) = iter f (f x (v 0)) (fun k => v (k + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ, ih, iter_succ]

variable {Ω : Type*}

/-- The **random iteration** (Markov chain driven by the innovations `V`):
`X_0 = X₀` and `X_{n+1} = f(X_n, V_n)`. -/
def chain (f : E → F → E) (X₀ : Ω → E) (V : ℕ → Ω → F) (n : ℕ) (ω : Ω) : E :=
  iter f (X₀ ω) (fun k => V k ω) n

@[simp] theorem chain_zero (X₀ : Ω → E) (V : ℕ → Ω → F) : chain f X₀ V 0 = X₀ := rfl

theorem chain_succ (X₀ : Ω → E) (V : ℕ → Ω → F) (n : ℕ) (ω : Ω) :
    chain f X₀ V (n + 1) ω = f (chain f X₀ V n ω) (V n ω) := rfl

variable [MeasurableSpace E] [MeasurableSpace F] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem measurable_iter (hf : Measurable (Function.uncurry f)) (n : ℕ) :
    Measurable (fun p : E × (ℕ → F) => iter f p.1 p.2 n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih => exact hf.comp (ih.prodMk ((measurable_pi_apply n).comp measurable_snd))

theorem measurable_iter_path (hf : Measurable (Function.uncurry f)) :
    Measurable (fun p : E × (ℕ → F) => fun n => iter f p.1 p.2 n) :=
  Measurable.of_eval (measurable_iter hf)

theorem measurable_chain (hf : Measurable (Function.uncurry f)) {X₀ : Ω → E} {V : ℕ → Ω → F}
    (hX₀ : Measurable X₀) (hV : ∀ n, Measurable (V n)) (n : ℕ) :
    Measurable (chain f X₀ V n) :=
  (measurable_iter hf n).comp (hX₀.prodMk (Measurable.of_eval hV))

/-- The transition kernel of the random iteration: `K(x, ·)` is the law of `f(x, V_0)`. -/
noncomputable def noiseKernel (f : E → F → E) (ν : Measure F) : Kernel E E :=
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ Kernel.const E ν) (Function.uncurry f)

theorem noiseKernel_apply (hf : Measurable (Function.uncurry f)) (ν : Measure F)
    [IsProbabilityMeasure ν] (x : E) : noiseKernel f ν x = ν.map (f x) := by
  rw [noiseKernel, Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.const_apply,
    Kernel.deterministic_apply, Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

theorem isMarkovKernel_noiseKernel (hf : Measurable (Function.uncurry f)) (ν : Measure F)
    [IsProbabilityMeasure ν] : IsMarkovKernel (noiseKernel f ν) :=
  Kernel.IsMarkovKernel.map _ hf

/-- Invariance of `π` for the kernel, `K ∘ₘ π = π`, is the fixed point equation
`(π ⊗ ν).map f = π`. -/
theorem noiseKernel_comp_eq (hf : Measurable (Function.uncurry f)) (ν : Measure F)
    [IsProbabilityMeasure ν] (π : Measure E) [IsProbabilityMeasure π] :
    noiseKernel f ν ∘ₘ π = (π.prod ν).map (Function.uncurry f) := by
  have := isMarkovKernel_noiseKernel hf ν
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.map_apply hf hs,
    Measure.prod_apply (hf hs)]
  refine lintegral_congr fun x => ?_
  rw [noiseKernel_apply hf]
  exact Measure.map_apply (hf.comp measurable_prodMk_left : Measurable (f x)) hs

section Stationary

variable [IsProbabilityMeasure P] {X₀ : Ω → E} {V : ℕ → Ω → F}

omit [IsProbabilityMeasure P] in
/-- In an independent sequence, `V_0` is independent of the shifted sequence `(V_{n+1})_n`. -/
theorem indepFun_zero_shift (hV : ∀ n, Measurable (V n)) (hiid : iIndepFun V P) :
    IndepFun (V 0) (fun ω n => V (n + 1) ω) P := by
  have h := hiid.indepFun_set {0} {n | 1 ≤ n} (by
    rw [Set.disjoint_left]; intro a ha hb; simp only [Set.mem_singleton_iff] at ha
    simp [ha] at hb) hV
  have g1 : Measurable fun y : ({0} : Set ℕ) → F => y ⟨0, rfl⟩ := measurable_pi_apply _
  have g2 : Measurable fun (y : {n : ℕ | 1 ≤ n} → F) (n : ℕ) =>
      y ⟨n + 1, by simp⟩ := Measurable.of_eval fun n => measurable_pi_apply _
  exact h.comp g1 g2

omit [IsProbabilityMeasure P] in
/-- The law of an iid sequence is the infinite product of its marginal. -/
theorem map_path_eq_infinitePi (hV : ∀ n, Measurable (V n)) (hiid : iIndepFun V P)
    {ν : Measure F} (hid : ∀ n, P.map (V n) = ν) :
    P.map (fun ω n => V n ω) = Measure.infinitePi (fun _ : ℕ => ν) := by
  rw [hiid.map_fun_eq_infinitePi_map hV]
  congr 1
  funext n
  exact hid n

/-- **Stationarity of a random iteration.** Let `X₀` be independent of the iid innovations
`(V_n)_n` (with law `ν`), and let the law `π` of `X₀` be invariant: `law(f(X₀, V_0)) = π`, i.e.
`(π ⊗ ν).map f = π` (equivalently `K ∘ₘ π = π` for `K = noiseKernel f ν`,
`noiseKernel_comp_eq`). Then the chain `X_{n+1} = f(X_n, V_n)` is stationary. -/
theorem isStationary_chain (hf : Measurable (Function.uncurry f)) (hX₀ : Measurable X₀)
    (hV : ∀ n, Measurable (V n)) (hind : IndepFun X₀ (fun ω n => V n ω) P)
    (hiid : iIndepFun V P) (hid : ∀ n, IdentDistrib (V n) (V 0) P P)
    (hinv : ((P.map X₀).prod (P.map (V 0))).map (Function.uncurry f) = P.map X₀) :
    IsStationary (chain f X₀ V) P := by
  set μ₀ := P.map X₀
  set ν := P.map (V 0)
  set L := Measure.infinitePi (fun _ : ℕ => ν)
  have hVm : Measurable fun ω n => V n ω := Measurable.of_eval hV
  have hVsm : Measurable fun ω n => V (n + 1) ω := Measurable.of_eval fun n => hV (n + 1)
  -- laws of the innovation sequence and of its shift
  have hVlaw : P.map (fun ω n => V n ω) = L :=
    map_path_eq_infinitePi hV hiid fun n => (hid n).map_eq
  have hVslaw : P.map (fun ω n => V (n + 1) ω) = L :=
    map_path_eq_infinitePi (fun n => hV (n + 1)) (hiid.precomp (add_left_injective 1))
      fun n => (hid (n + 1)).map_eq
  -- `V_0` is independent of the shifted sequence
  have h0s : IndepFun (V 0) (fun ω n => V (n + 1) ω) P := indepFun_zero_shift hV hiid
  -- `X₀` is independent of `(V_0, shifted sequence)`
  have hsplit : Measurable fun v : ℕ → F => (v 0, fun n => v (n + 1)) :=
    (measurable_pi_apply 0).prodMk (Measurable.of_eval fun n => measurable_pi_apply _)
  have hX0V : IndepFun X₀ (fun ω => (V 0 ω, fun n => V (n + 1) ω)) P :=
    hind.comp measurable_id hsplit
  -- joint laws
  have hlaw0s : P.map (fun ω => (V 0 ω, fun n => V (n + 1) ω)) = ν.prod L := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hV 0).aemeasurable hVsm.aemeasurable).1 h0s,
      hVslaw]
  have hlaw3 : P.map (fun ω => (X₀ ω, (V 0 ω, fun n => V (n + 1) ω))) = μ₀.prod (ν.prod L) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX₀.aemeasurable
      ((hV 0).prodMk hVsm).aemeasurable).1 hX0V, hlaw0s]
  have hlaw3' : P.map (fun ω => ((X₀ ω, V 0 ω), fun n => V (n + 1) ω)) =
      (μ₀.prod ν).prod L := by
    have e : (fun ω => ((X₀ ω, V 0 ω), fun n => V (n + 1) ω)) =
        MeasurableEquiv.prodAssoc.symm ∘ fun ω => (X₀ ω, (V 0 ω, fun n => V (n + 1) ω)) := rfl
    rw [e, ← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      (hX₀.prodMk ((hV 0).prodMk hVsm)), hlaw3, ← Measure.prodAssoc_prod,
      Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    simp
  -- the law of `(X_1, shifted innovations)` equals the law of `(X_0, innovations)`
  have hlaw1 : P.map (fun ω => (f (X₀ ω) (V 0 ω), fun n => V (n + 1) ω)) = μ₀.prod L := by
    have e : (fun ω => (f (X₀ ω) (V 0 ω), fun n => V (n + 1) ω)) =
        Prod.map (Function.uncurry f) id ∘ fun ω => ((X₀ ω, V 0 ω), fun n => V (n + 1) ω) :=
      rfl
    rw [e, ← Measure.map_map (hf.prodMap measurable_id) ((hX₀.prodMk (hV 0)).prodMk hVsm),
      hlaw3', ← Measure.map_prod_map _ _ hf measurable_id, hinv, Measure.map_id]
  have hlaw0 : P.map (fun ω => (X₀ ω, fun n => V n ω)) = μ₀.prod L := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX₀.aemeasurable hVm.aemeasurable).1 hind, hVlaw]
  -- conclusion
  have hΦ := measurable_iter_path hf
  have e1 : (fun ω n => chain f X₀ V (n + 1) ω) = (fun p : E × (ℕ → F) => fun n => iter f p.1 p.2 n) ∘
      fun ω => (f (X₀ ω) (V 0 ω), fun n => V (n + 1) ω) := by
    funext ω n; simp only [chain, Function.comp_apply, iter_succ']
  have e0 : (fun ω n => chain f X₀ V n ω) = (fun p : E × (ℕ → F) => fun n => iter f p.1 p.2 n) ∘
      fun ω => (X₀ ω, fun n => V n ω) := rfl
  unfold IsStationary
  have hm1 : Measurable fun ω => (f (X₀ ω) (V 0 ω), fun n => V (n + 1) ω) :=
    (hf.comp (hX₀.prodMk (hV 0))).prodMk hVsm
  rw [e1, e0, ← Measure.map_map hΦ hm1,
    ← Measure.map_map hΦ (hX₀.prodMk hVm), hlaw1, hlaw0]

end Stationary

/-! ### The canonical construction -/

section Canonical

variable (π : Measure E) [IsProbabilityMeasure π] (ν : Measure F) [IsProbabilityMeasure ν]

/-- The canonical probability space of a random iteration: `E × (ℕ → F)` with the product of the
initial law `π` and the infinite product `ν^⊗ℕ` of the innovation law. -/
noncomputable def canonicalMeasure : Measure (E × (ℕ → F)) :=
  π.prod (Measure.infinitePi fun _ : ℕ => ν)

instance : IsProbabilityMeasure (canonicalMeasure π ν) := by
  unfold canonicalMeasure; infer_instance

omit [IsProbabilityMeasure π] in
theorem map_fst_canonicalMeasure : (canonicalMeasure π ν).map Prod.fst = π := by
  simp [canonicalMeasure]

theorem map_snd_canonicalMeasure :
    (canonicalMeasure π ν).map Prod.snd = Measure.infinitePi fun _ : ℕ => ν := by
  simp [canonicalMeasure]

theorem map_coord_canonicalMeasure (n : ℕ) :
    (canonicalMeasure π ν).map (fun p : E × (ℕ → F) => p.2 n) = ν := by
  have e : (fun p : E × (ℕ → F) => p.2 n) = (fun v : ℕ → F => v n) ∘ Prod.snd := rfl
  rw [e, ← Measure.map_map (measurable_pi_apply n) measurable_snd, map_snd_canonicalMeasure,
    Measure.infinitePi_map_eval]

theorem indepFun_canonical :
    IndepFun (Prod.fst : E × (ℕ → F) → E) (fun p n => p.2 n) (canonicalMeasure π ν) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable]
  simp [canonicalMeasure]

theorem iIndepFun_canonical :
    iIndepFun (fun n (p : E × (ℕ → F)) => p.2 n) (canonicalMeasure π ν) := by
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map (fun n => (measurable_pi_apply n).comp
    (measurable_snd (α := E) (β := ℕ → F)))).2 ?_
  have e : (fun (p : E × (ℕ → F)) (n : ℕ) => ((fun v : ℕ → F => v n) ∘ Prod.snd) p) =
    Prod.snd := rfl
  rw [e, map_snd_canonicalMeasure]
  congr 1
  funext n
  exact (map_coord_canonicalMeasure π ν n).symm

/-- **Existence of the stationary Markov chain.** On the canonical space
`(E × (ℕ → F), π ⊗ ν^⊗ℕ)`, the random iteration started from the first coordinate and driven by
the coordinates of the second is a stationary Markov chain with marginal `π`, whenever `π` is
invariant: `(π ⊗ ν).map f = π`. -/
theorem isStationary_canonicalChain (hf : Measurable (Function.uncurry f))
    (hinv : (π.prod ν).map (Function.uncurry f) = π) :
    IsStationary (chain f Prod.fst fun n (p : E × (ℕ → F)) => p.2 n) (canonicalMeasure π ν) := by
  refine isStationary_chain hf measurable_fst (fun n => (measurable_pi_apply n).comp
    measurable_snd) (indepFun_canonical π ν) (iIndepFun_canonical π ν) (fun n => ?_) ?_
  · exact ⟨((measurable_pi_apply n).comp measurable_snd).aemeasurable,
      ((measurable_pi_apply 0).comp measurable_snd).aemeasurable,
      by rw [map_coord_canonicalMeasure, map_coord_canonicalMeasure]⟩
  · rw [map_fst_canonicalMeasure, map_coord_canonicalMeasure, hinv]

end Canonical

end RandomIteration

end ExtremeValueTheory
