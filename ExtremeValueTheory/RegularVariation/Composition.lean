/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.RegularVariation.UniformConvergenceTails
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Composition of regularly varying functions, and why the limit is a power

These two facts of the basic theory rest on measurability, through the uniform convergence theorem
or through the measurable solutions of the Cauchy functional equation. So they are not in
`RegularVariation/Basic.lean`, which assumes none.

## Main results

* `IsRegularlyVarying.comp`: if `f ∈ RV_ρ`, `g ∈ RV_η` and `g → ∞`, then `f ∘ g ∈ RV_{ρ η}`.
* `exists_isRegularlyVarying_of_tendsto`: if `f (c x) / f x` converges to a positive limit `k c` for
  every `c > 0`, then `k c = c ^ ρ` for some `ρ`, and `f` is regularly varying with index `ρ`.

## References

N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation*, Cambridge University Press (1987)
[BGT], §1.4 and §1.5.
-/

open Filter Topology Set Real MeasureTheory

namespace ExtremeValueTheory

variable {f g : ℝ → ℝ} {ρ η : ℝ}

/-- **Composition of regularly varying functions** ([BGT, §1.5]): if `f` is measurable near `∞` and
regularly varying with index `ρ`, `g` is regularly varying with index `η` and `g x → ∞`, then
`f ∘ g` is regularly varying with index `ρ * η`. Nothing but the limit is asked of `g`: the uniform
convergence theorem is used for `f` only. -/
theorem IsRegularlyVarying.comp (hf : IsRegularlyVarying f ρ) (hm : MeasurableNearTop f)
    (hg : IsRegularlyVarying g η) (hgtop : Tendsto g atTop atTop) :
    IsRegularlyVarying (fun x => f (g x)) (ρ * η) := by
  refine ⟨hgtop.eventually hf.1, fun c hc => ?_⟩
  have hl : 0 < c ^ η := rpow_pos_of_pos hc η
  have hlim : (c ^ η) ^ ρ = c ^ (ρ * η) := by rw [← rpow_mul hc.le, mul_comm]
  rw [← hlim, Metric.tendsto_nhds]
  intro ε hε
  have hK : Icc (c ^ η / 2) (2 * c ^ η) ⊆ Ioi 0 := fun _ hk => (half_pos hl).trans_le hk.1
  have hU := Metric.tendstoUniformlyOn_iff.1 (hf.tendstoUniformlyOn_of_measurableNearTop hm
    isCompact_Icc hK) (ε / 2) (half_pos hε)
  have hr := hg.2 c hc
  have hmem : ∀ᶠ x in atTop, g (c * x) / g x ∈ Icc (c ^ η / 2) (2 * c ^ η) :=
    hr.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have hcont : ContinuousAt (fun k : ℝ => k ^ ρ) (c ^ η) :=
    continuousAt_rpow_const _ _ (Or.inl hl.ne')
  have hclose := Metric.tendsto_nhds.1 (hcont.tendsto.comp hr) (ε / 2) (half_pos hε)
  filter_upwards [hgtop.eventually hU, hmem, hclose, hg.1] with x h1 h2 h3 hgx
  have hgcx : (g (c * x) / g x) * g x = g (c * x) := div_mul_cancel₀ _ hgx.ne'
  have h4 := h1 _ h2
  rw [hgcx] at h4
  have h5 : dist ((g (c * x) / g x) ^ ρ) ((c ^ η) ^ ρ) < ε / 2 := h3
  calc dist (f (g (c * x)) / f (g x)) ((c ^ η) ^ ρ)
      ≤ dist (f (g (c * x)) / f (g x)) ((g (c * x) / g x) ^ ρ) +
        dist ((g (c * x) / g x) ^ ρ) ((c ^ η) ^ ρ) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by rwa [dist_comm]) h5
    _ = ε := add_halves ε

/-- **The limit is a power** ([BGT, Theorem 1.4.1], as we recall it; the book was not available to
check the numbering): if `f` is eventually positive and measurable near `∞`, and
`f (c x) / f x → k c` with `k c > 0` for every `c > 0`, then there is `ρ` with `k c = c ^ ρ` for every
`c > 0`, so `f` is regularly varying with index `ρ`.

The limit `k` satisfies the multiplicative Cauchy equation, and it is measurable as a limit of
measurable functions. -/
theorem exists_isRegularlyVarying_of_tendsto {k : ℝ → ℝ} (hpos : ∀ᶠ x in atTop, 0 < f x)
    (hm : MeasurableNearTop f) (hk : ∀ c, 0 < c → 0 < k c)
    (h : ∀ c, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (k c))) :
    ∃ ρ : ℝ, IsRegularlyVarying f ρ ∧ ∀ c, 0 < c → k c = c ^ ρ := by
  -- the multiplicative Cauchy equation
  have hmul : ∀ c d, 0 < c → 0 < d → k (c * d) = k c * k d := by
    intro c d hc hd
    have hd' : Tendsto (fun x => d * x) atTop atTop := tendsto_id.const_mul_atTop hd
    have h1 := ((h c hc).comp hd').mul (h d hd)
    refine tendsto_nhds_unique (h (c * d) (mul_pos hc hd)) (h1.congr' ?_)
    filter_upwards [hd'.eventually hpos] with x hx
    simp only [Function.comp_apply] at hx ⊢
    rw [div_mul_div_cancel₀ hx.ne', mul_assoc]
  -- the additive form
  let A : ℝ →+ ℝ :=
    { toFun := fun t => log (k (exp t))
      map_zero' := by
        have h1 := hmul 1 1 one_pos one_pos
        rw [one_mul] at h1
        have h2 : k 1 = 1 := by
          have := hk 1 one_pos
          nlinarith
        simp [h2]
      map_add' := fun s t => by
        rw [exp_add, hmul _ _ (exp_pos s) (exp_pos t),
          log_mul (hk _ (exp_pos s)).ne' (hk _ (exp_pos t)).ne'] }
  have hA : ∀ t, A t = log (k (exp t)) := fun _ => rfl
  -- measurability, as a limit along the integers
  obtain ⟨X, hX⟩ := hm
  have hAm : Measurable A := by
    have hlim : Tendsto (fun (n : ℕ) (t : ℝ) =>
        log ((Ici X).indicator f (exp t * n) / (Ici X).indicator f n)) atTop (𝓝 fun t => A t) := by
      rw [tendsto_pi_nhds]
      intro t
      have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have h1 := ((h _ (exp_pos t)).comp hn).log (hk _ (exp_pos t)).ne'
      refine h1.congr' ?_
      filter_upwards [hn.eventually (eventually_ge_atTop X),
        (tendsto_id.const_mul_atTop (exp_pos t)).comp hn |>.eventually (eventually_ge_atTop X)]
        with n h2 h3
      simp only [Function.comp_apply, id] at h3 ⊢
      rw [indicator_of_mem (mem_Ici.2 h2), indicator_of_mem (mem_Ici.2 h3)]
    refine measurable_of_tendsto_metrizable (fun n => ?_) hlim
    exact (((hX.comp (measurable_exp.mul_const _)).div_const _)).log
  have hAc : Continuous A := Measure.AddMonoidHom.continuous_of_measurable A hAm
  have hlin : ∀ t, A t = t * A 1 := fun t => by
    have := map_real_smul A hAc t (1 : ℝ)
    simpa using this
  have hpow : ∀ c, 0 < c → k c = c ^ (A 1) := by
    intro c hc
    have h1 := hlin (log c)
    rw [hA, exp_log hc] at h1
    rw [rpow_def_of_pos hc, ← h1, exp_log (hk c hc)]
  refine ⟨A 1, ⟨hpos, fun c hc => ?_⟩, hpow⟩
  rw [← hpow c hc]
  exact h c hc

end ExtremeValueTheory
