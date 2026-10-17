/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
Modified by Federico Carrone, 2026, from kkytola/ExtremeValueProject (commit f7c9a8ce260d):
ported to Lean/Mathlib v4.35.0 and renamed `ExtremeValueProject` to `ExtremeValueTheory`.
-/
import Mathlib

namespace ExtremeValueTheory

section classification_calculation

open Real Set

#check Differentiable
#check deriv

#check ContDiff

/-- Lemma 3.1 (ode-of-order-two-for-Q) -/
lemma ode_of_order_two_for_Q
    {Q α : ℝ → ℝ} (Q_diffble : Differentiable ℝ Q) (hQ0 : Q 0 = 0)
    (hDQ0 : deriv Q 0 = 1) (Q_eqn : ∀ h s, Q (h + s) = Q h * α s + Q s) :
    ContDiff ℝ 2 Q ∧ (∀ s, deriv (deriv Q) s = (deriv Q s) * (deriv (deriv Q) 0)) := by
  -- Step 1: `α = Q'`.
  have hα : ∀ s, α s = deriv Q s := by
    intro s
    have h1 : HasDerivAt (fun h ↦ Q (h + s)) (deriv Q (0 + s)) 0 :=
      (Q_diffble (0 + s)).hasDerivAt.comp_add_const 0 s
    have h2 : HasDerivAt (fun h ↦ Q h * α s + Q s) (deriv Q 0 * α s) 0 :=
      ((Q_diffble 0).hasDerivAt.mul_const (α s)).add_const (Q s)
    have h1' : HasDerivAt (fun h ↦ Q h * α s + Q s) (deriv Q (0 + s)) 0 := by
      convert h1 using 1
      funext h
      exact (Q_eqn h s).symm
    have := h2.unique h1'
    rw [hDQ0, one_mul, zero_add] at this
    exact this
  -- Step 2: some value of `Q` is nonzero.
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, Q s₀ ≠ 0 := by
    by_contra! hcon
    have : Q = fun _ ↦ 0 := funext hcon
    rw [this, deriv_const] at hDQ0
    exact zero_ne_one hDQ0
  -- Step 3: `Q' = 1 + k Q`.
  set k := (deriv Q s₀ - 1) / Q s₀ with hk
  have hDQ : deriv Q = fun h ↦ 1 + k * Q h := by
    funext h
    have e1 := Q_eqn h s₀
    have e2 := Q_eqn s₀ h
    rw [hα, add_comm] at e1
    rw [hα] at e2
    rw [hk]
    field_simp
    linarith
  have hDQ_diff : Differentiable ℝ (deriv Q) := by
    rw [hDQ]; exact (Q_diffble.const_mul k).const_add 1
  have hDDQ : ∀ s, deriv (deriv Q) s = k * deriv Q s := by
    intro s
    rw [hDQ]
    simp only [deriv_const_add', deriv_const_mul_field']
    rw [hDQ]
  have hDDQ0 : deriv (deriv Q) 0 = k := by rw [hDDQ, hDQ0, mul_one]
  refine ⟨?_, fun s ↦ by rw [hDDQ, hDDQ0, mul_comm]⟩
  have hC1 : ContDiff ℝ 1 Q := contDiff_one_iff_deriv.2 ⟨Q_diffble, hDQ_diff.continuous⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨Q_diffble, by simp, ?_⟩
  rw [hDQ]
  exact contDiff_const.add (contDiff_const.mul hC1)

/-- A version of `solve_Q` with `γ = Q''(0)` and without needing positivity of `Q'`. -/
lemma solve_Q_of_gamma_eq
    {Q : ℝ → ℝ} {γ : ℝ} (Q_diffble2 : ContDiff ℝ 2 Q) (hQ0 : Q 0 = 0) (hDQ0 : deriv Q 0 = 1)
    (hγ : γ = deriv (deriv Q) 0)
    (Q_de : ∀ s, deriv (deriv Q) s = (deriv Q s) * (deriv (deriv Q) 0)) :
    Q = if γ = 0 then (fun s ↦ s) else (fun s ↦ (exp (γ * s) - 1) / γ) := by
  rw [← hγ] at Q_de
  obtain ⟨hQd, -, hDQ⟩ :=
    contDiff_succ_iff_deriv.1 (show ContDiff ℝ (1 + 1) Q from Q_diffble2)
  have hDQd : Differentiable ℝ (deriv Q) := hDQ.differentiable (by norm_num)
  have hexp : ∀ s, deriv Q s = exp (γ * s) := by
    let g := fun s ↦ deriv Q s * exp (-(γ * s))
    have hg : ∀ s, HasDerivAt g 0 s := by
      intro s
      have h1 := (hDQd s).hasDerivAt
      have h2 : HasDerivAt (fun s ↦ exp (-(γ * s))) (exp (-(γ * s)) * (-(γ * 1))) s :=
        ((hasDerivAt_id s).const_mul γ).neg.exp
      convert h1.mul h2 using 1
      rw [Q_de]; ring
    have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hg s).differentiableAt)
      (fun s ↦ (hg s).deriv)
    intro s
    have h := hconst s 0
    simp only [g, hDQ0, mul_zero, neg_zero, exp_zero, mul_one] at h
    rw [Real.exp_neg] at h
    have := exp_pos (γ * s)
    field_simp at h
    exact h
  set T : ℝ → ℝ := if γ = 0 then (fun s ↦ s) else (fun s ↦ (exp (γ * s) - 1) / γ) with hT
  have hT0 : T 0 = 0 := by rw [hT]; split_ifs <;> simp
  have hTd : ∀ s, HasDerivAt T (deriv Q s) s := by
    intro s
    rw [hexp, hT]
    split_ifs with h0
    · simpa [h0] using hasDerivAt_id' s
    · have := ((((hasDerivAt_id' s).const_mul γ).exp).sub_const 1).div_const γ
      convert this using 1
      field_simp
  have hdiff : Differentiable ℝ (Q - T) :=
    fun s ↦ (hQd s).sub (hTd s).differentiableAt
  have hzero : ∀ s, deriv (Q - T) s = 0 := fun s ↦
    by simpa using ((hQd s).hasDerivAt.sub (hTd s)).deriv
  funext s
  have := is_const_of_deriv_eq_zero hdiff hzero s 0
  simp only [Pi.sub_apply, hQ0, hT0, sub_zero] at this
  linarith

/-- Lemma 3.2 (solve-Q) -/
-- Corrected from upstream: added the hypothesis `hγ : γ = deriv (deriv Q) 0` (upstream `γ` was
-- unconstrained, making the statement false, see `not_solve_Q` below).
lemma solve_Q
    {Q : ℝ → ℝ} {γ : ℝ} (Q_diffble2 : ContDiff ℝ 2 Q) (hQ0 : Q 0 = 0) (hDQ0 : deriv Q 0 = 1)
    (hγ : γ = deriv (deriv Q) 0) (_hDQ_pos : ∀ s, 0 < deriv Q s)
    (Q_de : ∀ s, deriv (deriv Q) s = (deriv Q s) * (deriv (deriv Q) 0)) :
    Q = if γ = 0 then (fun s ↦ s) else (fun s ↦ (exp (γ * s) - 1) / γ) :=
  solve_Q_of_gamma_eq Q_diffble2 hQ0 hDQ0 hγ Q_de

/-- Lemma 3.4 (solve-E) -/
-- Corrected from upstream: upstream had `γ = H''(0)` with `H = E ∘ exp`, the conclusion
-- `E = if γ = 0 then c * log else c * (rpow · γ - 1)` as functions on all of `ℝ`, and `hc` as an
-- (unusable) implicit binder; see `not_solve_E` below. Now `γ = H''(0) / c` (as in the
-- blueprint), the formula is `c * (σ ^ γ - 1) / γ`, and it is asserted only for `σ > 0`.
lemma solve_E
    {E A : ℝ → ℝ} {c γ : ℝ} (hc : c = deriv E 1)
    (hγ : γ = deriv (deriv (fun s ↦ E (exp s))) 0 / c)
    (A_pos : ∀ τ > 0, 0 < A τ) (E_mono : MonotoneOn E (Ioi 0))
    (E_noncst : ¬ ∃ C, ∀ σ > 0, E σ = C) (hE1 : E 1 = 0)
    (E_eqn : ∀ σ > 0, ∀ τ > 0, E (σ * τ) = E σ * A τ + E τ) :
    ∀ σ > 0, E σ = if γ = 0 then c * log σ else c * (σ ^ γ - 1) / γ := by
  set H : ℝ → ℝ := fun s ↦ E (exp s) with hH
  set α : ℝ → ℝ := fun s ↦ A (exp s) with hα
  have α_pos : ∀ s, 0 < α s := fun s ↦ A_pos _ (exp_pos s)
  have H_mono : Monotone H := fun a b hab ↦
    E_mono (exp_pos a) (exp_pos b) (exp_le_exp.2 hab)
  have H_eqn : ∀ h s, H (h + s) = H h * α s + H s := fun h s ↦ by
    simp only [hH, hα, exp_add]; exact E_eqn _ (exp_pos h) _ (exp_pos s)
  have H0 : H 0 = 0 := by simp [hH, hE1]
  have E_eq : ∀ σ > 0, E σ = H (log σ) := fun σ hσ ↦ by simp [hH, exp_log hσ]
  -- `H` is differentiable at some point, hence at `0`, hence everywhere.
  obtain ⟨s₀, hs₀⟩ := H_mono.ae_differentiableAt.exists
  have hd0 : DifferentiableAt ℝ H 0 := by
    have e : H = fun h ↦ (H (h + s₀) - H s₀) / α s₀ := by
      funext h; rw [H_eqn]; field_simp [(α_pos s₀).ne']; ring
    rw [e]
    have : DifferentiableAt ℝ (fun h ↦ H (h + s₀)) 0 :=
      ((zero_add s₀).symm ▸ hs₀).hasDerivAt.comp_add_const 0 s₀ |>.differentiableAt
    exact (this.sub_const _).div_const _
  have hDH : ∀ s, HasDerivAt H (deriv H 0 * α s) s := fun s ↦ by
    have h0' : HasDerivAt H (deriv H 0) (s - s) := by rw [sub_self]; exact hd0.hasDerivAt
    refine ((h0'.comp_sub_const s s).mul_const (α s) |>.add_const (H s)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only
    rw [← H_eqn, sub_add_cancel]
  have H_diff : Differentiable ℝ H := fun s ↦ (hDH s).differentiableAt
  -- `c = H'(0)`.
  have hc' : c = deriv H 0 := by
    rw [hc]
    have h1 : HasDerivAt (fun σ ↦ H (log σ)) (deriv H 0 * 1⁻¹) 1 := by
      have := (H_diff (log 1)).hasDerivAt.comp 1 (Real.hasDerivAt_log one_ne_zero)
      rw [log_one] at this
      exact this
    have h2 : HasDerivAt E (deriv H 0 * 1⁻¹) 1 := by
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds one_pos] with σ hσ
      exact E_eq σ hσ
    simpa using h2.deriv
  have c_ne : c ≠ 0 := by
    intro hc0
    apply E_noncst
    refine ⟨0, fun σ hσ ↦ ?_⟩
    have hz : ∀ s, deriv H s = 0 := fun s ↦ by rw [(hDH s).deriv, ← hc', hc0, zero_mul]
    rw [E_eq σ hσ, is_const_of_deriv_eq_zero H_diff hz (log σ) 0, H0]
  -- Normalize: `Q = H / c`.
  set Q : ℝ → ℝ := fun s ↦ H s / c with hQ
  have Q_diff : Differentiable ℝ Q := H_diff.div_const c
  have hQ0 : Q 0 = 0 := by simp [hQ, H0]
  have hDQ : deriv Q = fun s ↦ deriv H s / c := funext fun s ↦ deriv_div_const c
  have hDQ0 : deriv Q 0 = 1 := by rw [hDQ]; show deriv H 0 / c = 1; rw [← hc', div_self c_ne]
  have Q_eqn : ∀ h s, Q (h + s) = Q h * α s + Q s := fun h s ↦ by
    simp only [hQ, H_eqn]; field_simp
  obtain ⟨hQ2, Q_de⟩ := ode_of_order_two_for_Q Q_diff hQ0 hDQ0 Q_eqn
  have hγQ : γ = deriv (deriv Q) 0 := by
    rw [hγ, hDQ, deriv_div_const]
  have hQsol := solve_Q_of_gamma_eq hQ2 hQ0 hDQ0 hγQ Q_de
  intro σ hσ
  have hHQ : H (log σ) = c * Q (log σ) := by simp only [hQ]; field_simp
  rw [E_eq σ hσ, hHQ, hQsol]
  split_ifs with hγ0
  · rfl
  · rw [rpow_def_of_pos hσ, mul_comm (log σ)]; ring

/-! ### Counterexamples to `solve_Q` and `solve_E` as stated upstream

* In `solve_Q` the parameter `γ` is a free (implicit) variable not tied to `Q`
  (presumably `γ = deriv (deriv Q) 0` was intended), so the statement fails e.g. for
  `Q = id`, `γ = 1`.
* In `solve_E` the normalization is wrong (the correct formula would be
  `E σ = c * (σ ^ (γ / c) - 1) / (γ / c)` with `γ = H''(0)`, `H = E ∘ exp`), and moreover the
  conclusion is an equality of functions on all of `ℝ` although the hypotheses only constrain
  `E` on `(0, ∞)`. A counterexample is `E σ = 2 * (σ - 1)`, `A τ = τ`, `c = 2`, `γ = 2`. -/

lemma not_solve_Q :
    ¬ ∀ (Q : ℝ → ℝ) (γ : ℝ), ContDiff ℝ 2 Q → Q 0 = 0 → deriv Q 0 = 1 →
      (∀ s, 0 < deriv Q s) → (∀ s, deriv (deriv Q) s = (deriv Q s) * (deriv (deriv Q) 0)) →
      Q = if γ = 0 then (fun s ↦ s) else (fun s ↦ (exp (γ * s) - 1) / γ) := by
  intro h
  have := h (fun s ↦ s) 1 contDiff_id rfl (by simp) (by simp) (by simp)
  have h1 := congrFun this 1
  simp only [one_ne_zero, ↓reduceIte, one_mul, div_one] at h1
  have := Real.exp_one_gt_d9
  linarith

lemma not_solve_E :
    ¬ ∀ (E A : ℝ → ℝ) (c γ : ℝ), c = deriv E 1 →
      γ = deriv (deriv (fun s ↦ E (exp s))) 0 → (∀ τ > 0, 0 < A τ) → MonotoneOn E (Ioi 0) →
      (¬ ∃ C, ∀ σ > 0, E σ = C) → E 1 = 0 →
      (∀ σ > 0, ∀ τ > 0, E (σ * τ) = E σ * A τ + E τ) →
      E = if γ = 0 then (fun σ ↦ c * log σ) else (fun σ ↦ c * (σ.rpow γ - 1)) := by
  intro h
  have hc : (2 : ℝ) = deriv (fun σ : ℝ ↦ 2 * (σ - 1)) 1 := by
    simp only [deriv_const_mul_field', deriv_sub_const, deriv_id'']; norm_num
  have hH : deriv (fun s ↦ 2 * (exp s - 1)) = fun s ↦ 2 * exp s := by
    funext s
    simp only [deriv_const_mul_field', deriv_sub_const, Real.deriv_exp]
  have hγ : (2 : ℝ) = deriv (deriv (fun s ↦ 2 * (exp s - 1))) 0 := by
    rw [hH]; simp only [deriv_const_mul_field', Real.deriv_exp, exp_zero]; norm_num
  have := h (fun σ ↦ 2 * (σ - 1)) (fun τ ↦ τ) 2 2 hc hγ (fun τ hτ ↦ hτ)
    (fun x _ y _ hxy ↦ by simp only; linarith)
    (by rintro ⟨C, hC⟩; have h1 := hC 1 one_pos; have h2 := hC 2 two_pos; linarith)
    (by norm_num) (fun σ _ τ _ ↦ by ring)
  have h2 := congrFun this 2
  simp only [two_ne_zero, ↓reduceIte, Real.rpow_eq_pow, Real.rpow_two] at h2
  norm_num at h2

end classification_calculation

end ExtremeValueTheory
