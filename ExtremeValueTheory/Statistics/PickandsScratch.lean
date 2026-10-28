import ExtremeValueTheory.Statistics.PickandsNormality

open Filter Topology Set Real MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix

namespace ExtremeValueTheory

/-! ### The second-order remainder of the Pickands statistic -/

section Remainder

/-- `|log (1 + z) - z| ≤ 2 z²` for `|z| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |Real.log (1 + z) - z| ≤ 2 * z ^ 2 := by
  rw [abs_le] at hz
  have h1 : 0 < 1 + z := by linarith
  have hu := Real.log_le_sub_one_of_pos h1
  have hl := Real.one_sub_inv_le_log_of_pos h1
  have e : 1 - (1 + z)⁻¹ = z - z ^ 2 / (1 + z) := by field_simp; ring
  have hq : z ^ 2 / (1 + z) ≤ 2 * z ^ 2 := by
    rw [div_le_iff₀ h1]; nlinarith [sq_nonneg z]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg z]

/-- `log (1 + A u) / A → u₀` as `A → 0` with `A ≠ 0`, and `u → u₀`. -/
theorem tendsto_log_one_add_mul_div {α : Type*} {l : Filter α} {A u : α → ℝ} {u₀ : ℝ}
    (hA : Tendsto A l (𝓝 0)) (hA0 : ∀ᶠ p in l, A p ≠ 0) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun p => Real.log (1 + A p * u p) / A p) l (𝓝 u₀) := by
  have hAu : Tendsto (fun p => |A p * u p|) l (𝓝 0) := by
    have := (hA.mul hu).abs
    simpa using this
  have hr : Tendsto (fun p => 2 * |A p| * u p ^ 2) l (𝓝 0) := by
    have := (hA.abs.const_mul 2).mul (hu.pow 2)
    simpa using this
  have hd : Tendsto (fun p => Real.log (1 + A p * u p) / A p - u p) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hr
    filter_upwards [hA0, hAu.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with p hp hsmall
    have hpos : 0 < |A p| := abs_pos.2 hp
    have e : Real.log (1 + A p * u p) / A p - u p =
        (Real.log (1 + A p * u p) - A p * u p) / A p := by field_simp
    rw [Real.norm_eq_abs, e, abs_div, div_le_iff₀ hpos]
    calc |Real.log (1 + A p * u p) - A p * u p| ≤ 2 * (A p * u p) ^ 2 :=
          abs_log_one_add_sub_le hsmall
      _ = 2 * |A p| * u p ^ 2 * |A p| := by rw [mul_pow, ← sq_abs (A p)]; ring
  simpa using hd.add hu

/-- Locally uniform convergence along a reparametrized filter, evaluated at a moving point. -/
theorem tendsto_comp_of_tendstoLocallyUniformlyOn {β : Type*} {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ}
    {s : Set ℝ} (h : TendstoLocallyUniformlyOn F f atTop s) {l : Filter β} {φ g : β → ℝ}
    (hφ : Tendsto φ l atTop) {x : ℝ} (hx : x ∈ s) (hf : ContinuousWithinAt f s x)
    (hg : Tendsto g l (𝓝[s] x)) : Tendsto (fun b => F (φ b) (g b)) l (𝓝 (f x)) := by
  have h' : TendstoLocallyUniformlyOn (fun b => F (φ b)) f l s := fun u hu y hy => by
    obtain ⟨t, ht, hev⟩ := h u hu y hy
    exact ⟨t, ht, hφ.eventually hev⟩
  exact h'.tendsto_comp hf hx hg

theorem strictMonoOn_extRVLimit (γ : ℝ) : StrictMonoOn (extRVLimit γ) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun x hx => (hasDerivAt_extRVLimit γ hx).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_extRVLimit γ hx).deriv]
  exact rpow_pos_of_pos hx _

/-- The log-ratio of spacings of `U` at the points `x_i t`, `x_i = 1/(-y_i)`:
`log ((U(x₀t) - U(x₁t)) / (U(x₁t) - U(x₂t)))`. With `t = n/k` and `y_i = -(n/k)(1 - U_{(τ_i k+1)})`
this is `log 2 ×` the Pickands estimator of the sample `U(1/(1 - U_i))`. -/
noncomputable def pickandsLog (U : ℝ → ℝ) (t : ℝ) (y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.log ((U ((-y 0)⁻¹ * t) - U ((-y 1)⁻¹ * t)) / (U ((-y 1)⁻¹ * t) - U ((-y 2)⁻¹ * t)))

/-- The asymptotic bias factor of the Pickands estimator ([dHF, Theorem 3.3.5]):
`b = (log 2)⁻¹ ((H(1) - H(1/2)) / (D(1) - D(1/2)) - (H(1/2) - H(1/4)) / (D(1/2) - D(1/4)))`,
with `D = D_γ` and `H = H_{γ,ρ}`. -/
noncomputable def pickandsBias (γ ρ : ℝ) : ℝ :=
  ((extSecondOrderLimit γ ρ 1 - extSecondOrderLimit γ ρ (1 / 2)) /
      (extRVLimit γ 1 - extRVLimit γ (1 / 2)) -
    (extSecondOrderLimit γ ρ (1 / 2) - extSecondOrderLimit γ ρ (1 / 4)) /
      (extRVLimit γ (1 / 2) - extRVLimit γ (1 / 4))) / Real.log 2

/-- **The second-order remainder of the Pickands statistic.** Under second-order extended regular
variation, `(pickandsLog U t y - pickandsMap γ y) / A(t) → b log 2` as `t → ∞` and `y` tends to
the centering point `(-1, -2, -4)`. -/
theorem tendsto_pickandsLog_sub_div {U : ℝ → ℝ} {γ ρ : ℝ} {a A : ℝ → ℝ}
    (h2 : IsExtSecondOrderRegularlyVarying U γ ρ a A) :
    Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
      (pickandsLog U p.1 p.2 - pickandsMap γ p.2) / A p.1)
      (atTop ×ˢ 𝓝 pickandsCenter) (𝓝 (pickandsBias γ ρ * Real.log 2)) := by
  set l : Filter (ℝ × EuclideanSpace ℝ (Fin 3)) := atTop ×ˢ 𝓝 pickandsCenter with hl
  set D := extRVLimit γ with hD
  set H := extSecondOrderLimit γ ρ with hH
  set F : ℝ → ℝ → ℝ := fun t x => ((U (x * t) - U t) / a t - D x) / A t with hF
  have hfst : Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => p.1) l atTop := tendsto_fst
  have hsnd : Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => p.2) l (𝓝 pickandsCenter) :=
    tendsto_snd
  have hτ : ∀ i, (0 : ℝ) < pickandsTimes i := by intro i; fin_cases i <;> simp [pickandsTimes]
  have hxlim : ∀ i, Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => (-p.2 i)⁻¹) l
      (𝓝 ((pickandsTimes i : ℝ)⁻¹)) := by
    intro i
    have hc : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y i := by fun_prop
    have h1 := (hc.tendsto _).comp hsnd
    have := h1.neg.inv₀ (by simp [pickandsCenter, (hτ i).ne'])
    simpa [pickandsCenter] using this
  have hxpos : ∀ i, ∀ᶠ p in l, 0 < (-p.2 i)⁻¹ := fun i =>
    (hxlim i).eventually (lt_mem_nhds (inv_pos.2 (hτ i)))
  have hFl : ∀ i, Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => F p.1 (-p.2 i)⁻¹) l
      (𝓝 (H (pickandsTimes i : ℝ)⁻¹)) := fun i =>
    tendsto_comp_of_tendstoLocallyUniformlyOn h2.tendstoLocallyUniformlyOn hfst
      (inv_pos.2 (hτ i))
      (continuousAt_extSecondOrderLimit γ ρ (inv_pos.2 (hτ i))).continuousWithinAt
      (tendsto_nhdsWithin_iff.2 ⟨hxlim i, hxpos i⟩)
  have hDl : ∀ i, Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => D (-p.2 i)⁻¹) l
      (𝓝 (D (pickandsTimes i : ℝ)⁻¹)) := fun i =>
    (hasDerivAt_extRVLimit γ (inv_pos.2 (hτ i))).continuousAt.tendsto.comp (hxlim i)
  have hmono := strictMonoOn_extRVLimit γ
  have hd01 : 0 < D (pickandsTimes 0 : ℝ)⁻¹ - D (pickandsTimes 1 : ℝ)⁻¹ := by
    have := hmono (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 by norm_num)
      (by norm_num)
    simp only [pickandsTimes]; norm_num; linarith
  have hd12 : 0 < D (pickandsTimes 1 : ℝ)⁻¹ - D (pickandsTimes 2 : ℝ)⁻¹ := by
    have := hmono (show (0 : ℝ) < 1 / 4 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
      (by norm_num)
    simp only [pickandsTimes]; norm_num; linarith
  set u : ℝ × EuclideanSpace ℝ (Fin 3) → ℝ := fun p =>
    (F p.1 (-p.2 0)⁻¹ - F p.1 (-p.2 1)⁻¹) / (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) with hu
  set u' : ℝ × EuclideanSpace ℝ (Fin 3) → ℝ := fun p =>
    (F p.1 (-p.2 1)⁻¹ - F p.1 (-p.2 2)⁻¹) / (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) with hu'
  have hul : Tendsto u l (𝓝 ((H (pickandsTimes 0 : ℝ)⁻¹ - H (pickandsTimes 1 : ℝ)⁻¹) /
      (D (pickandsTimes 0 : ℝ)⁻¹ - D (pickandsTimes 1 : ℝ)⁻¹))) :=
    ((hFl 0).sub (hFl 1)).div ((hDl 0).sub (hDl 1)) hd01.ne'
  have hul' : Tendsto u' l (𝓝 ((H (pickandsTimes 1 : ℝ)⁻¹ - H (pickandsTimes 2 : ℝ)⁻¹) /
      (D (pickandsTimes 1 : ℝ)⁻¹ - D (pickandsTimes 2 : ℝ)⁻¹))) :=
    ((hFl 1).sub (hFl 2)).div ((hDl 1).sub (hDl 2)) hd12.ne'
  have hA : Tendsto (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => A p.1) l (𝓝 0) :=
    h2.tendsto_zero.comp hfst
  have hA0 := hfst.eventually h2.eventually_ne_zero
  have ha0 := hfst.eventually h2.eventually_pos
  have hlim := (tendsto_log_one_add_mul_div hA hA0 hul).sub
    (tendsto_log_one_add_mul_div hA hA0 hul')
  have hp01 := ((hDl 0).sub (hDl 1)).eventually (lt_mem_nhds hd01)
  have hp12 := ((hDl 1).sub (hDl 2)).eventually (lt_mem_nhds hd12)
  have h1u : ∀ᶠ p in l, 0 < 1 + A p.1 * u p := by
    have : Tendsto (fun p => 1 + A p.1 * u p) l (𝓝 (1 + 0 * _)) :=
      tendsto_const_nhds.add (hA.mul hul)
    rw [zero_mul, add_zero] at this
    exact this.eventually (lt_mem_nhds one_pos)
  have h1u' : ∀ᶠ p in l, 0 < 1 + A p.1 * u' p := by
    have : Tendsto (fun p => 1 + A p.1 * u' p) l (𝓝 (1 + 0 * _)) :=
      tendsto_const_nhds.add (hA.mul hul')
    rw [zero_mul, add_zero] at this
    exact this.eventually (lt_mem_nhds one_pos)
  have hval : (H (pickandsTimes 0 : ℝ)⁻¹ - H (pickandsTimes 1 : ℝ)⁻¹) /
        (D (pickandsTimes 0 : ℝ)⁻¹ - D (pickandsTimes 1 : ℝ)⁻¹) -
      (H (pickandsTimes 1 : ℝ)⁻¹ - H (pickandsTimes 2 : ℝ)⁻¹) /
        (D (pickandsTimes 1 : ℝ)⁻¹ - D (pickandsTimes 2 : ℝ)⁻¹) =
      pickandsBias γ ρ * Real.log 2 := by
    have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    simp only [pickandsBias, pickandsTimes, hD, hH]
    norm_num
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [hA0, ha0, hp01, hp12, h1u, h1u', hxpos 0, hxpos 1, hxpos 2]
    with p hA0 ha0 hp01 hp12 h1u h1u' hx0 hx1 hx2
  have hUi : ∀ i, U ((-p.2 i)⁻¹ * p.1) =
      U p.1 + a p.1 * (D (-p.2 i)⁻¹ + A p.1 * F p.1 (-p.2 i)⁻¹) := by
    intro i
    simp only [hF]
    field_simp
    ring
  have eN : U ((-p.2 0)⁻¹ * p.1) - U ((-p.2 1)⁻¹ * p.1) =
      a p.1 * (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) * (1 + A p.1 * u p) := by
    rw [hUi 0, hUi 1]
    simp only [hu]
    have hne := hp01.ne'
    generalize D (-p.2 0)⁻¹ = d0 at hne ⊢
    generalize D (-p.2 1)⁻¹ = d1 at hne ⊢
    rw [sub_ne_zero] at hne
    field_simp
    ring
  have eN' : U ((-p.2 1)⁻¹ * p.1) - U ((-p.2 2)⁻¹ * p.1) =
      a p.1 * (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) * (1 + A p.1 * u' p) := by
    rw [hUi 1, hUi 2]
    simp only [hu']
    have hne := hp12.ne'
    generalize D (-p.2 1)⁻¹ = d0 at hne ⊢
    generalize D (-p.2 2)⁻¹ = d1 at hne ⊢
    rw [sub_ne_zero] at hne
    field_simp
    ring
  have e4 : ∀ i, 0 < (-p.2 i)⁻¹ →
      D (4 / -p.2 i) = D 4 + 4 ^ γ * D (-p.2 i)⁻¹ := by
    intro i hi
    rw [div_eq_mul_inv]
    exact extRVLimit_mul (by norm_num) hi
  have h4 : (0 : ℝ) < 4 ^ γ := by positivity
  have hM : pickandsMap γ p.2 = Real.log (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) -
      Real.log (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) := by
    simp only [pickandsMap]
    rw [← hD, e4 0 hx0, e4 1 hx1, e4 2 hx2]
    rw [show D 4 + 4 ^ γ * D (-p.2 0)⁻¹ - (D 4 + 4 ^ γ * D (-p.2 1)⁻¹) =
      4 ^ γ * (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) by ring,
      show D 4 + 4 ^ γ * D (-p.2 1)⁻¹ - (D 4 + 4 ^ γ * D (-p.2 2)⁻¹) =
      4 ^ γ * (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) by ring,
      Real.log_mul h4.ne' hp01.ne', Real.log_mul h4.ne' hp12.ne']
    ring
  have hL : pickandsLog U p.1 p.2 = Real.log (D (-p.2 0)⁻¹ - D (-p.2 1)⁻¹) +
      Real.log (1 + A p.1 * u p) - (Real.log (D (-p.2 1)⁻¹ - D (-p.2 2)⁻¹) +
      Real.log (1 + A p.1 * u' p)) := by
    simp only [pickandsLog]
    rw [eN, eN', Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) h1u.ne', Real.log_mul (by positivity) h1u'.ne',
      Real.log_mul ha0.ne' hp01.ne', Real.log_mul ha0.ne' hp12.ne']
    ring
  rw [hL, hM]
  field_simp
  ring

end Remainder

/-! ### Convergence in probability through a joint limit -/

section Prob

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- If `G(s, y) → g₀` as `s → l_s` and `y → c`, `t_n → l_s` deterministically and `Y_n → c` in
probability, then `G(t_n, Y_n) → g₀` in probability. -/
theorem TendstoInMeasure.comp_prod_of_tendsto {E β : Type*} [PseudoMetricSpace E]
    {lt : Filter β} {G : β × E → ℝ} {c : E} {g₀ : ℝ} (hG : Tendsto G (lt ×ˢ 𝓝 c) (𝓝 g₀))
    {t : ℕ → β} (ht : Tendsto t atTop lt) {Y : ℕ → Ω → E}
    (hY : TendstoInMeasure P Y atTop (fun _ => c)) :
    TendstoInMeasure P (fun n ω => G (t n, Y n ω)) atTop (fun _ => g₀) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  obtain ⟨S, hS, B, hB, hSB⟩ := mem_prod_iff.1 (hG (Metric.ball_mem_nhds g₀ hε))
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.1 hB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hY δ hδ)
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [ht hS] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  have hmem := hSB (show (t n, Y n ω) ∈ S ×ˢ B from ⟨hn, hδB (Metric.mem_ball.2 hcon)⟩)
  simp only [mem_preimage, Metric.mem_ball] at hmem
  linarith

end Prob

/-! ### Asymptotic normality of the Pickands estimator -/

section Normality

theorem measurable_extRVLimit (γ : ℝ) : Measurable (extRVLimit γ) := by
  by_cases hγ : γ = 0
  · rw [show extRVLimit γ = Real.log from funext fun x => by simp [extRVLimit, hγ]]
    exact measurable_log
  · rw [show extRVLimit γ = fun x => (x ^ γ - 1) / γ from funext (extRVLimit_of_ne hγ)]
    fun_prop

theorem measurable_pickandsMap (γ : ℝ) : Measurable (pickandsMap γ) := by
  have := measurable_extRVLimit γ
  unfold pickandsMap
  fun_prop

theorem measurable_pickandsLog {U : ℝ → ℝ} (hU : Measurable U) (t : ℝ) :
    Measurable (pickandsLog U t) := by
  unfold pickandsLog
  fun_prop

theorem measurable_pickands_pi (n k : ℕ) : Measurable fun y : Fin n → ℝ => pickands y k :=
  ((((measurable_orderStat_pi k).sub (measurable_orderStat_pi (2 * k))).div
    ((measurable_orderStat_pi (2 * k)).sub (measurable_orderStat_pi (4 * k)))).log).div_const _

/-- The asymptotic variance of the Pickands estimator,
`(2 · 2^{2γ} + 1) / (4 D_γ(2)² (log 2)²)`; see `pickandsVariance_of_ne` and
`pickandsVariance_zero` for the closed forms of [dHF, Theorem 3.3.5]. -/
noncomputable def pickandsVariance (γ : ℝ) : ℝ :=
  (2 * (2 ^ γ) ^ 2 + 1) / (4 * extRVLimit γ 2 ^ 2 * Real.log 2 ^ 2)

/-- For `γ ≠ 0` the asymptotic variance of the Pickands estimator is
`γ² (2^{2γ+1} + 1) / (2 (2^γ - 1) log 2)²` ([dHF, Theorem 3.3.5]). -/
theorem pickandsVariance_of_ne {γ : ℝ} (hγ : γ ≠ 0) :
    pickandsVariance γ = γ ^ 2 * (2 ^ (2 * γ + 1) + 1) / (2 * (2 ^ γ - 1) * Real.log 2) ^ 2 := by
  have hd := extRVLimit_pos (γ := γ) one_lt_two
  rw [extRVLimit_of_ne hγ] at hd
  have h1 : (2 : ℝ) ^ γ - 1 ≠ 0 := by
    intro h; rw [h, zero_div] at hd; exact lt_irrefl _ hd
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [pickandsVariance, extRVLimit_of_ne hγ, rpow_add two_pos, rpow_one,
    show 2 * γ = γ + γ by ring, rpow_add two_pos]
  field_simp
  ring

/-- For `γ = 0` the asymptotic variance of the Pickands estimator is `3 / (4 (log 2)⁴)`
([dHF, Theorem 3.3.5]). -/
theorem pickandsVariance_zero : pickandsVariance 0 = 3 / (4 * Real.log 2 ^ 4) := by
  rw [pickandsVariance, extRVLimit_zero_left]
  norm_num
  ring

theorem pickandsVariance_nonneg (γ : ℝ) : 0 ≤ pickandsVariance γ := by
  unfold pickandsVariance; positivity

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Asymptotic normality of the Pickands estimator, uniform representation.** Let the `V_i`
be iid uniform on `(0, 1)` (with values in `(0, 1)` everywhere), let `U` be measurable and
nondecreasing on `(1, ∞)` and of second-order extended regular variation with indices `γ`, `ρ`
and auxiliary functions `a`, `A`. If `k → ∞`, `k/n → 0` and `√k A(n/k) → λ`, then the Pickands
estimator `γ̂_P` of the sample `U(1/(1 - V_i))` satisfies
`√k (γ̂_P - γ) ⇒ N(λ b_{γ,ρ}, σ²_γ)` (`pickandsBias`, `pickandsVariance`). -/
theorem tendstoInDistribution_pickands_uniform {V : ℕ → Ω → ℝ} (hV : ∀ i, Measurable (V i))
    (hind : iIndepFun V P) (hlaw : ∀ i, P.map (V i) = volume.restrict (Set.Icc 0 1))
    (hV01 : ∀ i ω, V i ω ∈ Ioo (0 : ℝ) 1) {U : ℝ → ℝ} (hUm : MonotoneOn U (Ioi 1))
    (hUmeas : Measurable U) {γ ρ lam : ℝ} {a A : ℝ → ℝ}
    (h2 : IsExtSecondOrderRegularlyVarying U γ ρ a A) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0))
    (hlam : Tendsto (fun n => √(k n : ℝ) * A (n / k n)) atTop (𝓝 lam)) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal (lam * pickandsBias γ ρ) (pickandsVariance γ).toNNReal) P') :
    TendstoInDistribution (fun n ω => √(k n : ℝ) *
        (pickands (fun i : Fin n => U (1 / (1 - V i ω))) (k n) - γ)) atTop Z (fun _ => P) P' := by
  set S := brownianCovMatrix fun i => (pickandsTimes i : ℝ≥0) with hS
  set Y : ℕ → Ω → EuclideanSpace ℝ (Fin 3) := fun n ω =>
    WithLp.toLp 2 (fun i => -tailTime V n (k n) (pickandsTimes i * k n) ω) with hY
  have hτ : ∀ i, 0 < pickandsTimes i := by intro i; fin_cases i <;> simp [pickandsTimes]
  have hT := tendstoInDistribution_sqrt_smul_tailTime hV hind hlaw hk hkn pickandsTimes hτ
  have hsk : Tendsto (fun n => √(k n : ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hk)
  have hYm : ∀ n, Measurable (Y n) := fun n => (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.2 fun i => (measurable_tailTime hV n (k n) _).neg)
  set v0 : ℝ := pickandsGrad γ ⬝ᵥ S *ᵥ pickandsGrad γ with hv0
  have hDM := hT.delta_method_gaussian (θh := Y) (θ := pickandsCenter)
    (posSemidef_brownianCovMatrix _) HasLaw.id hsk (hasGradientAt_pickandsMap γ)
    (fun n => ((measurable_pickandsMap γ).comp (hYm n)).aemeasurable)
    (HasLaw.id (μ := gaussianReal 0 v0.toNNReal))
  have hY0 := hT.tendstoInMeasure_of_smul hsk
  have hYc : TendstoInMeasure P Y atTop (fun _ => pickandsCenter) := by
    rw [tendstoInMeasure_iff_dist] at hY0 ⊢
    intro ε hε
    simpa [dist_eq_norm, hY, pickandsCenter] using hY0 ε hε
  have ht : Tendsto (fun n : ℕ => (n : ℝ) / k n) atTop atTop := tendsto_div_atTop_of_tendsto hk hkn
  have hG := TendstoInMeasure.comp_prod_of_tendsto (tendsto_pickandsLog_sub_div h2) ht hYc
  have hB := TendstoInMeasure.mul' (tendstoInMeasure_const_of_tendsto (P := P) hlam) hG rfl
  have hBm : ∀ n, AEMeasurable (fun ω => √(k n : ℝ) * A (n / k n) *
      ((pickandsLog U (n / k n) (Y n ω) - pickandsMap γ (Y n ω)) / A (n / k n))) P := fun n =>
    (measurable_const.mul ((((measurable_pickandsLog hUmeas _).comp (hYm n)).sub
      ((measurable_pickandsMap γ).comp (hYm n))).div_const _)).aemeasurable
  have hC := hDM.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun q : ℝ × ℝ => (Real.log 2)⁻¹ * (q.1 + q.2)) (by fun_prop) hB hBm
  refine (tendstoInDistribution_of_tendstoInMeasure_sub _ _ hC ?_ ?_).congr_limit
    hZ.aemeasurable ?_
  · have h4 : ∀ᶠ n in atTop, 4 * k n < n := by
      have := hkn.const_mul (4 : ℝ)
      rw [mul_zero] at this
      filter_upwards [this.eventually (gt_mem_nhds one_pos),
        (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0] with n h1 h2
      rw [← mul_div_assoc, div_lt_one h2] at h1
      exact_mod_cast h1
    have hg : MonotoneOn (fun v : ℝ => U (1 / (1 - v))) (Ioo 0 1) := by
      intro v hv w hw hvw
      have hv1 : 0 < 1 - v := sub_pos.2 hv.2
      have hw1 : 0 < 1 - w := sub_pos.2 hw.2
      refine hUm ?_ ?_ (one_div_le_one_div_of_le hv1 (by linarith))
      · simp only [mem_Ioi]; rw [lt_one_div one_pos hv1]; linarith [hv.1]; norm_num
      · simp only [mem_Ioi]; rw [lt_one_div one_pos hw1]; linarith [hw.1]; norm_num
    refine tendstoInMeasure_of_eventuallyEq (g := fun _ _ => (0 : ℝ))
      (tendstoInMeasure_const_of_tendsto tendsto_const_nhds) ?_
    filter_upwards [hk.eventually_gt_atTop 0, h4, ht.eventually h2.eventually_ne_zero,
      eventually_gt_atTop 0] with n hk0 hn4 hA0 hn0
    intro ω
    have hk0' : (0 : ℝ) < k n := by exact_mod_cast hk0
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hkk : (k n : ℝ) / n * (n / k n) = 1 := by field_simp
    have hos : ∀ j < n, orderStat (fun i : Fin n => U (1 / (1 - V i ω))) j =
        U ((tailTime V n (k n) j ω)⁻¹ * (n / k n)) := by
      intro j hj
      rw [show (fun i : Fin n => U (1 / (1 - V i ω))) =
        (fun v : ℝ => U (1 / (1 - v))) ∘ (fun i : Fin n => V i ω) from rfl,
        orderStat_comp_monotoneOn hg (fun i => hV01 i ω) hj, tailTime, inv_div,
        div_mul_eq_mul_div, hkk]
    have key : pickands (fun i : Fin n => U (1 / (1 - V i ω))) (k n) =
        pickandsLog U (n / k n) (Y n ω) / Real.log 2 := by
      rw [pickands, hos (k n) (by omega), hos (2 * k n) (by omega), hos (4 * k n) (by omega)]
      simp [pickandsLog, hY, pickandsTimes]
    have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    simp only [Pi.sub_apply]
    rw [key, pickandsMap_center]
    field_simp
    ring
  · intro n
    exact (measurable_const.mul (((measurable_pickands_pi n (k n)).comp (measurable_pi_iff.2
      fun i => hUmeas.comp (measurable_const.div (measurable_const.sub (hV i))))).sub_const
        _)).aemeasurable
  · rw [hZ.map_eq]
    have hv0nn : 0 ≤ v0 := by rw [hv0, hS, pickandsGrad_quadForm]; positivity
    rw [show (fun ω : ℝ => (Real.log 2)⁻¹ * ((id ω, lam * (pickandsBias γ ρ * Real.log 2)).1 +
        (id ω, lam * (pickandsBias γ ρ * Real.log 2)).2)) = (fun x => (Real.log 2)⁻¹ * x) ∘
        (fun x => x + lam * (pickandsBias γ ρ * Real.log 2)) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_add_const,
      gaussianReal_map_const_mul]
    have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    congr 1
    · field_simp
    · apply NNReal.eq
      rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hv0nn,
        Real.coe_toNNReal _ (pickandsVariance_nonneg γ), hv0, hS, pickandsGrad_quadForm,
        pickandsVariance]
      field_simp

end Normality

end ExtremeValueTheory
