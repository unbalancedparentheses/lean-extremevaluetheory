/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import ExtremeValueTheory.Statistics.Moment

/-!
# Extreme quantiles and tail probabilities: the Weissman estimators

PLACEHOLDER
-/

open Filter Topology Set Real MeasureTheory ProbabilityTheory Finset

namespace ExtremeValueTheory

/-! ### Convergence in probability: elementary manipulations -/

section InProbability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A deterministic convergent sequence converges in probability. -/
theorem tendstoInMeasure_const_of_tendsto {ι : Type*} {l : Filter ι} {a : ι → ℝ} {c : ℝ}
    (ha : Tendsto a l (𝓝 c)) :
    TendstoInMeasure P (fun i (_ : Ω) => a i) l (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Metric.tendsto_nhds.1 ha ε hε] with i hi
  have : {ω : Ω | ε ≤ dist (a i) c} = ∅ := by
    ext ω; simp [not_le.2 hi]
  rw [this, measure_empty]

/-- **Continuous mapping theorem** for convergence in probability to a constant, in one
variable. -/
theorem tendstoInMeasure_comp {ι : Type*} {l : Filter ι} {f : ι → Ω → ℝ} {a : ℝ}
    (hf : TendstoInMeasure P f l (fun _ => a)) {φ : ℝ → ℝ} (hφ : ContinuousAt φ a) :
    TendstoInMeasure P (fun i ω => φ (f i ω)) l (fun _ => φ a) :=
  tendstoInMeasure_comp₂ hf hf (φ := fun p => φ p.1) (hφ.comp continuousAt_fst)

/-- Products of sequences converging in probability to constants. -/
theorem tendstoInMeasure_mul {ι : Type*} {l : Filter ι} {f g : ι → Ω → ℝ} {a b : ℝ}
    (hf : TendstoInMeasure P f l (fun _ => a)) (hg : TendstoInMeasure P g l (fun _ => b)) :
    TendstoInMeasure P (fun i ω => f i ω * g i ω) l (fun _ => a * b) :=
  tendstoInMeasure_comp₂ hf hg (φ := fun p => p.1 * p.2) continuous_mul.continuousAt

/-- If `g_i → c` in probability and `f_i = g_i` on events `A_i` whose probability tends to one,
then `f_i → c` in probability. No measurability is needed. -/
theorem tendstoInMeasure_of_eqOn {ι : Type*} {l : Filter ι} {f g : ι → Ω → ℝ} {c : ℝ}
    (hg : TendstoInMeasure P g l (fun _ => c)) {A : ι → Set Ω}
    (hA : Tendsto (fun i => P (A i)ᶜ) l (𝓝 0)) (heq : ∀ᶠ i in l, ∀ ω ∈ A i, f i ω = g i ω) :
    TendstoInMeasure P f l (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  have h := (hg ε hε).add hA
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [heq] with i hi
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  by_cases hωA : ω ∈ A i
  · left
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rwa [← hi ω hωA]
  · right
    exact hωA

/-- If `f_i = g_i` everywhere for `i` large, convergence in probability transfers. -/
theorem tendstoInMeasure_of_eventuallyEq {ι : Type*} {l : Filter ι} {f g : ι → Ω → ℝ} {c : ℝ}
    (hg : TendstoInMeasure P g l (fun _ => c)) (heq : ∀ᶠ i in l, ∀ ω, f i ω = g i ω) :
    TendstoInMeasure P f l (fun _ => c) :=
  tendstoInMeasure_of_eqOn hg (A := fun _ => univ) (by simpa using tendsto_const_nhds)
    (heq.mono fun i hi ω _ => hi ω)

/-- If `Z_n → 0` in probability and `a_n` is eventually bounded, then `a_n Z_n → 0` in
probability. -/
theorem tendstoInMeasure_mul_zero_of_bounded {Z : ℕ → Ω → ℝ}
    (hZ : TendstoInMeasure P Z atTop (fun _ => 0)) {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ᶠ n in atTop, |a n| ≤ C) :
    TendstoInMeasure P (fun n ω => a n * Z n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hZ ⊢
  intro ε hε
  have hC : 0 < |C| + 1 := by positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hZ (ε / (|C| + 1)) (by positivity)) (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [ha] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_mul] at hω ⊢
  by_contra hlt
  push Not at hlt
  have h1 : |a n| * |Z n ω| ≤ (|C| + 1) * |Z n ω| :=
    mul_le_mul_of_nonneg_right (hn.trans ((le_abs_self C).trans (by linarith)))
      (abs_nonneg _)
  rw [lt_div_iff₀ hC] at hlt
  linarith

/-- A sequence of random variables is *bounded in probability* (tight) if for every `ε > 0`
there is `M` with `P(|Z_n| > M) ≤ ε` for all large `n`. This holds, for instance, whenever
`Z_n` converges in distribution. -/
def IsBoundedInProbability (P : Measure Ω) (Z : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ M : ℝ, ∀ᶠ n in atTop, P {ω | M < |Z n ω|} ≤ ε

/-- **Slutsky-type lemma**: if `Z_n` is bounded in probability and `a_n → 0`, then
`a_n Z_n → 0` in probability. -/
theorem tendstoInMeasure_mul_zero_of_isBoundedInProbability {Z : ℕ → Ω → ℝ}
    (hZ : IsBoundedInProbability P Z) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => a n * Z n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨M, hM⟩ := hZ ε hε
  set M' := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [hM, Metric.tendsto_nhds.1 ha (δ / M') (by positivity)] with n h1 h2
  refine (measure_mono fun ω hω => ?_).trans h1
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_mul] at hω h2 ⊢
  by_contra hle
  push Not at hle
  have h3 : |a n| * |Z n ω| ≤ |a n| * M' :=
    mul_le_mul_of_nonneg_left (hle.trans (le_max_left _ _)) (abs_nonneg _)
  rw [lt_div_iff₀ hM'pos] at h2
  linarith

end InProbability

/-! ### The tail quantile function -/

section Quantile

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}

/-- The **tail quantile** `x_p = F^←(1 - p) = inf {x | P(Y > x) ≤ p}` of a real random
variable `Y`, for `0 < p < 1`. -/
noncomputable def tailQuantile (P : Measure Ω) (Y : Ω → ℝ) (p : ℝ) : ℝ :=
  sInf {x | survival P Y x ≤ p}

theorem tailQuantile_le_of_survival_le {p M y : ℝ} (hM : p < survival P Y M)
    (hy : survival P Y y ≤ p) : tailQuantile P Y p ≤ y := by
  refine csInf_le ⟨M, fun x hx => ?_⟩ hy
  by_contra h
  exact absurd ((survival_anti Y (not_le.1 h).le).trans hx) (not_le.2 hM)

theorem le_tailQuantile_of_lt_survival (hY : Measurable Y) {p y : ℝ} (hp : 0 < p)
    (hy : p < survival P Y y) : y ≤ tailQuantile P Y p := by
  have hne : {x | survival P Y x ≤ p}.Nonempty := by
    obtain ⟨x, hx⟩ := ((tendsto_survival_atTop (P := P) hY).eventually (gt_mem_nhds hp)).exists
    exact ⟨x, hx.le⟩
  refine le_csInf hne fun x hx => ?_
  by_contra h
  exact absurd ((survival_anti Y (not_le.1 h).le).trans hx) (not_le.2 hy)

/-- **Asymptotics of tail quantiles** under regular variation: if `F̄ = P(Y > ·)` is regularly
varying with index `-α` and `p_n ↓ 0`, then `x_{p_n} → ∞` and `F̄(c x_{p_n}) / p_n → c ^ (-α)`
for every `c > 0`. -/
theorem tendsto_tailQuantile (hY : Measurable Y) {α : ℝ}
    (hRV : IsRegularlyVarying (survival P Y) (-α)) {p : ℕ → ℝ} (hp0 : ∀ᶠ n in atTop, 0 < p n)
    (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun n => tailQuantile P Y (p n)) atTop atTop ∧ ∀ c : ℝ, 0 < c →
      Tendsto (fun n => survival P Y (c * tailQuantile P Y (p n)) / p n) atTop
        (𝓝 (c ^ (-α))) := by
  set F := survival P Y with hF_def
  have hFanti : Antitone F := survival_anti Y
  have hFpos : ∀ x, 0 < F x := survival_pos hRV
  set t : ℕ → ℝ := fun n => tailQuantile P Y (p n) with ht_def
  have hspec : ∀ M, ∀ᶠ n in atTop, F (t n) ≤ p n ∧ (∀ x < t n, p n < F x) ∧ M ≤ t n := by
    intro M
    filter_upwards [hp0, hp.eventually (gt_mem_nhds (hFpos M))] with n h1 h2
    exact threshold_spec hFanti (continuousWithinAt_survival hY) (tendsto_survival_atTop hY)
      h1 h2
  have htinf : Tendsto t atTop atTop :=
    tendsto_atTop.2 fun M => (hspec M).mono fun n h => h.2.2
  have hr : Tendsto (fun n => F (t n) / p n) atTop (𝓝 1) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have hcont : Tendsto (fun c : ℝ => c ^ (-α)) (𝓝 1) (𝓝 1) := by
        have := Real.continuousAt_rpow_const 1 (-α) (Or.inl one_ne_zero)
        simpa using this.tendsto
      obtain ⟨c, hca, hc1⟩ := (((hcont.eventually (lt_mem_nhds ha)).filter_mono
        nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (1 : ℝ)))).exists
      have hc0 : (0 : ℝ) < c := zero_lt_one.trans hc1
      have hlim := (hRV.tendsto hc0).comp (htinf.atTop_div_const hc0)
      filter_upwards [hlim.eventually (lt_mem_nhds hca), hspec 1, hp0] with n h1 h2 h3
      simp only [Function.comp_apply, mul_div_cancel₀ _ hc0.ne'] at h1
      have htn : 0 < t n := one_pos.trans_le h2.2.2
      have hlt : p n < F (t n / c) := h2.2.1 _ (div_lt_self htn hc1)
      refine h1.trans_le ?_
      rw [div_le_div_iff₀ (hFpos _) h3]
      exact mul_le_mul_of_nonneg_left hlt.le (hFpos _).le
    · filter_upwards [hspec 0, hp0] with n h1 h2
      exact lt_of_le_of_lt ((div_le_one h2).2 h1.1) ha
  refine ⟨htinf, fun c hc => ?_⟩
  have h := ((hRV.tendsto hc).comp htinf).mul hr
  rw [mul_one] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [div_mul_div_cancel₀ (hFpos (t n)).ne']

/-- **Uniform convergence along bounded multipliers**: if `F` is antitone and regularly
varying with index `ρ`, `s_n → ∞` and `c_n ∈ [a, b] ⊆ (0, ∞)`, then
`F(c_n s_n) / (F(s_n) c_n ^ ρ) → 1`. This is the uniform convergence theorem ([BGT, Theorem
1.5.2]) evaluated along a sequence. -/
theorem tendsto_div_mul_rpow_of_mem_Icc {F : ℝ → ℝ} (hF : Antitone F) {ρ : ℝ}
    (hRV : IsRegularlyVarying F ρ) {s c : ℕ → ℝ} (hs : Tendsto s atTop atTop) {a b : ℝ}
    (ha : 0 < a) (hc : ∀ᶠ n in atTop, c n ∈ Icc a b) :
    Tendsto (fun n => F (c n * s n) / (F (s n) * c n ^ ρ)) atTop (𝓝 1) := by
  have hU := Metric.tendstoUniformlyOn_iff.1
    (hRV.tendstoUniformlyOn_Icc (a := 0) (Or.inr (hF.antitoneOn _)) (b₁ := a) (b₂ := b) ha)
  set m := min (a ^ ρ) (b ^ ρ) with hm_def
  obtain ⟨n₀, hn₀⟩ := hc.exists
  have hm : 0 < m :=
    lt_min (rpow_pos_of_pos ha _) (rpow_pos_of_pos (ha.trans_le (hn₀.1.trans hn₀.2)) _)
  have hlow : ∀ x ∈ Icc a b, m ≤ x ^ ρ := by
    intro x hx
    rcases le_total 0 ρ with hρ | hρ
    · exact (min_le_left _ _).trans (rpow_le_rpow ha.le hx.1 hρ)
    · exact (min_le_right _ _).trans (rpow_le_rpow_of_nonpos (ha.trans_le hx.1) hx.2 hρ)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hs.eventually (hU (ε * m) (by positivity)), hc] with n h1 h2
  have hpos : 0 < c n ^ ρ := rpow_pos_of_pos (ha.trans_le h2.1) _
  have h3 := h1 _ h2
  rw [Real.dist_eq] at h3 ⊢
  rw [div_mul_eq_div_div, div_sub_one hpos.ne', abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  rw [abs_sub_comm] at h3
  calc |F (c n * s n) / F (s n) - c n ^ ρ| < ε * m := h3
    _ ≤ ε * c n ^ ρ := by gcongr; exact hlow _ h2

/-- **Quantiles at comparable levels** ([dHF, Theorem 1.1.6 and §4.3]): if `F̄ = P(Y > ·)` is
regularly varying with index `-α`, `α > 0`, and `p_n, r_n ↓ 0` with `d_n = r_n / p_n` bounded
and bounded away from `0`, then `x_{p_n} / (x_{r_n} d_n ^ (1/α)) → 1`. In other words the tail
quantile function is regularly varying with index `γ = 1/α`, locally uniformly. -/
theorem tendsto_tailQuantile_div_tailQuantile (hY : Measurable Y) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (survival P Y) (-α)) {p r : ℕ → ℝ}
    (hp0 : ∀ᶠ n in atTop, 0 < p n) (hp : Tendsto p atTop (𝓝 0))
    (hr0 : ∀ᶠ n in atTop, 0 < r n) (hr : Tendsto r atTop (𝓝 0)) {a b : ℝ} (ha : 0 < a)
    (hd : ∀ᶠ n in atTop, r n / p n ∈ Icc a b) :
    Tendsto (fun n => tailQuantile P Y (p n) / (tailQuantile P Y (r n) * (r n / p n) ^ (1 / α)))
      atTop (𝓝 1) := by
  set F := survival P Y with hF_def
  have hFpos : ∀ x, 0 < F x := survival_pos hRV
  obtain ⟨hs, hFs⟩ := tendsto_tailQuantile hY hRV hr0 hr
  set s := fun n => tailQuantile P Y (r n) with hs_def
  have hT : Tendsto (fun n => F (s n) / r n) atTop (𝓝 1) := by
    simpa using hFs 1 one_pos
  have key : ∀ κ : ℝ, 0 < κ → Tendsto (fun n => F (κ * (r n / p n) ^ (1 / α) * s n) / p n)
      atTop (𝓝 (κ ^ (-α))) := by
    intro κ hκ
    have hc : ∀ᶠ n in atTop, κ * (r n / p n) ^ (1 / α) ∈
        Icc (κ * a ^ (1 / α)) (κ * b ^ (1 / α)) := by
      filter_upwards [hd] with n hn
      have hdn : 0 < r n / p n := ha.trans_le hn.1
      exact ⟨by gcongr; exact hn.1, by gcongr; exact hn.2⟩
    have hU := tendsto_div_mul_rpow_of_mem_Icc (survival_anti Y) hRV hs (by positivity) hc
    have h := (hU.mul hT).const_mul (κ ^ (-α))
    rw [mul_one, mul_one] at h
    refine h.congr' ?_
    filter_upwards [hd, hp0, hr0] with n hn hpn hrn
    have hdn : 0 < r n / p n := ha.trans_le hn.1
    have hid : (κ * (r n / p n) ^ (1 / α)) ^ (-α) = κ ^ (-α) * (p n / r n) := by
      rw [Real.mul_rpow hκ.le (rpow_nonneg hdn.le _), ← Real.rpow_mul hdn.le,
        show 1 / α * -α = -1 by field_simp, Real.rpow_neg_one, inv_div]
    rw [hid]
    have h1 := hFpos (s n)
    have h2 := rpow_pos_of_pos hκ (-α)
    simp only [hF_def] at h1 ⊢
    field_simp
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := min (ε / 2) (1 / 2) with hη_def
  have hη0 : 0 < η := by positivity
  have hηε : η < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hup : (1 + η) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hlo : 1 < (1 - η) ^ (-α) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by linarith) (by linarith) (by linarith)
  filter_upwards [(key (1 + η) (by linarith)).eventually (gt_mem_nhds hup),
    (key (1 - η) (by linarith)).eventually (lt_mem_nhds hlo), hd, hp0,
    hp.eventually (gt_mem_nhds (hFpos 0)), hs.eventually_gt_atTop 0] with n h1 h2 hn hpn hpF hsn
  have hdn : 0 < r n / p n := ha.trans_le hn.1
  have hD : 0 < s n * (r n / p n) ^ (1 / α) := mul_pos hsn (rpow_pos_of_pos hdn _)
  have hU : tailQuantile P Y (p n) ≤ (1 + η) * (r n / p n) ^ (1 / α) * s n :=
    tailQuantile_le_of_survival_le hpF ((div_le_one hpn).1 h1.le)
  have hL : (1 - η) * (r n / p n) ^ (1 / α) * s n ≤ tailQuantile P Y (p n) :=
    le_tailQuantile_of_lt_survival hY hpn ((one_lt_div hpn).1 h2)
  have e1 : tailQuantile P Y (p n) / (s n * (r n / p n) ^ (1 / α)) ≤ 1 + η := by
    rw [div_le_iff₀ hD]; linarith
  have e2 : 1 - η ≤ tailQuantile P Y (p n) / (s n * (r n / p n) ^ (1 / α)) := by
    rw [le_div_iff₀ hD]; linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Quantile

/-! ### Localization of the intermediate order statistic -/

section Localization

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The intermediate order statistic estimates the intermediate quantile** ([dHF, Corollary
2.2.2]): if the iid `X_i` have survival function regularly varying with index `-α`, `α > 0`,
and `k → ∞`, `k / n → 0`, then `X_{(k+1)} / x_{k/n} → 1` in probability. -/
theorem tendstoInMeasure_orderStat_div_tailQuantile {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {α : ℝ} (hα : 0 < α)
    (hRV : IsRegularlyVarying (fun x => (P {ω | x < X 0 ω}).toReal) (-α)) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hkn : Tendsto (fun n => (k n : ℝ) / n) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => orderStat (fun i : Fin n => X i ω) (k n) /
      tailQuantile P (X 0) ((k n : ℝ) / n)) atTop (fun _ => 1) := by
  change IsRegularlyVarying (survival P (X 0)) (-α) at hRV
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hkpos : ∀ᶠ n in atTop, (0 : ℝ) < k n := hkR.eventually_gt_atTop 0
  have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  have hr0 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < k n / n := by
    filter_upwards [hkpos, hnpos] with n h1 h2; positivity
  obtain ⟨hs, hFc⟩ := tendsto_tailQuantile (hX 0) hRV hr0 hkn
  set s := fun n : ℕ => tailQuantile P (X 0) ((k n : ℝ) / n) with hs_def
  have hcnt : ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ ≤
      |(exceedCount (fun i : Fin n => X i ω) (c * s n) : ℝ) / k n - c ^ (-α)|}) atTop
      (𝓝 0) := by
    intro c hc δ hδ
    refine tendsto_measure_abs_exceedCount_div_sub hX hindep hident hk ?_ hδ
    refine (hFc c hc).congr fun n => ?_
    simp only [survival]
    rw [div_div_eq_mul_div, mul_comm]
  have hkn' : ∀ᶠ n : ℕ in atTop, k n < n := by
    filter_upwards [hkn.eventually (gt_mem_nhds one_pos), hnpos] with n h1 h2
    rw [div_lt_one h2] at h1
    exact_mod_cast h1
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set c₂ := 1 + ε / 2 with hc₂
  set c₁ := max (1 / 2) (1 - ε / 2) with hc₁
  have hc₂1 : 1 < c₂ := by linarith
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hc₁1 : c₁ < 1 := max_lt (by norm_num) (by linarith)
  have hc₁ε : 1 - ε / 2 ≤ c₁ := le_max_right _ _
  have hδ₂ : 0 < 1 - c₂ ^ (-α) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg hc₂1 (neg_lt_zero.2 hα); linarith
  have hδ₁ : 0 < c₁ ^ (-α) - 1 := by
    have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hc₁0 hc₁1 (neg_lt_zero.2 hα); linarith
  have h := (hcnt c₂ (by linarith) _ hδ₂).add (hcnt c₁ hc₁0 _ hδ₁)
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hkn', hkpos, hs.eventually_gt_atTop 0] with n hkn hkpos' hsn
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
  obtain ⟨h1, h2⟩ := hcon
  set x : Fin n → ℝ := fun i => X i ω with hx
  have hT2 : orderStat x (k n) ≤ c₂ * s n := by
    rw [orderStat_le_iff x hkn]
    have := (abs_lt.1 h1).2
    have h' : (exceedCount x (c₂ * s n) : ℝ) / k n < 1 := by linarith
    rw [div_lt_one hkpos'] at h'
    exact_mod_cast h'.le
  have hT1 : c₁ * s n < orderStat x (k n) := by
    rw [lt_orderStat_iff x hkn]
    have := (abs_lt.1 h2).1
    have h' : 1 < (exceedCount x (c₁ * s n) : ℝ) / k n := by linarith
    rw [one_lt_div hkpos'] at h'
    exact_mod_cast h'
  have e2 : orderStat x (k n) / s n ≤ c₂ := by rwa [div_le_iff₀ hsn]
  have e1 : c₁ < orderStat x (k n) / s n := by rwa [lt_div_iff₀ hsn]
  have : |orderStat x (k n) / s n - 1| < ε := by
    rw [abs_lt]; constructor <;> linarith
  linarith

end Localization

end ExtremeValueTheory
