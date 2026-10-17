# Faithfulness audit of main theorem statements

Scope: statements and definitions only (proofs are kernel-checked). First audit: the EVD
classification, Fréchet/Weibull MDA, regular variation, Breiman, Fréchet POT, subexponential
laws. Second audit (rows marked †): Gumbel MDA (`DomainOfAttraction/Gumbel.lean`,
`GumbelNecessity.lean`), the general Pickands–Balkema–de Haan file
(`PeaksOverThreshold/Balkema.lean`), order statistics and the Hill estimator (`Statistics/*`),
and stable laws / the generalized CLT (`StableLaws/*`). Rows marked § were added after the third audit and checked by the fourth audit (see below). Third audit (rows marked ‡): the PBdH
converse (`PeaksOverThreshold/Converse.lean`), the asymmetric GCLT
(`StableLaws/GeneralizedCLT.lean`, `Constants.lean`), and random sums / ruin
(`HeavyTails/RandomSums.lean`, `Ruin.lean`, `StretchedExponential.lean`), Karamata's converse
and the Fréchet/Weibull von Mises conditions, the Pickands and moment estimators
(`Statistics/Pickands.lean`, `Moment.lean`), extreme quantiles (`Statistics/ExtremeQuantile.lean`), upper order statistics and records
(`Statistics/UpperOrderStatistics.lean`, `Records.lean`), stationary sequences and the extremal index
(`Dependence/`, `ForMathlib/Probability/Process/Stationary.lean`), and vague convergence and
Poisson random measures (`ForMathlib/MeasureTheory/Measure/Vague.lean`,
`ForMathlib/Probability/{PoissonRandomMeasure,BinomialPointProcess}.lean`). No `sorry`/`axiom`/`admit` found in
`ExtremeValueTheory/`.

References: [EKM] Embrechts–Klüppelberg–Mikosch, *Modelling Extremal Events*;
[dHF] de Haan–Ferreira, *Extreme Value Theory*; [BGT] Bingham–Goldie–Teugels,
*Regular Variation*; [JM] Jessen–Mikosch (2006); [Feller] Feller, *An Introduction to
Probability Theory*, Vol. II; [ST] Samorodnitsky–Taqqu, *Stable Non-Gaussian Random
Processes*.

## Conventions

- **CDFs.** `CumulativeDistributionFunction` is a `StieltjesFunction ℝ` (monotone,
  right-continuous) that tends to 0 at `-∞` and 1 at `+∞`. It is in bijection with
  `ProbabilityMeasure ℝ` (`equiv_probabilityMeasure`).
- **Affine action.** `AffineIncrEquiv` is the group of maps `x ↦ a x + b` with `a > 0`, and
  `(A • F) x = F (A⁻¹ x)`. So `((A n • F) x)^n = F(a_n x + b_n)^n` with
  `(a_n, b_n) = coefs (A n)⁻¹`, which is the c.d.f. of `A n (M_n)`. The textbook normalization
  `P((M_n − d_n)/c_n ≤ x) = Fⁿ(c_n x + d_n)` is covered exactly by taking `A n = (c_n · + d_n)⁻¹`.
- **"Of type" / classification.** "`A • G = Λ`" means `G(x) = Λ(A x)`, i.e. `G` has the same
  type as `Λ`.
- **Standard laws.** `standardGumbelCDF x = exp(−e^{−x})`. `standardFrechetCDF hα x =
  exp(−x^{−α})` for `x > 0` and `0` for `x ≤ 0`. `standardWeibullCDF hα x = exp(−(−x)^α)` for
  `x < 0` and `1` for `x ≥ 0`. The branches are split by `if`, so `rpow` is never applied to a
  negative base.
- **Survival functions** are real-valued: `1 − F x` in the MDA files, `(P {x < X}).toReal` in
  Breiman, and `tail μ x = μ.real (Ioi x) = (μ (Ioi x)).toReal` for subexponential laws. All
  measures involved are finite, so `toReal` never hits `∞`.
- **Regular variation.** `IsRegularlyVarying f ρ` means: `f` is eventually positive, and for
  every `c > 0`, `f(cx)/f(x) → c^ρ` as `x → ∞`. `IsSlowlyVarying` is the case `ρ = 0`. BGT
  builds measurability into the definition; here it is a separate hypothesis wherever it is
  needed (UCT, Potter for general `f`, representation). Eventual positivity makes the junk
  value `x/0 = 0` irrelevant.
- **Integrals.** Wherever an improper integral appears (Karamata, mean excess, Breiman),
  integrability is proved (`integrableOn_Ioi`) or assumed (`hint`, `hmom`). So the Bochner
  "non-integrable ⇒ 0" convention never makes a statement vacuous.
- **Real `⨆`** (`tendsto_sup_excessSurvival`) would be `0` on an unbounded family. Here the
  family is bounded (both terms lie in `[0,1]`) and the proof bounds it explicitly, so this is
  harmless.
- **Right endpoint filter.** `upperEndpointFilter F = ⨅_{F x < 1} 𝓟 (Ioi x ∩ {F < 1})`. It is
  `atTop` if `F < 1` everywhere and `𝓝[<] x_F` otherwise (`upperEndpointFilter_eq_atTop`,
  `_eq_nhdsLT`, together with `exists_rightEndpoint_of_not_lt_one`). So it is never `⊥`; this
  was checked in a scratch file (`NeBot` for every `F`).
- **Sup-form PBdH.** Real `⨆` of an unbounded family is `0`; the scratch file confirms
  `⨆ x ∈ Ici (0:ℝ), x = 0`. The sup-form statements go through `tendsto_iSup_abs_sub_iff`,
  which requires and is given the bound `|·| ≤ 1` (both terms lie in `[0,1]`). So the `⨆` is the
  genuine supremum and the sup forms are equivalent to the uniform forms.
- **Order statistics.** `orderStat x j` is the `(j+1)`-th largest entry for `j < n` (checked:
  `orderStat ![3,1,2] 0 = 3`), and junk `0` for `j ≥ n`. The Hill theorem only uses `k(n) < n`,
  which holds eventually because `k/n → 0`.
- **Stable laws.** `charFun μ t = ∫ exp(i t x) dμ` (Mathlib). `IsSymmStable α c μ` means `μ` is a
  probability measure with `charFun μ t = exp(−c|t|^α)`. It is uninhabited for `α > 2, c > 0`
  and for `c < 0`, but the theorems are stated for `0 < α ≤ 2` (or `< 2`), where
  `exists_isSymmStable` gives inhabitants.
- **i.i.d. model.** For subexponential laws, i.i.d. variables are the coordinates under
  `Measure.pi (fun _ : Fin n => μ)`. `map_pi_sum_eq_convPow` identifies the law of the sum with
  the convolution power `convPow μ n`.

## Table

| Theorem (Lean) | Reference | Informal textbook statement | Lean vs. textbook | Verdict |
|---|---|---|---|---|
| `IsExtremeValueDistr` (def) | EKM Def 3.2.1 / Thm 3.2.3 setting | `H` is non-degenerate and is a weak limit of `c_n⁻¹(M_n − d_n)` for i.i.d. `X_i` | `¬IsDegenerate G ∧ ∃ F As, ∀ x, ContinuousAt G x → ((As n • F) x)^n → G x`. Convergence at continuity points is weak convergence (`tendsto_iff_forall_continuousAt_tendsto`). | FAITHFUL |
| `IsDegenerate` (def) | standard | the law is a point mass | `∀ x, F x = 0 ∨ F x = 1`. `isDegenerate_iff` gives a jump at a single `x₀`, and `eq_diracProba_of_isDegenerate` gives a Dirac mass. | FAITHFUL |
| `MulAction AffineIncrEquiv CDF` | — | law of `aX + b`, `a > 0` | `(A • F) x = F(A⁻¹ x)`. This is the c.d.f. of `A X`, and `mul_smul` holds by `rfl`. | FAITHFUL |
| `standardGumbelCDF` / `standardFrechetCDF` / `standardWeibullCDF` | EKM Def 3.2.6 | `Λ, Φ_α, Ψ_α` | Formulas as in Conventions. Each is shown to be an EVD (`isExtremeValueDistr_standard*`), so the classification is not vacuous. | FAITHFUL |
| `IsExtremeValueDistr.classification` | EKM Thm 3.2.3 (Fisher–Tippett–Gnedenko) | Every EVD is of the type of `Λ`, `Φ_α` or `Ψ_α` for some `α > 0` | Gives `∃ A, A • G = Λ`, or `∃ A, ∃ ξ > 0, A • G = Φ_ξ`, or `∃ A, ∃ ξ > 0, A • G = Ψ_ξ`. No extra hypotheses. | FAITHFUL |
| `IsInMDAFrechet` (def) | EKM §3.3.1, dHF Def 1.1.1 | `∃ c_n > 0, d_n` with `Fⁿ(c_n x + d_n) → Φ_α(x)` | `∃ As, ∀ x, ((As n • F) x)^n → Φ_α x`. "For all `x`" is the same as "at continuity points" because `Φ_α` is continuous. Affine maps absorb the "type" freedom. | FAITHFUL |
| `isInMDAFrechet_iff` | EKM Thm 3.3.7, dHF Thm 1.2.1(1) | `F ∈ MDA(Φ_α)` ⇔ `F̄ ∈ RV_{−α}` | `IsInMDAFrechet F hα ↔ IsRegularlyVarying (1 − F) (−α)`. Eventual positivity of `1 − F` encodes `x_F = ∞`. | FAITHFUL |
| `IsInMDAWeibull` (def) | EKM §3.3.2 | `Fⁿ(c_n x + d_n) → Ψ_α(x)` | Same shape as the Fréchet definition. | FAITHFUL |
| `isInMDAWeibull_iff` | EKM Thm 3.3.12, dHF Thm 1.2.1(2) | `F ∈ MDA(Ψ_α)` ⇔ `x_F < ∞` and `F̄(x_F − 1/t) ∈ RV_{−α}` | The right side is `∃ xF, F xF = 1 ∧ (∀ x < xF, F x < 1) ∧ RV(t ↦ 1 − F(xF − t⁻¹), −α)`, so `xF` is exactly the right endpoint. The junk value `0⁻¹ = 0` only affects `t = 0`, which is irrelevant at `atTop`. | FAITHFUL |
| `IsRegularlyVarying`, `IsSlowlyVarying` (defs) | BGT §1.2, §1.4 | `f > 0` measurable, `f(λx)/f(x) → λ^ρ` | Eventually positive, and the limit holds for every `c > 0`. Measurability is separate (see Conventions). | FAITHFUL (measurability factored out) |
| `isRegularlyVarying_iff_exists_isSlowlyVarying` | BGT Thm 1.4.1 | `f = x^ρ L(x)`, `L` slowly varying | Same, with the equality holding eventually. | FAITHFUL |
| `IsRegularlyVarying.tendstoUniformlyOn_of_measurable` (and `IsSlowlyVarying.` version) | BGT Thm 1.2.1 / 1.5.2 (UCT) | measurable `f ∈ RV_ρ` ⇒ `f(λx)/f(x) → λ^ρ` uniformly on compact `K ⊂ (0,∞)` | Same. `Measurable f` is required on all of ℝ; this is equivalent up to changing `f` far out (see `congr`). | FAITHFUL |
| `IsRegularlyVarying.tendstoUniformlyOn_of_isCompact` | BGT §1.5.2 | UCT for monotone `f` | Requires `f` monotone or antitone on some `[a,∞)` instead of measurable. | FAITHFUL (special case) |
| `potter_bound`, `potter_bound_of_measurable`, `potter_bounds_of_measurable` | BGT Thm 1.5.6(iii) | ∀ `A > 1, δ > 0` ∃ `X`: `f(y)/f(x) ≤ A max((y/x)^{ρ+δ},(y/x)^{ρ−δ})` for `x, y ≥ X` | Same, plus `X > 0` and `f > 0` on `[X,∞)`. The `bounds` version adds the matching lower bound `A⁻¹ min(…)`. The first version assumes eventual monotonicity, the others measurability. | FAITHFUL |
| `isSlowlyVarying_iff_exists_representation` | BGT Thm 1.3.1 | measurable `L` is slowly varying ⇔ `L(x) = c(x) exp ∫_a^x ε(u)/u du` with `c → c₀ > 0`, `ε → 0` | Same, with `a > 0`, `c` and `ε` measurable, and interval integrability of `ε(t)/t` stated explicitly (so the integral is not junk). Measurability of `L` is a global hypothesis on both sides. | FAITHFUL |
| `IsRegularlyVarying.tendsto_integral_Ioi_div` | BGT Prop 1.5.10 (direct half of Karamata) | `f ∈ RV_{−α}`, `α > 1`, locally bounded ⇒ `∫_x^∞ f / (x f(x)) → 1/(α−1)` | Requires `F` antitone on all of ℝ (stronger than local boundedness, but natural for survival functions). Integrability is proved. | FAITHFUL (special case: antitone) |
| ‡ `IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi` | BGT Thm 1.6.1 (converse Karamata) | `x F(x)/∫_x^∞ F → α−1 > 0` ⇒ `F ∈ RV_{−α}` | Assumes `F` antitone on ℝ and integrable on some `(a,∞)`; positivity is derived. BGT allows locally integrable `F`, so this is a special case. | FAITHFUL (special case: antitone) |
| ‡ `IsRegularlyVarying.tendsto_integral_zero_div` | BGT Prop 1.5.8 | `f ∈ RV_ρ`, `ρ > −1`, locally bounded ⇒ `∫_0^x f/(x f(x)) → 1/(ρ+1)` | Measurable, interval-integrable on every `[0,x]`. | FAITHFUL |
| ‡ `isInMDAFrechet_of_vonMises`, `isInMDAWeibull_of_vonMises` | EKM Cor 3.3.8 / 3.3.13 | `x F'(x)/F̄(x) → α` ⇒ `MDA(Φ_α)`; `(x_F−x)F'(x)/F̄(x) → α` ⇒ `MDA(Ψ_α)` | Only differentiability near the endpoint; positivity of `F'` is not assumed (it follows). The Weibull version derives `F x_F = 1`. Instantiated by `paretoCDF` and `powerCDF`. | FAITHFUL |
| `tendsto_measure_mul_div_measure` | Breiman (1965); JM Lemma 4.2(1) | `X ⫫ Y`, `P(X > x) ∈ RV_{−α}`, `Y ≥ 0`, `E Y^{α+ε} < ∞` ⇒ `P(XY > x)/P(X > x) → E Y^α` | Hypotheses are `IndepFun X Y P`, `Y ≥ 0` a.e., RV of `x ↦ (P{x < X}).toReal`, and integrability of `Y^{α+ε}`. The conclusion is `→ ∫ Y^α dP` (`0^α = 0` since `α > 0`, and `Y^α` is integrable). No sign condition on `X`, which matches the reference. | FAITHFUL |
| `gpdSurvival` (def) | EKM Def 3.4.1 | `Ḡ_{ξ,β}(x) = (1+ξx/β)^{−1/ξ}`, or `e^{−x/β}` if `ξ = 0` | Same formula, used only for `ξ ≥ 0`, `x ≥ 0`. For `ξ < 0` and `x > −β/ξ`, `rpow` of a negative base returns junk instead of `0`. This is documented and unused. | FAITHFUL (for `ξ ≥ 0`) |
| `tendstoUniformlyOn_excessSurvival` / `tendsto_sup_excessSurvival` | EKM Thm 3.4.13(b) (Pickands–Balkema–de Haan) | `F ∈ MDA(H_ξ)` ⇔ ∃ `β(u)`: `sup_{0<x<x_F−u} |F_u(x) − Ḡ_{ξ,β(u)}(x)| → 0` | Only the "⇒" direction, only the Fréchet case `ξ = 1/α > 0`, with explicit `β(u) = u/α`. It is stated after the change of variable `x = β(u) y`: `F(u + (u/α)y)/F(u) → Ḡ_{1/α,1}(y)` uniformly for `y ≥ 0`, which is equivalent to the textbook form. Assumes `F` antitone and in `RV_{−α}`, which by `isInMDAFrechet_iff` is exactly `MDA(Φ_α)` when `F = 1 − F_X`. | DIFFERS (one direction, `ξ > 0` only); correct as stated |
| `tendsto_meanExcess_div` | EKM §3.4 (mean excess of RV tails), via Karamata | `F̄ ∈ RV_{−α}`, `α > 1` ⇒ `e(u)/u → 1/(α−1)` | `meanExcess F u = (∫_{Ioi u} F)/F u`, which is `E[X − u | X > u]` when `F = F̄`. Assumes `F` antitone. | FAITHFUL |
| † `IsInMDAGumbel` (def) | EKM §3.3.3, dHF Def 1.1.1 | `Fⁿ(a_n x + b_n) → Λ(x)` | Same shape as the Fréchet definition, for every `x`. Since `Λ` is continuous this is weak convergence. Inhabited: `isInMDAGumbel_standardExponentialCDF`, `isInMDAGumbel_standardGumbelCDF`. | FAITHFUL |
| † `standardExponentialCDF` | — | `1 − e^{−x}` on `x ≥ 0` | `max 0 (1 − e^{−x})`, which is the same function. | FAITHFUL |
| † `isInMDAGumbel_of_vonMises` | EKM Thm 3.3.27 / Ex. 3.3.24, dHF Thm 1.1.8 | `F''` exists near `x_F`, `F' > 0`, `(1−F)F''/(F')² → −1` ⇒ `F ∈ MDA(Λ)` | Same, but only for `x_F = +∞`: the hypotheses are on `(z, ∞)` with the limit at `atTop`, and they imply `F < 1` everywhere. | FAITHFUL (`x_F = ∞` only) |
| `isInMDAGumbel_of_vonMises_nhdsLT` | EKM Thm 3.3.27, dHF Thm 1.1.8 | same, `x_F < ∞`, limit as `x ↑ x_F` | Hypotheses on `(z, x_F)`, limits along `𝓝[<] x_F`, and `F → 1` at `x_F` (needed: a jump at `x_F` breaks the conclusion). Instantiated by `isInMDAGumbel_expNegInvCDF`. | FAITHFUL |
| † `isInMDAGumbel_iff_atTop` / `_nhdsLT` / `isInMDAGumbel_iff` | dHF Thm 1.1.8 + 1.2.5, EKM Thm 3.3.26 | `F ∈ MDA(Λ)` ⇔ ∃ `f > 0` with `F̄(t + x f(t))/F̄(t) → e^{−x}` as `t ↑ x_F`, for all `x` | The `iff` version splits on `x_F = ∞` (filter `atTop`, `F < 1`) or `x_F < ∞` (filter `𝓝[<] x_F`, `F < 1` on `(−∞,x_F)`, `F x_F = 1`). The quantifiers are right: one `f` for all `x`. The `f > 0` condition is "eventually" on the right side, and the necessity lemmas give it everywhere. `F̄ t > 0` along the filter, so `/0` is not an issue. When `t + x f(t) > x_F` the value `F̄ = 0` is the true value. | FAITHFUL |
| † `gpdSurvival'` (def) | EKM Def 3.4.1 | `Ḡ_{ξ,β}`, all `ξ` | `(max (1+ξx/β) 0)^{−1/ξ}` for `ξ ≠ 0`, `e^{−x/β}` for `ξ = 0`. For `ξ < 0` the exponent is `> 0`, so beyond the endpoint the value is `0^{>0} = 0`, which is correct. Agrees with `gpdSurvival` for `ξ ≥ 0` (`gpdSurvival'_eq_gpdSurvival`). This fixes the `ξ < 0` junk of old finding #4. | FAITHFUL |
| † `IsInMDAGEV` (def) | EKM Thm 3.4.5 / dHF Thm 1.1.3 | `F ∈ MDA(H_ξ)` | `ξ > 0`: `MDA(Φ_{1/ξ})`. `ξ < 0`: `MDA(Ψ_{−1/ξ})`. `ξ = 0`: `MDA(Λ)`. These are the right parameter maps. | FAITHFUL |
| † `upperEndpointFilter` (def) | — | `u ↑ x_F` | See Conventions: `atTop` or `𝓝[<] x_F`, never `⊥`. | FAITHFUL |
| † `isInMDAFrechet_iff_tendstoUniformlyOn_excessSurvival` / `_tendsto_sup_` | EKM Thm 3.4.13(b), `ξ > 0` | `F ∈ MDA(Φ_α)` ⇔ ∃ `β(u)` with `sup |F_u − Ḡ_{1/α,β(u)}| → 0` | Both directions now, with the explicit `β(u) = u/α` on both sides. "⇒" with a specific `β` is stronger than the textbook. "⇐" with a specific `β` is weaker than the textbook "⇐" (which allows any `β`). Uniform on `Ici 0` after the change of variable `x ↦ β(u)x`, which is equivalent. | DIFFERS (canonical `β` in "⇐"); correct |
| † `isInMDAWeibull_iff_tendstoUniformlyOn_excessSurvival` / `_tendsto_sup_` | EKM Thm 3.4.13(b), `ξ < 0` | same, `ξ = −1/α` | `∃ x_F, F x_F = 1 ∧ (∀ x < x_F, F x < 1) ∧` uniform convergence on `Ici 0` along `𝓝[<] x_F` to `Ḡ_{−1/α,1}(x) = (max(1−x/α) 0)^α`, with `β(u) = (x_F − u)/α`. The GPD endpoint `x = α` maps to `u + β(u)α = x_F`, so "`x ≥ 0`" is the same as the textbook `0 < x < x_F − u`, since both sides vanish beyond it. Checked by hand on `F̄(x_F − s) = s^α`. The same caveat about canonical `β` in "⇐" applies. | DIFFERS (canonical `β` in "⇐"); correct |
| † `tendstoUniformlyOn_excessSurvival_of_auxiliary`, `isInMDAGumbel_and_tendstoUniformlyOn_of_auxiliary_*` | EKM Thm 3.4.13(b), `ξ = 0`; dHF Thm 1.1.6 | auxiliary `f` ⇒ `sup_x |F̄(u+f(u)x)/F̄(u) − e^{−x}| → 0` | Same, uniform on `Ici 0` along any filter. For finite `x_F`, uniformity on all `x ≥ 0` (not just `x < (x_F−u)/f(u)`) is stronger or equal, and it is proved. | FAITHFUL |
| † `exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV'` | EKM Thm 3.4.13(b) "⇒", dHF Thm 1.1.6 | `F ∈ MDA(H_ξ)` ⇒ ∃ `β > 0`, `sup_{x≥0} |F̄(u+β(u)x)/F̄(u) − Ḡ_{ξ,1}(x)| → 0` as `u ↑ x_F` | Exactly this, for all `ξ ∈ ℝ`, with no extra hypothesis (the `haux` of the unprimed version is discharged by de Haan's theorem). `Ḡ_{ξ,β}(x) = Ḡ_{ξ,1}(x/β)`, so scale 1 after rescaling is equivalent. Instantiated in a scratch file on `standardExponentialCDF` with `ξ = 0`. Only "⇒" (see finding 2). | FAITHFUL ("⇒" half) |
| † `orderStat` (def) | dHF §3.2 | `X_{(1)} ≥ ⋯ ≥ X_{(n)}` | `orderStat x j = X_{(j+1)}` through `Tuple.sort` and `Fin.rev`; junk `0` for `j ≥ n`. `lt_orderStat_iff` gives the exceedance duality. Checked on a concrete sample. | FAITHFUL |
| † `hill` (def) | dHF (3.2.2) | `γ̂ = k⁻¹ Σ_{i<k} (log X_{n−i,n} − log X_{n−k,n})` | `k⁻¹ Σ_{i<k} (log X_{(i+1)} − log X_{(k+1)})`, the same formula. `Real.log` of a nonpositive order statistic is `log|x|` (junk; see finding 5). | FAITHFUL (positive samples) |
| † `tendstoInMeasure_hill` | dHF Thm 3.2.2; Mason (1982) | iid, `F̄ ∈ RV_{−α}`, `α > 0`, `k → ∞`, `k/n → 0` ⇒ `γ̂ →_P 1/α` | Hypotheses: `iIndepFun X P`, `IdentDistrib (X i) (X 0)`, measurability, RV of `x ↦ P(X₀ > x).toReal` (finite measure, so `toReal` is safe), `k → ∞`, `k/n → 0`. The conclusion is `TendstoInMeasure` to the constant `1/α`. Not vacuous: `tendstoInMeasure_hill_pareto` instantiates RV. No positivity assumption on `X`, which matches dHF (junk logs occur only on an event of vanishing probability). Only the consistency direction; Mason's converse is not claimed. | FAITHFUL |
| ‡ `pickands` (def), `tendstoInMeasure_pickands` | EKM Thm 6.4.1, dHF §3.3 | `F ∈ MDA(H_ξ)`, `k → ∞`, `k/n → 0` ⇒ `ξ̂ →_P ξ` | `pickands x k` uses `orderStat x k, 2k, 4k`, which are `X_{n−k,n}, X_{n−2k,n}, X_{n−4k,n}`. The hypotheses are iid (`iIndepFun`, `IdentDistrib`) with `F` the c.d.f. of `X 0` and `IsInMDAGEV ξ`. All `ξ ∈ ℝ`. Instantiated on the exponential law (`ξ = 0`). Junk values (`log` of a nonpositive ratio, order statistics with `4k ≥ n`) occur only on events of vanishing probability. | FAITHFUL |
| ‡ `momentEstimator`, `tendstoInMeasure_momentEstimator_of_isInMDAGEV'` | dHF Thm 3.5.2 (Dekkers–Einmahl–de Haan) | `γ̂ = M₁ + 1 − ½(1 − M₁²/M₂)⁻¹ →_P γ` for all `γ`, `x_F > 0` | Same formula and hypotheses (`x_F > 0` is stated as `∃ y > 0, F y < 1`). | FAITHFUL |
| ‡ `IsExtendedRegularlyVarying` (def), `isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile` | dHF Def B.2.1, Thm 1.1.6 | `F ∈ MDA(H_γ)` ⇔ `U` extended RV with index `γ` | `U(t) = inf{y : 1 − F(y) ≤ 1/t}`. Both directions. The `γ ≠ 0` corollaries assume `f` monotone (true for `U`); without some regularity they fail. | FAITHFUL |
| ‡ `IsSecondOrderRegularlyVarying` (def) | dHF Def 2.3.1, §2.3 | `(U(tx)/U(t) − x^γ)/A(t) → x^γ(x^ρ−1)/ρ` | Same, with `|A| ∈ RV_ρ` and constant sign of `A` built into the definition (dHF derive `|A| ∈ RV_ρ` from the limit when it is non-degenerate, Thm 2.3.3). | FAITHFUL (one derived property assumed) |
| § `tendstoInMeasure_hill_of_isMDependent`, `tendstoInMeasure_hill_of_alphaMixing_rate` | Resnick–Stărică (1995), Rootzén–Leadbetter–de Haan (1998) | Hill consistency for dependent stationary data | Reduction to `Var(exceedance count)/k² → 0` (identical marginals only). m-dependent: no stationarity needed. α-mixing: stationarity, cluster condition `Σ_{h≤rₙ} P(X_h > uₙ | X₀ > uₙ) = o(k)` (assumed, not derived from the tail process), `(n/k)²α(rₙ+1) → 0`. The mixing rate is a simple sufficient condition, not the sharpest in the literature. | FAITHFUL |
| ‡ `tendstoInDistribution_hill` | dHF Thm 3.2.5 | second order, `√k A(n/k) → λ` ⇒ `√k(γ̂ − γ) ⇒ N(λ/(1−ρ), γ²)` | Same, with `U = survivalQuantile` of the tail; limit stated as `TendstoInDistribution` to any `Z` with the Gaussian law. Exact Pareto case also proved without `k/n → 0`. | FAITHFUL |
| ‡ `tendsto_measureReal_orderStat_le`, `tendsto_measureReal_affine_orderStat_le` | EKM Thm 4.2.3, LLR Thm 2.2.2 | `n F̄(uₙ) → τ` ⇒ `P(X_{(k)} ≤ uₙ) → e^{−τ} Σ_{j<k} τ^j/j!` | Same (`orderStat x j` is `X_{(j+1)}`). The affine version needs `H(x) ∈ (0,1)`, i.e. points inside the support. | FAITHFUL |
| ‡ `tendsto_measureReal_orderStat_zero_le_and_orderStat_one_le` | EKM §4.2 | joint limit of the two largest | Same, two levels only; `k > 2` levels not covered. | FAITHFUL (two levels) |
| ‡ `measureReal_isRecord`, `tendstoInMeasure_recordCount_div_log` | EKM §5.4, Rényi | iid, continuous `F`: `P(I_k = 1) = 1/k`, `N_n/log n →_P 1` | "Continuous" is stated as atomless (`P(X₀ = x) = 0`). Indices start at `0`, so the probability for index `k` is `1/(k+1)`. Only pairwise independence of record indicators is proved, which is enough for the law of large numbers. | FAITHFUL |
| ‡ `weissman`, `tendstoInMeasure_weissman_div*` | dHF Thm 4.3.1, Weissman (1978) | `x̂_p / x_p →_P 1` | `tailQuantile` is `inf{x : F̄(x) ≤ p}`. Intermediate levels (`d_n ∈ [a,b]`): unconditional. Far tail: assumes `√k(γ̂ − γ) = O_P(1)`, `log d_n/√k → 0`, and the bias condition `x_{pₙ}/(x_{k/n} d_n^{1/α}) → 1` as hypotheses (dHF derive the bias condition from second-order RV; here it is proved only for exact Pareto tails). | DIFFERS (bias and rate assumed in the far-tail case); correct |
| § `tendstoInMeasure_weissman_div_of_secondOrder`, `tendstoInDistribution_weissman` | dHF §4.3 | second order, `√k A(n/k) → λ`, `log d_n/√k → 0` ⇒ `x̂/x_p →_P 1`; `(√k/log d_n)(x̂/x_p − 1) ⇒ N(λ/(1−ρ), γ²)` | Requires `ρ < 0` (the uniform remainder bound used is only valid then); `ρ = 0` is not covered. `d_n ≥ 1` (weaker than `n pₙ = o(k)`) for consistency, `d_n → ∞` for normality. Normality of the tail-probability estimator not done. | DIFFERS (`ρ < 0`); correct |
| § `tendstoInDistribution_weissman_of_rho_eq_zero`, `tendstoInDistribution_tailProbEstimator(_of_rho_eq_zero)` | dHF §4.3–4.4 | `ρ ≤ 0` extrapolation | `ρ = 0` needs a majorant of `|A|` on the extrapolation range (automatic if `|A|` eventually monotone); normality at `ρ = 0` assumes `A` asymptotically constant there, giving centered limits (bias cancellation). Not checked against the dHF text for `ρ = 0`. | FAITHFUL (extra regularity at `ρ = 0`) |
| ‡ `tailProbEstimator`, `tendstoInMeasure_tailProbEstimator_div*` | dHF §4.4 | `p̂(yₙ)/F̄(yₙ) →_P 1` | Same structure as the Weissman row. | DIFFERS (same caveat); correct |
| ‡ `returnLevel`, `gevFun_returnLevel` | Coles §3.1.3 | `H_ξ(z_m) = 1 − 1/m` | Same, for `m > 1`. | FAITHFUL |
| † `IsStable`, `IsStrictlyStable` (defs) | Feller VI.1 Def 1; ST Def 1.1.4 | non-degenerate, `μ^{*n} = law(a_n X + b_n)` (`b_n = 0` for strictly stable), `a_n > 0` | Same, for all `n ≥ 1`; non-degeneracy is `μ ≠ δ_x` for all `x`. Inhabited by Gaussian, Cauchy, and `IsSymmStable` with `0<α≤2`, `c>0`. | FAITHFUL |
| † `IsSymmStable` (def) | ST (1.2.3), Feller XVII.4 | `SαS`: `φ(t) = exp(−c|t|^α)` | `IsProbabilityMeasure μ ∧ ∀ t, charFun μ t = exp(−c|t|^α)`. `|t|^α` is `rpow` of a nonnegative base, so there is no junk. See Conventions for parameter ranges. | FAITHFUL |
| † `stableConst` (def) | Feller XVII.5 | `C_α = α ∫₀^∞ (1−cos u) u^{−α−1} du` | Same formula. The integral is Bochner, and is junk `0` when not integrable (`α ∉ (0,2)`). It is only used with `0 < α < 2`, where `stableConst_pos` proves it is positive and integrability is proved (`integrableOn_one_sub_cos_mul_rpow`). Value checked: `n∫(1−cos(tx/a_n))dμ → ∫(1−cos(tu)) d(u^{−α})`, which equals `C_α|t|^α`. | FAITHFUL |
| † `exists_isSymmStable` | ST §1.1, Feller XVII.4 | `SαS(c)` exists for `0 < α ≤ 2` | For `0 < α ≤ 2`, `c ≥ 0`. `c = 0` gives `δ₀`, which is allowed here and is not claimed to be stable. | FAITHFUL |
| † `exists_tendsto_of_tendsto_charFun` | Feller XV.3 Thm 2 (Lévy continuity) | `φ_n → f` pointwise, `f` continuous at 0 ⇒ `f = φ_ν` and `μ_n ⇒ ν` | Same, on a finite-dimensional real inner product space; convergence is in `ProbabilityMeasure E` (weak topology). | FAITHFUL |
| † `charFun_cauchyMeasure` (+ `isStrictlyStable_cauchyMeasure`) | Feller XV.2 | `φ(t) = exp(i t x₀ − γ|t|)` | Same, for all `γ ≥ 0` (`γ = 0` is the Dirac case, also correct). | FAITHFUL |
| † `tendsto_map_convPow_of_isRegularlyVarying` / `tendstoInDistribution_inv_mul_sum_of_isRegularlyVarying` | Feller XVII.5 Thm 2, EKM Thm 2.2.8 (symmetric case) | `X` symmetric, `P(|X|>x) ∈ RV_{−α}`, `0<α<2`, `n P(|X|>a_n) → 1` ⇒ `S_n/a_n ⇒ SαS(C_α)` | Hypotheses: symmetry `μ.map neg = μ`, RV of the two-sided tail `absTail`, `a n > 0`, `n·absTail μ (a n) → 1`. These are satisfiable: `SymmPareto` with `a_n = (n+1)^{1/α}` is used in `exists_isSymmStable_stableConst`. The normalization `a_n⁻¹ Σ_{k<n} X_k` with limit `exp(−C_α|t|^α)` is correct (see the `stableConst` row). The i.i.d. version takes `Y ∼ ν` with `IsSymmStable α C_α ν` and gives `TendstoInDistribution`; `ν` exists by the first theorem. Only the symmetric case: no centering constants, no skewness `β`. | DIFFERS (symmetric case only); correct |
| ‡ `IsMaxStable` (def), `isMaxStable_iff_isExtremeValueDistr` | EKM Def 3.2.1, Thm 3.2.2 | non-degenerate `G` with `Gⁿ(aₙx + bₙ) = G(x)` for all `n ≥ 1` ⇔ EVD | Same. | FAITHFUL |
| ‡ `gevCDF` (def), `IsExtremeValueDistr.exists_smul_eq_gevCDF` | EKM Def 3.4.1, Thm 3.4.5 | `H_ξ`; every EVD is of type `H_ξ` | Built from `gevFun` (which equals `0` or `1` outside the support, correctly). Explicit affine maps to `Φ_{1/ξ}`, `Ψ_{−1/ξ}`, `Λ`. | FAITHFUL |
| ‡ GEV moments (`integral_id_gevCDF`, `variance_id_gevCDF`, `integral_id_gevCDF_zero`, `integral_mul_gevFun_pow_gevCDF`) | EKM §3.4 (table number unverified), Hosking–Wallis–Wood (1985) | mean `(Γ(1−ξ)−1)/ξ`, Gumbel mean `γ`, variance, PWMs | Integrability is proved (`ξ < 1`, resp. `ξ < 1/2`), so Bochner junk is avoided. The Gumbel variance `π²/6` and the `ξ = 0` PWMs are proved too (`variance_id_gevCDF_zero`, `integral_mul_gevFun_pow_gevCDF_zero`). | FAITHFUL |
| ‡ `tendstoInMeasure_blockMaxEmpCDF` | Coles §3.3 | block-maxima empirical c.d.f. → `H` | Normalizing constants are given (known), as stated in the docstring. | FAITHFUL (known norming) |
| ‡ `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival` / `_tendsto_sup_` | EKM Thm 3.4.13(b), dHF Thm 1.1.6 | `F ∈ MDA(H_ξ)` ⇔ ∃ `β(u) > 0`: `sup_{x≥0} |F̄(u+β(u)x)/F̄(u) − Ḡ_{ξ,1}(x)| → 0` as `u ↑ x_F` | Exactly this, for every `ξ`, `β` arbitrary and eventually positive along `upperEndpointFilter` (never `⊥`). The converse proves that there is no atom at a finite `x_F` rather than assuming it. | FAITHFUL |
| ‡ `HasStableCharFun` (def) | ST Def 1.1.6 (`α ≠ 1`) | `φ(t) = exp(−σ^α|t|^α(1 − iβ sign t tan(πα/2)))` | `exp(−c|t|^α + i e sign(t)|t|^α)`. The predicate itself has no parameter restrictions; it is the strictly stable family only for `0 < α < 2`, `α ≠ 1`, `c > 0`, `|e| ≤ c|tan(πα/2)|` (at `α = 1` it describes a Cauchy law with drift). In that range it is the ST family with `c = σ^α`, `e = cβ tan(πα/2)`, and `stableSkewConst_eq_mul_tan` proves the GCLT's `e` is `(2p−1) C_α tan(πα/2)`. `iff_isSymmStable` for `e = 0`. | FAITHFUL (parametrization differs) |
| ‡ `tendsto_map_convPow_of_isRegularlyVarying_of_lt_one`, `tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt` | Feller XVII.5 Thm 2, EKM Thm 2.2.8 (`α ≠ 1`) | RV two-sided tail, tail balance `p`, `n P(|X|>aₙ) → 1` ⇒ `(S_n − b_n)/aₙ ⇒` stable | Hypotheses: RV of `absTail`, `μ(Ioi x)/absTail → p` (`q = 1−p` is derived), `aₙ > 0`. `b_n = 0` for `α < 1`, `n ∫ y dμ` for `1 < α < 2` (integrability is proved). Limit: `HasStableCharFun α C_α ((2p−1)E_α)`. Sufficiency here; the converse (RV and tail balance) is in `GCLTConverse.*`. The hypotheses are instantiated (symmetric Pareto, `p = 1/2`); no skewed `p ≠ 1/2` instance is in the library. | DIFFERS (sufficiency only); correct |
| ‡ `ProbabilityTheory.IsStationary` (def) | LLR §3.1 | strict stationarity | Law of the shifted path `(X_{n+1})ₙ` equals the law of `(Xₙ)ₙ` on `ℕ → ℝ`. Equivalent to shift-invariance of all finite-dimensional laws. | FAITHFUL |
| ‡ `ConditionD`, `ConditionD'` (defs) | LLR §3.2, (3.4.3); EKM §4.4 | `D(uₙ)`: `|P(max_{A∪B} ≤ uₙ) − P(max_A)P(max_B)| ≤ α_{n,lₙ}` for index sets separated by `lₙ = o(n)`; `D'`: `limsup n Σ_{j<n/k} P(X₀>uₙ, X_j>uₙ) → 0` | Same. `D'` is stated in the equivalent ε–k₀ form. | FAITHFUL |
| ‡ `tendsto_measureReal_partialMax_le_exp` | LLR Thm 3.4.1, EKM Thm 4.4.3 | stationary, `D`, `D'`, `n P(X₀>uₙ) → τ` ⇒ `P(M_n ≤ uₙ) → e^{−τ}` | Same. | FAITHFUL |
| ‡ `HasExtremalIndex` (def) | LLR §3.7, EKM Def 8.1.1 | `θ ∈ [0,1]` with `P(M_n ≤ uₙ(τ)) → e^{−θτ}` whenever `n P(X₀>uₙ(τ)) → τ` | Quantifies over all such level sequences. When the marginal has atoms, no such sequence may exist for some `τ`, and the condition is then vacuous there (as in the textbook, which assumes such levels exist). `HasExtremalIndexStrict` adds existence of levels for every `τ` (LLR), with uniqueness of `θ` (`HasExtremalIndex.unique`). | FAITHFUL |
| ‡ `tendsto_measureReal_partialMax_le_pow`, `isExtremeValueDistr_pow` | LLR Thm 3.7.1, EKM Thm 8.1.2 | `F^n(aₙx+bₙ) → H(x)` and extremal index `θ > 0` ⇒ `P(M_n ≤ aₙx+bₙ) → H(x)^θ`, an EVD of the same type | Same; `θ > 0` is required, as in the textbook. Instantiated by `hasExtremalIndex_movingMax` (`θ = 1/2`) and the iid case. | FAITHFUL |
| ‡ `HasSpectralTailProcess`, `HasTailProcess` (defs) | BS09 §2, KS20 Ch. 5 | conditional weak limits of `X/|X_0|` and `X/x` given `|X_0| > x` on every finite window | Same, with windows any finite `S ⊂ ℤ` and convergence tested on bounded continuous functions (`TendstoLawCond`). Stationarity for this file is `HasShiftInvariantWindows` (all finite windows are shift-invariant), equivalent to strict stationarity. | FAITHFUL |
| ‡ `polar_iff`, `HasSpectralTailProcess.hasTailProcess` | BS09 Thm 2.1 | tail process ⇔ spectral tail process; `Y = |Y_0|Θ`, `|Y_0|` Pareto independent of `Θ` | Same. The BS09 erratum (SPA 121 (2011)) was not consulted; statements were checked against KS20 and PS18 instead. | FAITHFUL |
| ‡ `HasSpectralTailProcess.lintegral_timeChange` | BS09 Thm 3.1, KS20 Thm 5.3.1 | `E[g(Θ_{·−i}) 1{Θ_{−i} ≠ 0}] = E[g(Θ_·/|Θ_i|)|Θ_i|^α]` | Same, for measurable `g ≥ 0` on finite windows and stationary `X`. | FAITHFUL |
| ‡ `candidateExtremalIndex` (def) and its properties | KS20 §7.5, PS18 §4 | `ϑ = E[sup_{k≥0}|Θ_k|^α − sup_{k≥1}|Θ_k|^α]` | Suprema in `[0,∞]` with `∞ − ∞ = 0`; when `Θ_t → 0` the suprema are finite and this is the textbook real expectation. With the convention, `ϑ = P(sup_{k≥1}|Y_k| ≤ 1)` holds unconditionally. The link with the block extremal index is proved: `θ ≤ ϑ` (`le_candidateExtremalIndex`) and `θ = ϑ` under anticlustering. | FAITHFUL (convention for infinite suprema) |
| § `IsRegVarVector` (def), `isRegVarVector_iff`, `IsRegVarVector.eq_polarMeasure` | Hult–Lindskog (2006), Resnick (2007) Thm 6.1, KS20 §2.1 | `X` regularly varying with exponent measure `μ` ⇔ `‖X‖ ∈ RV_{−α}` and spectral limit `S`; `μ = α r^{−α−1}dr ⊗ S` | Normalized by `P(‖X‖ > x)` (so `μ{‖y‖>1} = 1`), tested on bounded continuous functions vanishing near `0`. Equivalent to the `aₙ`-sequence form up to the scaling of `μ`. Converse Cramér–Wold not formalized. | FAITHFUL |
| § `isRegVarVector_of_indepFun` | Resnick (2007) §6.5 | independent RV components ⇒ `μ` on the axes | Assumes `X₁, X₂ ≥ 0` and tail ratio `P(X₂ > x)/P(X₁ > x) → c`. | FAITHFUL (nonnegative, tail-balanced case) |
| § `AntiClusteringAt`, `ForwardAntiClusteringAt`, `AntiClustering`, `ConditionA` (defs) | BS09 (4.1), KS20 §6.1 | `AC(rₙ)`; block condition `𝒜(uₙ)` | AC in the equivalent ε–m form. `AntiClustering` is two-sided at every level `aₙx`; the theorems only use the forward half at one level sequence. | FAITHFUL |
| § `HasSpectralTailProcess.tendsto_blockRatio`, `.hasExtremalIndex_abs`, `.tendsto_partialMax_abs_of_antiClustering` | BS09 Prop 4.2, KS20 §7.5 | under AC and mixing, extremal index `θ = ϑ` | The cluster ratio → `ϑ` uses only stationarity, the tail process, `uₙ, rₙ → ∞` and forward AC at `uₙ`; condition `𝒜` (a hypothesis here; derived from α-mixing in `conditionA_of_alphaMixing`) and `rₙ/n → 0` enter only for `e^{−ϑτ}`. Extremal index stated for `|X|` (and for `X ≥ 0`). | FAITHFUL (`𝒜` assumed) |
| § `HasSpectralTailProcess.le_candidateExtremalIndex` | KS20 Lemma 7.5.4 (hypotheses not verified) | `θ ≤ ϑ` | Without anticlustering, but with `𝒜(uₙ)` along one level sequence, `nP(|X₀|>uₙ) → τ > 0`, `rₙ → ∞`, `rₙ/n → 0`. | FAITHFUL (as stated; literature hypotheses unchecked) |
| § `HasSpectralTailProcess.le_candidateExtremalIndex'` | KS20 Lemma 7.5.4 (as described by Bai–Kulik–Wang 2024: "always holds", stated for `ℝ₊`-valued series) | `θ ≤ ϑ` | Only stationarity, spectral tail process, existence of `θ` for `|X|`, measurability, `α > 0`. No AC, mixing, `𝒜` or `rₙ`. KS20 itself not consulted directly. | FAITHFUL |
| ‡ `candidateExtremalIndex_movingMax`, `hasExtremalIndex_movingMax_candidateExtremalIndex` | EKM Ex. 8.1.3 | moving maximum: `θ = ϑ = 1/2` | Spectral tail process proved from scratch for Pareto innovations (assumed nonnegative pointwise, a null-set normalization). `θ = 1/2` is now also obtained through the main theorem via 1-dependence (`hasExtremalIndex_movingMax_of_isMDependent`). | FAITHFUL |
| § `LinearProcess.tendsto_measureReal_sum_mul_div`, `.tendsto_measureReal_tsum_mul_div` | EKM Lemma A3.26, Davis–Resnick (1985) | `P(Σψ_jZ_j > x)/P(|Z|>x) → Σ|ψ_j|^α(p1{ψ_j>0}+q1{ψ_j<0})` | Finite sums: real-valued iid noise, no sign condition. Infinite sums: only `0 < δ < α < 1` with `Σ|ψ_j|^δ < ∞`; `α ≥ 1` (which needs centering) not covered. | DIFFERS (`α < 1` for series); correct |
| § `MovingAverage.hasSpectralTailProcess`, `.candidateExtremalIndex_spectral` | KS20 Ch. 15, EKM Ex. 8.1.4 | spectral tail process and `ϑ = max ψ^α/Σψ^α` | Finite order, `ψ_j ≥ 0`, noise nonnegative everywhere. `θ = ϑ` for this process is proved via m-dependence (`MovingAverage.hasExtremalIndex`). | FAITHFUL (nonnegative case) |
| § `strongMixingCoeff`, `betaMixingCoeff`, `IsMDependent` (defs) | Bradley (2005) | `α`, `β` mixing; m-dependence | Coefficients valued in `ℝ≥0∞`, supremum over `s` of past `σ(X_t : t ≤ s)` vs future `σ(X_t : t ≥ s + h)`; `β` with the ½ factor over finite partitions. m-dependence: past up to `s` independent of future from `s + m + 1`. | FAITHFUL |
| § `conditionA_of_alphaMixing`, `conditionA_of_isMDependent` | BS09 §4, KS20 §7.5 | mixing at a rate ⇒ `𝒜(uₙ)` | Stationarity, `rₙ → ∞`, `rₙ/n → 0`, `lₙ/rₙ → 0`, `(n/rₙ)α(lₙ) → 0`, `n P(X₀ > uₙ)` bounded. Nothing for β-mixing beyond `α ≤ β`. | FAITHFUL |
| § `HasSpectralTailProcess.hasExtremalIndex_of_isMDependent`, `MovingAverage.hasExtremalIndex` | EKM §8.1 (Ex. 8.1.4) | m-dependent: `θ = ϑ`; moving average `θ = max ψ^α/Σψ^α` | Extremal index of `|X|` in general; the examples drop `|·|` because their noise is nonnegative. Moving average: finite order, `ψ ≥ 0`, nonnegative iid regularly varying noise. Infinite-order processes not covered. | FAITHFUL (finite order, nonnegative) |
| § `InfiniteMovingAverage.hasSpectralTailProcess_and_hasExtremalIndex(_of_lt_one)`, `AR1.hasExtremalIndex(_of_pos)` | Davis–Resnick (1985), KS20 Ch. 15, EKM §8.1 | infinite MA: `θ = ϑ = sup ψ^α/Σψ^α`; AR(1): `θ = 1 − φ^α` | The `_of_lt_one`/`_of_pos` versions hold for every `α > 0` with `Σψ^δ < ∞` for some `δ < min(α,1)` (for `α > 1` slightly stronger than the optimal `Σψ < ∞`); `ψ ≥ 0`, nonnegative iid noise. The original versions are the `α < 1` special case. AR(1) is the MA representation, shown to satisfy the recursion a.s.; uniqueness of the stationary solution proved in `AR1.ae_eq_process`. | FAITHFUL (δ < 1 condition) |
| § `IsSimpleMaxStable` (def), `exists_isSimpleMaxStable_of_spectralMeasure`, `IsPoissonRandomMeasure.isSimpleMaxStable_map_process` | de Haan (1984), dHF §6.1, Resnick Prop 5.11 | spectral representation of max-stable vectors/processes | Max-stability in the c.d.f. form `F(y)^n = F(y/n)` with unit Fréchet margins. Only the constructive "⇐" direction; the "⇒" direction (every simple max-stable law has a spectral measure) is not proved. Processes via finite-dimensional laws; the marking theorem (PRM marks ↔ iid processes) not formalized. | DIFFERS ("⇐" only); correct |
| § `hasExceedanceLevels_of_isRegularlyVarying`, `*_strict` corollaries | LLR Thm 1.7.13 | RV tails admit levels for every `τ`; extremal index unique | The strict versions (`HasExtremalIndexStrict`) of all extremal-index examples. | FAITHFUL |
| § `HasSpectralTailProcess.candidateExtremalIndex_eq_measure_backward` | BS09 §4, KS20 §5.6 | `ϑ = P(sup_{k≤−1}|Y_k| ≤ 1)` | Stationarity and `Θ_t → 0` at both ends (from two-sided AC in the `_of_antiClusteringAt` version). | FAITHFUL |
| § `SumAntiClusteringAt`, `tendstoInMeasure_hill_of_alphaMixing_of_sumAntiClustering` | KS20 §9.1 | Hill consistency under `S(rₙ, uₙ)` and α-mixing | The cluster condition is derived from `S(rₙ,uₙ)` or `rₙ = o(kₙ)`; plain anticlustering does not imply it (it bounds a probability, not an expected count). Examples: moving maximum and finite moving average. | FAITHFUL |
| § `AR1.ae_eq_process` | — | uniqueness of the stationary AR(1) solution | Among solutions bounded in probability (e.g. identically distributed), `|φ| < 1`. | FAITHFUL |
| § `HasEscapeMass` (def), `HasSpectralTailProcess.tendsto_clusterRatio_iff`, `.lt_candidateExtremalIndex_iff` | (new; cf. BS09 §4, KS20 §7.5) | cluster ratio → `ϑ − η`; `θ = ϑ − η` under `𝒜` | Exact identity under stationarity; the iff needs the spectral tail process, `uₙ, rₙ → ∞`. The `θ` statements additionally need `𝒜`, `nP(|X₀|>uₙ) → τ > 0`, `rₙ/n → 0`. | FAITHFUL |
| § `logEchoProcess_theta_lt_vartheta` | (new example) | stationary RV sequence with `θ = 1/2 < ϑ = 1` | Fully concrete: iid Pareto noise on `ℤ`, explicit lag `⌊log z⌋ + 1`. Conclusion bundles stationarity, `HasSpectralTailProcess` with `Θ = 1{t=0}`, `ϑ = 1`, `HasExtremalIndex … (1/2)`. | FAITHFUL |
| § `GCLTConverse.exists_isRegularlyVarying_of_tendsto`, `.isRegularlyVarying_truncSecondMoment_iff_absTail` | Feller XVII.5 Thm 2, Gnedenko–Kolmogorov §35 | domain of attraction of a stable law ⇒ `U ∈ RV_{2−α}` (and tail `RV_{−α}` for `α < 2`) | Symmetric version, plus the general version `exists_isRegularlyVarying_tailBalance_of_tendsto` (any centering `bₙ`): RV, tail balance and Lévy-measure limits derived. The limit law is not identified as stable in the converse. Symmetric iff with explicit `aₙ = normSeq μ n`. | FAITHFUL |
| § `pickandsDependence`, `IsSimpleMaxStable.hasUpperTailDependence`, `tendsto_pickandsDependenceEstimator` | Pickands (1981), dHF §6.1, Beirlant et al. §9.4, Coles §8.4 | `V = (1/x+1/y)A(y/(x+y))`; `λ_U = 2 − θ_E = 2(1 − A(1/2))`; Pickands estimator consistent | Convention `A(t) = ∫ max(t w₀, (1−t) w₁) dH` (mirror of some texts). Convexity of `A` only for laws with a spectral measure (converse spectral theorem not formalized). Estimator: known unit Fréchet margins, pairwise independent sample. Tail dependence of RV vectors in threshold form only. | FAITHFUL (stated scope) |
| § `logEchoProcess_phase_transition`, `conditionA_logEchoProcess`, `not_hasExtremalIndex_mixture` | (new examples) | block-length phase transition; `𝒜` for long blocks; mixture with `η = 0` but no `θ` | Concrete iid Pareto noise; the mixture uses an event independent of the noise with `0 < p < 1`. `𝒜` for the echo process only for `log n = o(rₙ)`, and shown to fail when `rₙ/log n` has a finite limit. | FAITHFUL |
| § `RandomIteration.exists_isStationary_of_kernel`, `tendstoLawCond_tailChain_iid`, `ARMAX.hasExtremalIndex_candidate` | Perfekt (1994), Janssen–Segers (2014), KS20 Ch. 14, EKM §8.1 | stationary Markov chains; tail chain; ARMAX `θ = ϑ = 1 − φ^α` | Chains as `X_{t+1} = f(X_t, V_t)`, ℕ-indexed and forward only (no two-sided chain, no ℤ-window stationarity). Tail-chain condition in random-function form `|f(x,v) − a(v)x| ≤ b(v)`; RV of `π` as a conditional-limit hypothesis. ARMAX `θ` and `ϑ` computed independently, not via the anticlustering theorem. | FAITHFUL (stated scope) |
| § `SkorokhodSpace`, `skorokhodEDist`, `SkorokhodSpace.instSeparableSpace`, `.measurableSpace_eq_comap_coeFn` | Billingsley §12, Thms 12.2, 12.5 | `D[0,1]` with `J₁`; separable; Borel = projection σ-algebra | Domain Mathlib's `unitInterval`, time changes as order isomorphisms of `I`, values in a (pseudo-e)metric space; `J₁` defined via `edist`. Thm 12.5 for second-countable `E` with all projections (not a dense subset of times). Completeness under `d°` not proved. | FAITHFUL (stated scope) |
| ‡ `Measure.TendstoVaguely` (def) | Resnick §3.4, Kallenberg §4.1 | `∫ f dμ_i → ∫ f dμ` for `f ∈ C_c` | Same, as a predicate (no topology on `Measure X`). Portmanteau lemmas assume regularity, which is automatic for locally finite measures on locally compact second-countable Hausdorff spaces. | FAITHFUL |
| ‡ `IsPoissonRandomMeasure` (def), `exists_isPoissonRandomMeasure` | Resnick §3.3, Kallenberg Thm 3.6 | independent Poisson counts on disjoint sets, `N(A) ~ Po(ν(A))` | Measurable `N : Ω → Measure E` for Mathlib's σ-algebra on measures; the joint law of counts on any finite disjoint family of finite-`ν` sets is the product of Poissons. Includes `N(A) = ∞` a.s. when `ν(A) = ∞` (field `ae_eq_top`, added after the third audit). Existence for every s-finite `ν`. | FAITHFUL |
| ‡ `TendstoInLawVaguely` (def), `tendstoInLawVaguely_sumDiracRange` | Resnick Prop 3.21, Kallenberg Thm 4.11 | `n μₙ → ν` vaguely ⇒ binomial process `⇒ PRM(ν)` | Convergence in law is defined through joint count laws on finite families of *disjoint* relatively compact `ν`-continuity sets (equivalent to convergence of fdd count laws, reduction from overlapping sets not formalized). No topology on the space of measures. | DIFFERS (fdd-count formulation); correct |
| ‡ `IsPoissonRandomMeasure.lintegral_exp_neg_lintegral`, `.map_eq` | Resnick Prop 3.6, Kallenberg Lemma 3.1 | Laplace functional; law determined by intensity | All measurable `f ≥ 0`, σ-finite `ν`, using `EReal.exp` so `exp(−∞) = 0`. Uniqueness from simple functions (not from `C_c^+` alone). | FAITHFUL |
| ‡ `tendsto_measureReal_sumDiracRange_timeSpace_eq` | Resnick Cor 4.19, EKM Thm 5.3.2 | exceedance point process `⇒ PRM(Leb ⊗ μ_G)` | Proved on disjoint exceedance intervals / time rectangles above a threshold `u` with `G(u) > 0`, not as convergence on the compactified space `(x_l, ∞]`. The order-statistic corollaries match the direct theorems exactly. | DIFFERS (interval classes); correct |
| `IsSubexponential` (def) | EKM Def 1.3.3 | `F` on `(0,∞)` with `F̄^{*2}(x)/F̄(x) → 2` | `μ(Iio 0) = 0`, `tail μ x > 0` for all `x` (the textbook `F(x) < 1`), and the limit `2`. Being a probability measure is a typeclass hypothesis on the theorems, not a field of the structure. | FAITHFUL |
| `IsSubexponential.of_isRegularlyVarying` | EKM Cor 1.3.2 | `F̄ ∈ RV_{−α}`, `α ≥ 0` ⇒ subexponential | No sign hypothesis on `α`; it is automatically `α ≥ 0`. | FAITHFUL |
| `tendsto_tail_sub_div` | EKM Lemma 1.3.5(a) | `F̄(x−y)/F̄(x) → 1` | Holds for every real `y`. | FAITHFUL |
| `tendsto_tail_convPow_div`, `tendsto_measure_sum_div_tail` | EKM Lemma 1.3.4 | `F̄^{*n}(x)/F̄(x) → n` | For `n ≥ 1`, in convolution form and in i.i.d.-sum form. | FAITHFUL |
| `tendsto_measure_max_div_tail`, `tendsto_measure_sum_div_measure_max` | EKM Lemma 1.3.1 | `P(max > x) ~ n F̄(x)`; `P(S_n > x) ~ P(M_n > x)` | Same. The max version needs only `tail > 0`. | FAITHFUL |
| ‡ `tendsto_map_convPow_sub_of_isRegularlyVarying_one` (and `'`) | Feller XVII.5 Thm 2, EKM Thm 2.2.8 (`α = 1`) | `bₙ = n E[X 1{|X| ≤ aₙ}]`, limit `exp(−C₁|t| − iβ(2/π) t log|t| + iκt)` | Same hypotheses as the `α ≠ 1` rows with `α = 1`; the truncation is `Icc (−aₙ) aₙ`. The limit is `exp(−(π/2)|t| + iβ(c t − t log|t|))` with `β = 2p−1`. This is the ST parametrization with `σ = π/2` (so `β(2/π)σ = β`) and a location shift `κ`, which depends on the centering. `c = stableLogConst = 1 − γ` is proved (`StableIntegral.stableLogConst_eq`). | FAITHFUL |
| ‡ `IsSubexponential.of_tendsto_tail_div`, `.convPow`, `tendsto_tail_conv_div_of_tendsto` | EKM Lemma A3.15 | tail-equivalent laws on `[0,∞)` stay subexponential; `F̄_{A*B} ~ (c₁+c₂)F̄` | Same, with `c > 0` (resp. `c₁, c₂ > 0`) and the new law on `[0,∞)`. | FAITHFUL |
| ‡ `IsSubexponential.tendsto_tail_compound_div` / `.compound` | EKM Thm A3.20 | `E(1+ε)^N < ∞` ⇒ `P(S_N > x) ~ E N · F̄(x)` | The law of `S_N` is `compound μ p = Σ pₙ μ^{*n}` (`Measure.sum`), with `p : ℕ → ℝ≥0`, `HasSum p 1`, `Summable (pₙ(1+ε)^n)`. This is the law of an independent random sum. | FAITHFUL |
| ‡ `pkRuin`, `IsSubexponential.tendsto_pkRuin_div`, `tendsto_pkRuin_div_mul_tail` | EKM Thm 1.3.6 (Embrechts–Veraverbeke) | `F_I ∈ S` ⇒ `ψ(u) ~ ρ⁻¹ F̄_I(u)` | `ψ` is *defined* by the Pollaczek–Khinchine formula `ρ/(1+ρ) Σ (1+ρ)^{-n} F̄_I^{*n}(u)`, which is correct, but the formula is not derived from the Cramér–Lundberg process. `integratedTail μ` is the density `F̄/m` on `(0,∞)`. The RV corollaries assume `F̄ ∈ RV_{−α}`, `α > 1` (so `m < ∞` is proved), but not `μ(Iio 0) = 0`, so `m = ∫_0^∞ F̄` is `E X⁺` (the mean claim size when claims are nonnegative). | DIFFERS (ruin probability defined via P–K); correct |
| ‡ `IsSubexponential.of_tail_eq_exp_neg_rpow` | EKM Ex. 1.4.3 | `F̄(x) = e^{−x^τ}`, `0 < τ < 1` ⇒ subexponential | Takes a measure with this tail as a hypothesis. Instantiated by `weibullTailLaw` (`isSubexponential_weibullTailLaw`). | FAITHFUL |
| ‡ `IsSubexponential.lognormal` | EKM Ex. 1.4.7 | `e^Z`, `Z ~ N(m, v)`, is subexponential | `lognormal m v = (gaussianReal m v).map exp`, `v ≠ 0`. | FAITHFUL |
| ‡ `IsSStar` (def), `IsSStar.isSubexponential`, `.isSubexponential_integratedTail` | Klüppelberg (1988) Thm 3.2 | `F ∈ 𝒮*` ⇒ `F ∈ 𝒮` and `F_I ∈ 𝒮` | `𝒮*`: law on `[0,∞)`, positive tail, `∫ F̄ < ∞`, `∫_0^x F̄(x−y)F̄(y)dy/F̄(x) → 2m`. Exact theorem numbers in EKM/FKZ not verified. | FAITHFUL |
| ‡ `IsSubexponential.of_convPow` | Embrechts–Goldie–Veraverbeke (1979) | `F^{*n} ∈ 𝒮` ⇒ `F ∈ 𝒮` | For laws on `[0,∞)`, `n ≥ 1`. | FAITHFUL |
| `kesten_bound` | EKM Lemma 1.3.5(c) | ∀ `ε > 0` ∃ `K` ∀ `n`, `x ≥ 0`: `F̄^{*n}(x) ≤ K(1+ε)^n F̄(x)` | Holds for all `n` and all real `x`. | FAITHFUL (slightly stronger) |

## Fourth audit (independent check of the § rows)

No critical problems. The hypotheses of the θ = ϑ chain were instantiated jointly on concrete
processes (moving maximum with Pareto noise, AR(1) with `φ = 1/2`); `ConditionA` is trivially true
when `rₙ = n` (ℕ division), but every consumer assumes `rₙ → ∞`, `rₙ/n → 0`; `ForwardAntiClusteringAt`
is trivial for bounded `rₙ`, likewise excluded. Findings: documentation overstatements (fixed in
README, RESEARCH and this file), and one moderate gap: the new extremal-index results conclude
`HasExtremalIndex` rather than `HasExtremalIndexStrict`, so uniqueness of `θ` is not available for
them in Lean (mathematically levels exist for regularly varying tails). Fix in progress.

## Third audit (independent check of the ‡ rows)

An independent adversarial pass over the ‡ rows (scratch-file instantiations, junk-value and
vacuity checks) found no critical problems. Findings and status:

1. **RESOLVED (moderate):** `IsPoissonRandomMeasure` now has the field `ae_eq_top`
   (`ν A = ∞ → N(A) = ∞` a.s.). Existence still holds for every s-finite intensity
   (`ae_sum_sumDiracRange_eq_top`), and for σ-finite `ν` the field follows from the others
   (`IsPoissonRandomMeasure.of_map_eq_pi`).
2. **RESOLVED (minor):** `HasExtremalIndexStrict` (= `HasExtremalIndex` plus `HasExceedanceLevels`,
   the LLR definition) is added, with uniqueness `HasExtremalIndex.unique` and the upgrade
   `HasExtremalIndex.strict_of_continuous` for continuous marginals. `HasExtremalIndex` itself is
   unchanged.
3. **DOCUMENTED (minor):** `Measure.TendstoVaguely` keeps its definition (adding local finiteness
   would not give uniqueness on non-second-countable spaces anyway); its docstring now warns about
   the degenerate case and each result states its regularity hypothesis.
4. **RESOLVED (for `ρ < 0`):** the far-tail Weissman theorems now have second-order versions that
   derive the Hill rate and the bias condition. The unverified "dHF Thm 4.3.1" citations were
   replaced by "dHF §4.3".
5. **Minor:** the ruin corollaries do not assume nonnegative claims (row updated).
6. **Minor:** `HasStableCharFun` has no parameter restrictions (row updated).
7. **Minor:** the GCLT is sufficiency only, and no skewed instance is exhibited (row updated).
8. **Cosmetic:** `IsSubexponential` allows an atom at `0` (EKM assumes `(0,∞)`); the von Mises
   theorems assume a derivative of `F` rather than a density; `IsStationary` and
   `HasShiftInvariantWindows` are trivial for non-measurable paths (all theorems assume
   measurability); Pickands uses dHF's indexing, one off EKM's.

## Status of first-audit findings

1. **`ExtremeValueDistr.domainOfAtraction` roles swapped: FIXED.** The definition is now
   `{F | ∃ As, ∀ x, ContinuousAt G.toCDF x → ((As n • F) x)^n → G.toCDF x}`, which is the
   textbook domain of attraction of `G`. `domainOfAtraction_nonempty` now uses the witness `F`
   from `G.isEVD`, so it means what it says.
2. **PBdH only Fréchet "⇒": LARGELY RESOLVED.** There are now `iff` versions for Fréchet and
   Weibull, a Gumbel version from an auxiliary function, and the unified "⇒" for every `ξ ∈ ℝ`
   (`exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV'`). What remains is new finding 2.
3. **Karamata/old POT assume `F` antitone on ℝ: RESOLVED for Karamata** by `tendsto_integral_Ioi_div_of_measurable` (measurable `F`, no monotonicity) and `_of_antitoneOn` (antitone on `[a,∞)`). The old POT theorems are unchanged. The new
   Balkema theorems take a `CumulativeDistributionFunction`, so `1 − F` is antitone
   automatically and no extra hypothesis is needed.
4. **`gpdSurvival` junk for `ξ < 0`: RESOLVED** by `gpdSurvival'`, which uses `max … 0`, and
   that is what the Weibull and unified statements use.

## New findings (second audit, ranked by severity)

No vacuous hypotheses, `⊥` filters, wrong quantifier orders, or harmful junk-value dependencies
were found. The suspicious points were checked in a scratch Lean file, and all checks compiled:
`upperEndpointFilter F` is `NeBot` for every `F`; `⨆ x ∈ Ici 0, x = 0` (the pitfall is real, but
it is avoided by the explicit bound); `orderStat ![3,1,2] 0 = 3`; `hill` on a sample with
`−1` uses `log(−1) = 0`; and the unified PBdH instantiates on `standardExponentialCDF` with
`ξ = 0`.

1. **LARGELY RESOLVED: the asymmetric GCLT.** For `0 < α < 1` (no centering) and `1 < α < 2`
   (centering `n E X`), `tendsto_map_convPow_of_isRegularlyVarying_of_lt_one` and
   `tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt` take tail balance
   `P(X > x)/P(|X| > x) → p` and give skewed limits with `HasStableCharFun`, which are linked to
   `IsStrictlyStable` / `IsStable` (`HasStableCharFun.isStrictlyStable`). `α = 1` is now proved too
   (`tendsto_map_convPow_sub_of_isRegularlyVarying_one`, `StableLaws/GeneralizedCLTOne.lean`).
   The classical value `c = 1 − γ` is proved (`stableLogConst_eq`). The closed forms `C_α = Γ(1−α)cos(πα/2)`
   (`= π/2` at `α = 1`) and `E_α = C_α tan(πα/2)` are now proved (`StableLaws/Constants.lean`),
   and the primed GCLT theorems state the textbook characteristic function. Original text: **(Minor: scope) The GCLT is only the
   symmetric case.** `tendsto_map_convPow_of_isRegularlyVarying`
   and the i.i.d. version require `μ.map neg = μ`. EKM Thm 2.2.8 / Feller XVII.5 cover general
   `F` (tail balance `p, q`, centering `b_n`, skewed stable limits). Docstrings say "symmetric
   case", so this is accurately labelled, but citing "[EKM, Theorem 2.2.8]" without
   qualification overstates it. The general `IsStable` notion is never linked to the domain of
   attraction.
2. **RESOLVED: PBdH converse.** `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival` is the
   full equivalence for every `ξ ∈ ℝ` with an arbitrary scale `β` (eventually positive along the
   endpoint filter), including Gumbel "uniform GPD ⇒ MDA(Λ)". Original text: **(Minor: scope)
   PBdH converse.** The unified theorem is "⇒" only. The "⇐" directions exist
   only for `ξ ≠ 0`, and only with the canonical scale `β(u) = u/α` or `(x_F−u)/α`; the textbook
   "⇐" allows an arbitrary `β`. There is no Gumbel "uniform GPD ⇒ MDA(Λ)". The
   `isInMDAGumbel_and_…` lemmas start from an auxiliary function, not from the GPD
   approximation.
3. **RESOLVED: the von Mises criterion for finite `x_F`.** `isInMDAGumbel_of_vonMises_nhdsLT`
   takes the hypotheses on `(z, x_F)` with limits along `𝓝[<] x_F`, plus `F t → 1` as
   `t ↑ x_F` (no atom at `x_F`; a counterexample without it is in the docstring). It derives
   `F < 1` on `(−∞, x_F)` and `F x_F = 1`. Original text: **(Minor: scope) The von Mises
   criterion is only for `x_F = ∞`.** EKM Thm 3.3.27 also allows a
   finite right endpoint (hypotheses on `(z, x_F)`, limit as `x ↑ x_F`). The `nhdsLT`
   auxiliary-function criterion covers finite `x_F`, but no von Mises version of it is given.
4. **(Cosmetic) `hill` on nonpositive order statistics** uses Mathlib's `Real.log x = log |x|`
   (and `log 0 = 0`) instead of being undefined. This does not affect `tendstoInMeasure_hill`,
   since `X_{(k+1)} → ∞` in probability. It would matter only if `hill` were used for finite-`n`
   statements about samples that are not positive.
5. **(Cosmetic) Junk values in auxiliary definitions.** `stableConst α` is `α · 0` outside
   `(0,2)` (a non-integrable Bochner integral), and `orderStat x j = 0` for `j ≥ n`. Neither is
   reached by a main theorem (`0 < α < 2` is assumed; `k(n) < n` eventually).
   `IsSymmStable.isStrictlyStable` does not assume `α ≤ 2`, but it is vacuous there because
   `IsSymmStable α c` is uninhabited for `α > 2`, `c > 0`.

## First-audit findings (original text, for reference)

1. **(Moderate; not used by any main theorem) `ExtremeValueDistr.domainOfAtraction` has its
   roles swapped.** `ExtremeValueDistribution.lean:56`. The docstring says "c.d.f.s `F` for
   which `G` is the limit of `Fⁿ` up to affine maps". The Lean definition is
   `{F | ∃ As, ∀ x, ContinuousAt F x → ((As n • G.toCDF) x)^n → F x}`, i.e. the set of limits
   of normalized maxima *of `G`*. The proof of `domainOfAtraction_nonempty` confirms the
   mismatch: it exhibits the degenerate `(diracProba 0).cdf` as a member, which is impossible
   for a genuine domain of attraction of a non-degenerate `G`. So the lemma is vacuous with
   respect to its intended meaning. The intended definition is
   `{F | ∃ As, ∀ x, ContinuousAt G.toCDF x → ((As n • F) x)^n → G.toCDF x}`. The working
   MDA notions (`IsInMDAFrechet`, `IsInMDAWeibull`, `IsInMDAGumbel`) are separate and correct.
   Recommend fixing or deleting this definition and its lemma.
2. **(Minor: scope, not correctness) Pickands–Balkema–de Haan is only the Fréchet "⇒" half.**
   The docstring "[EKM, Theorem 3.4.13]" should say it covers one direction with `ξ > 0` only,
   with the explicit choice `β(u) = u/α`. The statement is correct as written.
3. **(Minor) Karamata and the POT results assume `F` antitone on all of ℝ.** This is stronger
   than BGT's "locally bounded `f ∈ RV_{−α}`". It is natural for survival functions, but the
   theorems do not apply to general regularly varying functions.
4. **(Cosmetic) `gpdSurvival` for `ξ < 0`** returns `rpow`-junk beyond the upper endpoint
   instead of `0`. It is documented as intended for `ξ ≥ 0` and never used with `ξ < 0`.

No vacuous hypotheses, collapsing definitions, wrong quantifier orders, or harmful junk-value
dependencies were found in the audited main theorems. All the main definitions have
non-trivial inhabitants: the three standard EVDs, `IsRegularlyVarying.rpow_id`, and
`isSlowlyVarying_log`.
