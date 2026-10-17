# Faithfulness audit of main theorem statements

Scope: statements and definitions only (proofs are kernel-checked). Not audited:
`Statistics/*`, `DomainOfAttraction/Gumbel.lean`. No `sorry`/`axiom`/`admit` found in
`ExtremeValueTheory/`.

References: [EKM] Embrechts–Klüppelberg–Mikosch, *Modelling Extremal Events*;
[dHF] de Haan–Ferreira, *Extreme Value Theory*; [BGT] Bingham–Goldie–Teugels,
*Regular Variation*; [JM] Jessen–Mikosch (2006).

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
| `tendsto_measure_mul_div_measure` | Breiman (1965); JM Lemma 4.2(1) | `X ⫫ Y`, `P(X > x) ∈ RV_{−α}`, `Y ≥ 0`, `E Y^{α+ε} < ∞` ⇒ `P(XY > x)/P(X > x) → E Y^α` | Hypotheses are `IndepFun X Y P`, `Y ≥ 0` a.e., RV of `x ↦ (P{x < X}).toReal`, and integrability of `Y^{α+ε}`. The conclusion is `→ ∫ Y^α dP` (`0^α = 0` since `α > 0`, and `Y^α` is integrable). No sign condition on `X`, which matches the reference. | FAITHFUL |
| `gpdSurvival` (def) | EKM Def 3.4.1 | `Ḡ_{ξ,β}(x) = (1+ξx/β)^{−1/ξ}`, or `e^{−x/β}` if `ξ = 0` | Same formula, used only for `ξ ≥ 0`, `x ≥ 0`. For `ξ < 0` and `x > −β/ξ`, `rpow` of a negative base returns junk instead of `0`. This is documented and unused. | FAITHFUL (for `ξ ≥ 0`) |
| `tendstoUniformlyOn_excessSurvival` / `tendsto_sup_excessSurvival` | EKM Thm 3.4.13(b) (Pickands–Balkema–de Haan) | `F ∈ MDA(H_ξ)` ⇔ ∃ `β(u)`: `sup_{0<x<x_F−u} |F_u(x) − Ḡ_{ξ,β(u)}(x)| → 0` | Only the "⇒" direction, only the Fréchet case `ξ = 1/α > 0`, with explicit `β(u) = u/α`. It is stated after the change of variable `x = β(u) y`: `F(u + (u/α)y)/F(u) → Ḡ_{1/α,1}(y)` uniformly for `y ≥ 0`, which is equivalent to the textbook form. Assumes `F` antitone and in `RV_{−α}`, which by `isInMDAFrechet_iff` is exactly `MDA(Φ_α)` when `F = 1 − F_X`. | DIFFERS (one direction, `ξ > 0` only); correct as stated |
| `tendsto_meanExcess_div` | EKM §3.4 (mean excess of RV tails), via Karamata | `F̄ ∈ RV_{−α}`, `α > 1` ⇒ `e(u)/u → 1/(α−1)` | `meanExcess F u = (∫_{Ioi u} F)/F u`, which is `E[X − u | X > u]` when `F = F̄`. Assumes `F` antitone. | FAITHFUL |
| `IsSubexponential` (def) | EKM Def 1.3.3 | `F` on `(0,∞)` with `F̄^{*2}(x)/F̄(x) → 2` | `μ(Iio 0) = 0`, `tail μ x > 0` for all `x` (the textbook `F(x) < 1`), and the limit `2`. Being a probability measure is a typeclass hypothesis on the theorems, not a field of the structure. | FAITHFUL |
| `IsSubexponential.of_isRegularlyVarying` | EKM Cor 1.3.2 | `F̄ ∈ RV_{−α}`, `α ≥ 0` ⇒ subexponential | No sign hypothesis on `α`; it is automatically `α ≥ 0`. | FAITHFUL |
| `tendsto_tail_sub_div` | EKM Lemma 1.3.5(a) | `F̄(x−y)/F̄(x) → 1` | Holds for every real `y`. | FAITHFUL |
| `tendsto_tail_convPow_div`, `tendsto_measure_sum_div_tail` | EKM Lemma 1.3.4 | `F̄^{*n}(x)/F̄(x) → n` | For `n ≥ 1`, in convolution form and in i.i.d.-sum form. | FAITHFUL |
| `tendsto_measure_max_div_tail`, `tendsto_measure_sum_div_measure_max` | EKM Lemma 1.3.1 | `P(max > x) ~ n F̄(x)`; `P(S_n > x) ~ P(M_n > x)` | Same. The max version needs only `tail > 0`. | FAITHFUL |
| `kesten_bound` | EKM Lemma 1.3.5(c) | ∀ `ε > 0` ∃ `K` ∀ `n`, `x ≥ 0`: `F̄^{*n}(x) ≤ K(1+ε)^n F̄(x)` | Holds for all `n` and all real `x`. | FAITHFUL (slightly stronger) |

## Findings (ranked by severity)

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
