# Expert review guide: *Extreme Value Theory in Lean*

Repository: `https://github.com/unbalancedparentheses/lean-extremevaluetheory` (blueprint:
`https://unbalancedparentheses.github.io/lean-extremevaluetheory`). Snapshot: release `v0.9.0` and later
commits up to `ace7f0e`.

**What this guide covers.** Parts I and II were written at commit `9a3bfe3` (2026-10-18). Every Lean
name in them still exists (one, in C9, is now deprecated), but their line numbers can be off by a few
lines, so search by name. Part I-B (the answer to Bai–Kulik–Wang's question, mixing without `θ = ϑ`, the
short-runs warning) and entries S1 to S9 of Part III (return levels, Wald intervals, the delta method,
extremal-index estimators, likelihood, GARCH) were written at commit `99fe16a` (2026-11-04). Entries R14a
and S10 to S16 (GEV joint normality, GEV return levels without assumed normality, Wilks and profile
likelihood, Pickands and moment normality, nonparametric tail dependence, the critical scale, the textbook
form of the domains of attraction) were written at commit `ace7f0e` (2026-11-05), and R14, C9, C14, C26, S2,
S4 and S7 were corrected to match. All of these were written by reading each statement and its definitions
in the Lean source, not the docstrings.

**What it does not cover.** Results in the library with no entry here include the multivariate domain
of attraction as a theorem (`isMDAWith_iff`; S15 only uses its definition), subexponential laws and ruin
(`IsSubexponential.tendsto_tail_compound_div`, `tendsto_pkRuin_div_mul_tail`), the counterexamples in
`ExtremeValueTheory/Minimality/` (apart from those named below), the properties of Pickands dependence
(`convexOn_pickandsDependence`; S15 covers only its rank-based estimator), L-moments
(`lSkewness_gevCDF_hosking`), the tail-probability estimator (`tailProbEstimator`), the general stochastic
recurrence (`SRE.eq_stationaryLaw`), the norming constants of the other named laws (`tendsto_gammaCDF_pow`,
`tendsto_pow_norming_tailQuantile`), the unified von Mises criterion (`isInMDAGEV_of_vonMises`), and the
scale profile interval and the level-`1 − α` forms, which S12 only names. `FAITHFULNESS.md` lists those, and
the README's Limitations section lists known restrictions.

## What we are asking

Every proof in this library has been checked by the Lean proof assistant: if a statement compiles,
it follows from its hypotheses (the only axioms used are the standard `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`). **The proof checker cannot tell whether a
statement says what the textbook theorem says.** A hypothesis might be stronger than needed, a
definition might differ subtly from the standard one, or a "junk value" convention might make a
statement weaker than it looks. That check needs a human expert in extreme value theory, and that is
what this document asks for.

You do not need to read or run Lean. Each entry below gives:

- **(a) Literature**: the textbook or paper statement, with a reference.
- **(b) Lean, in math**: a literal translation of the formal statement (every hypothesis, including
  measurability and junk-value conventions), followed by the exact Lean name and file.
- **(c) Caveats**: known deviations, mostly from the project's own audit (`FAITHFULNESS.md`).
- **(d) Questions** for you.

Comments of the form "entry R6, question 2: ..." are the most useful. "Looks right" is also useful.

**Priority.** Parts I and I-B (the extremal index `θ` versus the candidate extremal index `ϑ`) contain
results that we did not find in the textbooks: an exact formula for the gap `ϑ − θ`, an explicit process
with `θ = 1/2 < ϑ = 1`, a block-length phase transition, and a proposed answer to a question of
Bai, Kulik and Wang. Those are the entries where an expert's check matters most, and where the literature
attributions were *not* all verified against the original papers. They are marked ★. Novelty is
provisional: `docs/NOVELTY.md` and `docs/NOVELTY2.md` record what was searched and what could not be read,
and we claim no priority.

S10 is also marked ★, for a different reason. It is classical, not new, but it is the theorem practitioners
rely on whenever they fit a GEV by maximum likelihood and quote a standard error, so an error in its
statement would matter most in practice.

**If you have limited time**, pick the line that fits you and skip the rest. The times are estimates, and a
partial answer is useful.

| Your time and interest | Read | Time |
|---|---|---|
| Dependence, very little time | R14, its first two questions | 30 minutes |
| Statistics, very little time | S10: the matrix, then its questions 1 to 3, with Prescott–Walden or Smith open | 45 minutes |
| Dependence | Part I-B: D1 to D7 (30 minutes), R14 and R14a with [BKW24, §1.4] open (about an hour), R15 and R16 (30 minutes) | about 2 hours |
| Statistics | S10 and S11 (1 hour), S12 (45 minutes), S13 and S14 (45 minutes) | about 2.5 hours |
| Dependence, thorough | Part I, R1 to R13, after Part I-B | 2 to 3 hours more |
| Statistics, thorough | S15 and S16 (45 minutes), S1 to S9 (about 2 hours), after the above | about 3 hours more |

Each caveat in Part III says how much its theorem assumes, and the summary table at the end collects them.
Part II is classical and is the lowest priority: S16 and C25, C26 are the entries to read if you want to
check how it connects to Part III.

References used throughout: [EKM] Embrechts–Klüppelberg–Mikosch, *Modelling Extremal Events*;
[dHF] de Haan–Ferreira, *Extreme Value Theory: An Introduction*; [BGT] Bingham–Goldie–Teugels,
*Regular Variation*; [LLR] Leadbetter–Lindgren–Rootzén, *Extremes and Related Properties of Random
Sequences and Processes*; [Feller] Feller, *An Introduction to Probability Theory*, Vol. II; [ST]
Samorodnitsky–Taqqu, *Stable Non-Gaussian Random Processes*; [BS09] Basrak–Segers, SPA 119 (2009);
[KS20] Kulik–Soulier, *Heavy-Tailed Time Series* (2020); [PS18] Planinić–Soulier, *The tail
process revisited*, Extremes 21 (2018); [BKW24] Bai–Kulik–Wang, arXiv:2409.17966; [BW]
Bai–Wang, arXiv:2110.07499; [Resnick] Resnick, *Extreme Values, Regular Variation and Point
Processes*; [Billingsley] *Convergence of Probability Measures*, 2nd ed.; [Coles] Coles, *An Introduction
to Statistical Modeling of Extreme Values* (2001); [vdV] van der Vaart, *Asymptotic Statistics*; [FS03]
Ferro–Segers, JRSS B 65 (2003); [BDM16] Buraczewski–Damek–Mikosch, *Stochastic Models with Power-Law Tails*.

---

## Primer: how to read a Lean statement (one page)

A Lean theorem has the shape `theorem name (h₁ : A) (h₂ : B) : C`, meaning *if `A` and `B` then
`C`*. Arrows `A → B → C` mean the same thing. Implicit arguments in braces `{X : ℕ → Ω → ℝ}` are
universally quantified.

| Lean | Mathematics |
|---|---|
| `Tendsto f atTop (𝓝 L)` | `f(x) → L` as `x → ∞` (or `n → ∞` if `f` is a sequence) |
| `Tendsto f atTop atTop` | `f(x) → ∞` |
| `Tendsto f (𝓝[<] a) (𝓝 L)` | `f(x) → L` as `x ↑ a`, `x < a` |
| `∀ᶠ x in atTop, p x` | `p(x)` holds for all sufficiently large `x` ("eventually") |
| `∀ᵐ ω ∂P, p ω` | `p` holds `P`-almost surely |
| `TendstoUniformlyOn F f l S` | `sup_{x ∈ S} |F(u, x) − f(x)| → 0` along `l` |
| `P.real A` or `(P A).toReal` | `P(A)` as a real number |
| `Measure.map f μ` | the law (image measure) of `f` under `μ` |
| `HasLaw Z μ P` | `Z` has law `μ` under `P` |
| `iIndepFun X P`, `X ⟂ᵢ[P] Y` | mutual independence of the family `X`; `X` independent of `Y` |
| `IdentDistrib (X i) (X 0) P P` | `X_i` has the same law as `X_0` |
| `TendstoInMeasure P Yₙ atTop Y` | `Yₙ → Y` in probability |
| `TendstoInDistribution Yₙ atTop Z …` | `Yₙ ⇒ Z` in distribution (weak convergence of laws) |
| `Tendsto (fun n ↦ ⟨law n, _⟩) atTop (𝓝 ν)` in `ProbabilityMeasure ℝ` | weak convergence of laws |
| `charFun μ t` | `∫ e^{itx} μ(dx)` |
| `convPow μ n` | `μ^{*n}`, the law of `X₁ + ⋯ + Xₙ` |
| `F.toStieltjesFunction x` (written `F(x)` below) | the c.d.f. `F` evaluated at `x` |
| `A • F` for `A : AffineIncrEquiv` | `(A • F)(x) = F(A⁻¹x)`: the c.d.f. of `A(X)` where `A(x) = ax + b`, `a > 0` |
| `∫⁻`, `ℝ≥0∞` | integral of a `[0, ∞]`-valued function, in `[0, ∞]` |
| `∃! x, p x` | there is a unique `x` with `p x` |
| `StrongDual ℝ E` | continuous linear functionals on `E` |

**Junk values.** Lean functions are total, so undefined expressions get a conventional value:

- `x / 0 = 0` and `0⁻¹ = 0`.
- `Real.log 0 = 0` and `Real.log x = log |x|` for `x < 0`.
- `x ^ y` (real power) for `x < 0` is a meaningless number; `0 ^ y = 0` for `y > 0`.
- `(n / r : ℕ)` is **integer division**, `⌊n/r⌋`, and `n / 0 = 0`.
- `⨆` (supremum) of a real family that is **not bounded above** is `0`. In `[0, ∞]` the supremum is
  the genuine one.
- In `[0, ∞]`, subtraction is truncated (`a − b = 0` if `b ≥ a`, so `∞ − ∞ = 0`), and
  `(∞).toReal = 0`.
- A Bochner integral `∫ f` of a non-integrable `f` is `0`; `∑'` of a non-summable series is `0`.
- `sInf ∅ = 0` in `ℝ`.

The rule of thumb for reviewers: a junk value in a **conclusion** makes a theorem harder to prove
(a junk `0` would usually make the claimed limit false), so it is rarely a problem. A junk value in a
**hypothesis** or **definition** can make a statement vacuous or change its meaning; those cases are
flagged below. The audits checked each main definition for non-trivial inhabitants (for instance,
the three EVD families are shown to be extreme value distributions, and the hypotheses of the
dependence theorems were instantiated together on concrete processes).

**Regular variation (used everywhere).** `IsRegularlyVarying f ρ` means: `f(x) > 0` eventually, and
`f(cx)/f(x) → c^ρ` as `x → ∞` for every `c > 0`. Measurability is **not** part of the definition
(BGT build it in); it is a separate hypothesis where needed. `IsSlowlyVarying` is `ρ = 0`.

---

# Part I ★ — Extremal index, tail process, and the gap `θ < ϑ` (new results)

All Part I files are in `ExtremeValueTheory/Dependence/`.

## I.0 Definitions to check first

These definitions are used by every Part I theorem. If one is off, everything downstream is off.

**D1. Stationarity.** Two forms are used.
`IsStationary X P` (`ForMathlib/Probability/Process/Stationary.lean`): for `X : ℕ → Ω → ℝ`, the
path `(X_{n+1})_{n≥0}` has the same law on `ℝ^ℕ` as `(X_n)_{n≥0}`.
`HasShiftInvariantWindows P X` (`TimeChange.lean:70`): for `X : ℤ → Ω → ℝ`, for every `h ∈ ℤ` and
every finite `S ⊂ ℤ`, `(X_{t+h})_{t∈S}` has the same law as `(X_t)_{t∈S}`. This is strict
stationarity of a two-sided sequence.

**D2. Spectral tail process** `HasSpectralTailProcess P X α Q Θ` (`TailProcess.lean:91`), with
`X = (X_t)_{t∈ℤ}` on `(Ω, P)` and `Θ = (Θ_t)_{t∈ℤ}` on another space `(Ω', Q)`:
1. `x ↦ P(|X_0| > x)` is regularly varying with index `−α`; and
2. for every finite `S ⊂ ℤ`, the conditional law of `(X_t/|X_0|)_{t∈S}` given `|X_0| > x` converges
   weakly, as `x → ∞`, to the law of `(Θ_t)_{t∈S}`. Weak convergence is tested on bounded continuous
   functions (`TendstoLawCond`, `TailProcess/Polar.lean:108`).

`HasTailProcess` (`:757`) is the analogue with `X_t/x` and limit `Y` with `|Y_0|` Pareto(`α`).

**D3. Candidate extremal index** `candidateExtremalIndex Q Θ α` (`TailProcess.lean:358`):

  `ϑ = ∫ [ (sup_{k≥0} |Θ_k|)^α − (sup_{k≥1} |Θ_k|)^α ] dQ`,

with the suprema taken in `[0, ∞]` and truncated subtraction (so the integrand is `0` when
`sup_{k≥1}|Θ_k| = ∞`). The value lies in `[0, ∞]`; theorems use `ϑ.toReal`, which is harmless
because `ϑ ≤ 1` is proved (`candidateExtremalIndex_le_one`). Only **forward** lags `k ≥ 0` appear.

**D4. Extremal index** `HasExtremalIndex X P θ` (`ExtremalIndex.lean:81`), for `X : ℕ → Ω → ℝ`:
`θ ∈ [0, 1]`, and for every `τ > 0` and **every** level sequence `(uₙ)` with
`n P(X_0 > uₙ) → τ`, we have `P(M_n ≤ uₙ) → e^{−θτ}`, where `M_n = max(X_0, …, X_{n−1})`
(`partialMax`; junk `M_0 = X_0`, irrelevant). If no level sequence exists for some `τ`, the condition
is vacuous there. `HasExtremalIndexStrict` adds existence of levels for every `τ` (the [LLR]
definition), which makes `θ` unique. Regularly varying tails always admit levels
(`hasExceedanceLevels_of_isRegularlyVarying`, `ThetaLeVartheta.lean:58`), and `*_strict` corollaries
exist for all the examples (`StrictExtremalIndex*.lean`). The θ–ϑ theorems are stated for `|X|`.

**D5. Anticlustering** `ForwardAntiClusteringAt P X u r` (`Anticlustering/Basic.lean:78`), with
`u : ℕ → ℝ` and block lengths `r : ℕ → ℕ`: for every `ε > 0` there is `m` such that eventually in
`n`,

  `P(|X_0| > uₙ, ∃ t ∈ [m, rₙ] with |X_t| > uₙ) ≤ ε P(|X_0| > uₙ)`.

This is the forward half of [BS09, Cond. 4.1] / [KS20, §6.1] at **one** level sequence, in ε–m form
instead of `lim_m limsup_n P(…| |X_0| > uₙ) = 0`. The two-sided version `AntiClusteringAt` and
`AntiClustering` (at every level `aₙx`) are also defined; the theorems only use the forward one.

**D6. Block condition** `ConditionA X P u r` (`Anticlustering.lean:134`):

  `P(M_n ≤ uₙ) − P(M_{rₙ} ≤ uₙ)^{⌊n/rₙ⌋} → 0`.

`⌊n/rₙ⌋` is ℕ-division. If `rₙ = n` the condition is trivially true; every theorem that uses it also
assumes `rₙ → ∞` and `rₙ/n → 0`.

**D7. Cluster ratio and late-return mass** (`Anticlustering.lean:296`, `ThetaGap.lean:85–110`). New
definitions.

  `CRₙ = P(max_{0≤t<rₙ} |X_t| > uₙ) / (rₙ P(|X_0| > uₙ))`.

For `m < k`, the *late-return set* is the event `{|X_0| > uₙ, |X_t| ≤ uₙ for 0 < t ≤ m, |X_t| > uₙ for
some m < t ≤ k}`. The *late return at lag m* is

  `εₙ(m) = (1/rₙ) Σ_{k<rₙ} P(late-return set(m, k)) / P(|X_0| > uₙ) = E[(1 − Tₙ/rₙ)⁺ ; Tₙ > m | |X_0| > uₙ]`,

with `Tₙ` the first return time above `uₙ` after time 0. `HasLateReturnMass P X u r η` means
`η = lim_{m→∞} lim_{n→∞} εₙ(m)`, in the δ–m form: for every `δ > 0` there is `m₀` such that for
all `m ≥ m₀`, eventually `|εₙ(m) − η| ≤ δ`. In words, `η` is the conditional mass of returns
above the threshold within the block at lags that grow with the level.

**Questions on the definitions.**
1. D2 tests weak convergence on all finite windows `S ⊂ ℤ` with conditioning on `|X_0| > x` for real
   `x → ∞`. Is this the standard notion of "jointly regularly varying with spectral tail process"
   ([BS09, Thm 2.1], [KS20, Ch. 5])? Is anything lost by not also requiring a tail process for
   `X_t/x`? (Their equivalence is entry R1.)
2. D3 uses only forward lags and the `[0, ∞]` convention. Is this the `ϑ` of [KS20, (5.6.5)] / [PS18]
   (not the backward or two-sided variant)?
3. D4 quantifies over *all* level sequences with `n P(X_0 > uₙ) → τ`. Is that the [LLR, §3.7]
   definition, or is it the "for some `uₙ(τ)`" version? (The two agree for continuous marginals.)
4. D7 is new. Is there an existing notion in the literature that `η` coincides with (for example,
   a quantity in [BKW24] or in Smith's 1988 counterexample)?

## R1. Polar decomposition of the tail process

**(a) Literature.** [BS09, Thm 2.1]; [KS20, Ch. 5]. For a random variable `Z ≥ 0` (here `|X_0|`)
and a vector `V`, the tail process exists iff the spectral tail process exists. Then
`Y = |Y_0| Θ` with `|Y_0|` Pareto(`α`) independent of `Θ`.

**(b) Lean, in math.** Let `α > 0`, `Z : Ω → ℝ` and `V : Ω → E` measurable, with `E` a separable
normed space with its Borel σ-algebra. The following are equivalent:
1. `x ↦ P(Z > x)` is regularly varying with index `−α`, and there is a probability measure `μ` on
   `E` with: the law of `Z^{−1} V` given `Z > x` converges weakly to `μ` as `x → ∞`.
2. There is a probability measure `ν` on `ℝ × E` whose first marginal is Pareto(`α`), i.e.
   `ν₁(y, ∞) = y^{−α}` for `y ≥ 1`, with: the law of `(Z/x, x^{−1}V)` given `Z > x` converges weakly
   to `ν`.

Lean: `ExtremeValueTheory.polar_iff`, `Dependence/TailProcess/Polar.lean:698`. (`HasSpectralTailProcess.hasTailProcess`
applies this to windows of a time series.)

**(c) Caveats.** None in the audit. The [BS09] erratum (SPA 121 (2011)) was **not** consulted;
statements were compared with [KS20] and [PS18] instead. Independence of `|Y_0|` and `Θ` is proved
separately, not in this iff.

**(d) Questions.**
1. Is the content of the [BS09] erratum relevant to Theorem 2.1, and if so, does the statement
   above avoid it?

## R2. Time-change formula

**(a) Literature.** [BS09, Thm 3.1(iii)]; [KS20, Thm 5.3.1]. For a stationary regularly varying
series, for measurable `g ≥ 0` and `i ∈ ℤ`:
`E[g(Θ_{·−i}) 1{Θ_{−i} ≠ 0}] = E[g(Θ_·/|Θ_i|) |Θ_i|^α]`.

**(b) Lean, in math.** Let `α > 0`; `X_t` and `Θ_t` measurable for every `t`; `X` stationary (D1);
`X` has spectral tail process `Θ` with index `α` (D2). Then for every `i ∈ ℤ`, finite `S ⊂ ℤ`, and
measurable `g : ℝ^S → [0, ∞]`:

  `∫ 1{Θ_{−i} ≠ 0} g((Θ_{t−i})_{t∈S}) dQ = ∫ g((Θ_t/|Θ_i|)_{t∈S}) |Θ_i|^α dQ`.

On the right, when `Θ_i = 0` the factor `|Θ_i|^α = 0` kills the junk value of `Θ_t/0 = 0`.

Lean: `ExtremeValueTheory.HasSpectralTailProcess.lintegral_timeChange`,
`Dependence/TimeChange.lean:471`.

**(c) Caveats.** Finite windows only (equivalent to the path version by a monotone class argument,
which is not stated as such).

**(d) Questions.**
1. Is finite-window `g` enough for every downstream use you know of (for instance the identities
   for `ϑ` in R3)?

## R3. Identities for `ϑ`; `ϑ > 0` when `Θ_t → 0`

**(a) Literature.** [KS20, §5.6]; [PS18, §4]; [BS09, §4]. `ϑ = P(sup_{k≥1} |Y_k| ≤ 1)`, `ϑ ≤ 1`,
and `ϑ > 0` when `Θ_t → 0`.

**(b) Lean, in math.**
- `candidateExtremalIndex_eq_measure` (`TailProcess.lean:461`): if `α > 0`, every `Θ_t` is
  measurable and `|Θ_0| = 1` a.s., then `ϑ = (Pareto(α) ⊗ Q){(y, ω') : y |Θ_{k+1}(ω')| ≤ 1 for all
  k ≥ 0}`, i.e. `ϑ = P(sup_{k≥1} |Y_k| ≤ 1)` with `Y = R Θ`, `R` Pareto(α) independent of `Θ`. No
  stationarity and no decay of `Θ` is assumed (thanks to the `[0, ∞]` conventions of D3).
- `HasSpectralTailProcess.candidateExtremalIndex_pos` (`TimeChange.lean:595`): under the R2
  hypotheses, if `Θ_k → 0` a.s. as `k → ∞` (forward only), then `ϑ > 0`.
- `HasSpectralTailProcess.candidateExtremalIndex_eq_measure_backward` (`BackwardTailProcess.lean:452`):
  `ϑ = P(sup_{k≤−1} |Y_k| ≤ 1)` under stationarity and `Θ_t → 0` in both directions.

**(c) Caveats.** The `[0, ∞]` convention (D3) means the first identity holds unconditionally; when
`sup_{k≥1}|Θ_k| = ∞` with positive probability, `ϑ` is the convention's value, not a textbook value.

**(d) Questions.**
1. [RESEARCH.md] attributes "`ϑ > 0` / equivalent formulas for `ϑ`" to [PS18, Lemma 4.1] but notes
   this was not checked against the paper. Is that attribution correct?

## R4. Cluster ratio → `ϑ` under forward anticlustering at one level ★

**(a) Literature.** [BS09, Prop. 4.2]; [KS20, §7.5]: under anticlustering `AC(rₙ)` (and in the
literature usually mixing and `rₙ/n → 0`),
`P(max_{0≤t<rₙ} |X_t| > aₙx) / (rₙ P(|X_0| > aₙx)) → ϑ`.

**(b) Lean, in math.** Let `α > 0`; `X_t`, `Θ_t` measurable; `X` stationary; `X` has spectral tail
process `Θ`; `uₙ → ∞`; `rₙ → ∞` (`rₙ ∈ ℕ`); and forward anticlustering at `(uₙ, rₙ)` (D5). Then

  `P(max_{0≤t<rₙ} |X_t| > uₙ) / (rₙ P(|X_0| > uₙ)) → ϑ`.

Lean: `ExtremeValueTheory.HasSpectralTailProcess.tendsto_blockRatio`,
`Dependence/Anticlustering/BlockRatio.lean:178`.

**(c) Caveats.** The project highlights the *absence* of hypotheses: no mixing, no `rₙ/n → 0`, no
`rₙ P(|X_0| > uₙ) → 0`, anticlustering only forward and at a single level sequence. Also proved:
forward anticlustering at one level forces `Θ_t → 0` (without stationarity).

**(d) Questions.**
1. Is it known that the block-ratio limit needs only forward anticlustering at one level, with no
   mixing and no `rₙ/n → 0`? If so, where (for example in [KS20, Ch. 6–7])?
2. Does forward anticlustering at `(uₙ, rₙ)` imply `rₙ P(|X_0| > uₙ) → 0` for stationary sequences
   (it does for iid sequences)? If not, is the statement still the one you would expect in that regime?

## R5. `θ = ϑ` under anticlustering and condition `𝒜` ★

**(a) Literature.** [BS09, §4]; [KS20, §7.5]: under `AC(rₙ)` and the block condition `𝒜(aₙ)`
(implied by suitable mixing), the extremal index of `|X|` exists and equals `ϑ`.

**(b) Lean, in math.** Let `α > 0`; `X_t`, `Θ_t` measurable; `X` stationary; `X` has spectral tail
process `Θ`; `rₙ → ∞`, `rₙ/n → 0`. Assume: for every `τ > 0` and every level sequence `uₙ` with
`n P(|X_0| > uₙ) → τ`, both forward anticlustering at `(uₙ, rₙ)` and `ConditionA` for `|X|` at
`(uₙ, rₙ)` hold. Then `(|X_n|)_{n≥0}` has extremal index `ϑ` (D4).

Lean: `ExtremeValueTheory.HasSpectralTailProcess.hasExtremalIndex_abs`,
`Dependence/Anticlustering.lean:225`.

**(c) Caveats.** `𝒜` is a hypothesis here. It is derived from α-mixing at a rate (R12) and from
m-dependence (R11). The block length `rₙ` is the same for all `τ`. The conclusion is about `|X|`,
not `X`.

**(d) Questions.**
1. In the literature `AC` and `𝒜` are imposed at `uₙ = aₙ x` for `x > 0`, with `n P(|X_0| > aₙ) → 1`.
   Here they are imposed for all sequences with `n P(|X_0| > uₙ) → τ`. Are these equivalent in
   strength, or is one strictly stronger?

## R6. `θ ≤ ϑ` with no anticlustering, mixing or block condition ★

**(a) Literature.** [KS20, Lemma 7.5.4], as described by [BKW24] ("always holds", stated there for
`ℝ₊`-valued series). The exact hypotheses of [KS20] were **not** checked against the book.

**(b) Lean, in math.** Let `α > 0`; `X_t`, `Θ_t` measurable; `X` stationary (D1); `X` has spectral
tail process `Θ` (D2). If `(|X_n|)_{n≥0}` has extremal index `θ` (D4), then `θ ≤ ϑ`.

Lean: `ExtremeValueTheory.HasSpectralTailProcess.le_candidateExtremalIndex'`,
`Dependence/ThetaLeVartheta.lean:267`.

**(c) Caveats.** An earlier version, `le_candidateExtremalIndex` (no prime), additionally assumed `𝒜`
along one level sequence, `rₙ → ∞`, `rₙ/n → 0`. The primed version removes all of them; the level
sequences it needs come from regular variation.

**(d) Questions.**
1. Does [KS20, Lemma 7.5.4] state `θ ≤ ϑ` under exactly these hypotheses (stationarity, regular
   variation with a spectral tail process, existence of `θ`)? Or does it assume more (for example
   `𝒜`), in which case the Lean version is a strengthening?
2. Is this statement for `|X|` (rather than `X`, or `X⁺`) the form you would use?

## R7. Gap formula: cluster ratio → `L` iff late-return mass `= ϑ − L` ★ (new)

**(a) Literature.** None. New result. Related to [BS09, §4], [KS20, §7.5], and to the question in
[BKW24, §1] of when `θ < ϑ` happens.

**(b) Lean, in math.** Let `α > 0`; `X_t`, `Θ_t` measurable; `X` stationary; `X` has spectral tail
process `Θ`; `uₙ → ∞`; `rₙ → ∞`. Then for every real `L`:

  `CRₙ → L`  ⟺  `X` has late-return mass `η = ϑ − L` at `(uₙ, rₙ)` (D7).

Lean: `ExtremeValueTheory.HasSpectralTailProcess.tendsto_clusterRatio_iff`,
`Dependence/ThetaGap.lean:311`.

**(c) Caveats.** None found by the audits. There are no anticlustering, mixing, `rₙ/n` or
`rₙ P(|X_0| > uₙ)` hypotheses. Combined with R4, forward anticlustering implies `η = 0`. The
converse fails: the mixture process (R10) has `η = 0` but no anticlustering.

**(d) Questions.**
1. Is this identity known, perhaps in another form (for example via the "conditional
   anticlustering" or "cluster size" decompositions in [KS20, Ch. 6–7], or in [BKW24])?
2. Is `η`, defined by the weight `(1 − Tₙ/rₙ)⁺`, a natural quantity to you? Would a different
   normalization be more standard?

## R8. `θ < ϑ` iff the late-return mass is positive, and then `θ = ϑ − η` ★ (new)

**(a) Literature.** None; new.

**(b) Lean, in math.** Let `α > 0`; `X_t`, `Θ_t` measurable; `X` stationary; `X` has spectral tail
process `Θ`; `(|X_n|)` has extremal index `θ`; `uₙ` with `n P(|X_0| > uₙ) → τ` and `τ > 0`;
`rₙ → ∞`, `rₙ/n → 0`; and `ConditionA` for `|X|` at `(uₙ, rₙ)`. Then

  `θ < ϑ`  ⟺  there is `η > 0` such that `X` has late-return mass `η` at `(uₙ, rₙ)` and `θ = ϑ − η`.

Lean: `ExtremeValueTheory.HasSpectralTailProcess.lt_candidateExtremalIndex_iff`,
`Dependence/ThetaGap.lean:475`.

**(c) Caveats.** `𝒜` is needed here (it links the cluster ratio to `θ`), at one level sequence only.

**(d) Questions.**
1. Is "`θ = ϑ − η` under `𝒜` alone" consistent with the known examples of `θ < ϑ` (Bai–Wang [BW];
   Smith 1988)? Could you suggest one to test it on?

## R9. The echo process: `θ = 1/2 < ϑ = 1` with `Θ_t → 0` ★ (new example)

**(a) Literature.** None; new. Compare with the stable-regenerative model of [BW], which also has
`θ < ϑ`. Novelty was **not** checked against the literature.

**(b) Lean, in math.** Let `α > 0`, and let `(Z_t)_{t∈ℤ}` be iid with `Z_t ≥ 0` everywhere and
`Z_t ~ Pareto(α)` (`P(Z_t > z) = z^{−α}` for `z ≥ 1`), each `Z_t` measurable. Let
`L(z) = ⌊log z⌋₊ + 1` and define the **echo process**

  `X_t = max( Z_t, sup{ Z_s : s < t, s + L(Z_s) = t } )`:

every innovation appears at its own time and once more, `L(Z_s)` steps later. Then all of the
following hold:
1. `X` is stationary (D1);
2. `X` has spectral tail process `Θ_t = 1{t = 0}` (on a one-point space) with index `α`;
3. `ϑ = 1`;
4. `(X_n)_{n≥0}` has extremal index `θ = 1/2`.

Lean: `ExtremeValueTheory.logEchoProcess_theta_lt_vartheta`, `Dependence/EchoProcess.lean:400`.
The strict version (levels exist, `θ` unique) is `logEchoProcess_hasExtremalIndex_strict`, and
`logEchoProcess_not_hasExtremalIndex_one` confirms that `θ = 1` fails (`StrictExtremalIndexAll.lean`).

**(c) Caveats.** The supremum in the definition is a real `⨆` over `j ∈ ℕ`, which would be the junk
value `0` if infinitely many echoes landed at time `t`. That event is null by Borel–Cantelli, and this
is proved (`EchoProcess/Basic.lean:171`). `Θ_t = 1{t=0}` gives `|Y_t| → 0`. So **`|Y_t| → 0` does not imply
`θ = ϑ`**. An earlier reading of [PS18, Lemma 4.1] that suggested otherwise was withdrawn
(RESEARCH.md). Anticlustering fails for this process (`not_forwardAntiClusteringAt_echoProcess`).
The process is a stationary factor of iid noise, and it is β-mixing, geometrically for this lag (R15).
`𝒜` holds for long blocks (R10).

**(d) Questions.**
1. Is this example (or an equivalent one) already in the literature? It seems much simpler than
   [BW].
2. Is this a convincing counterexample to "`|Y_t| → 0` ⇒ `θ = ϑ`"? Is that implication claimed or
   suggested anywhere in the literature?
3. Strong (α- and β-) mixing has since been proved; see R15. Is that enough to show that the gap is not
   an artifact of weak dependence assumptions?

## R10. Echo phase transition, `𝒜` for long blocks, and the mixture ★ (new)

**(a) Literature.** None; new. Motivated by the open question in [BKW24, §1]: does the mesoscopic
phase transition of their model occur for other regularly varying processes?

**(b) Lean, in math.**

*Phase transition* (`logEchoProcess_phase_transition`, `Dependence/EchoPhaseTransition.lean:791`).
Same echo process and hypotheses as R9. Let `uₙ` satisfy `n P(X_0 > uₙ) → τ` with `τ > 0`, and let
`rₙ ∈ ℕ` be arbitrary. Then:
1. if `rₙ → ∞` and `rₙ/log n → 0`: `CRₙ → 1` and the late-return mass is `0`;
2. if `rₙ/log n → c` with `c > 0`: `CRₙ → (1 + min(1/(cα), 1))/2` and the late-return mass is
   `(1 − min(1/(cα), 1))/2`;
3. if `rₙ → ∞`, `rₙ/n → 0` and `log n / rₙ → 0`: `CRₙ → 1/2` and the late-return mass is `1/2`.

The transition is continuous, with a kink at `c = 1/α`, the scale `(1/α) log n` of the echo lag at
level `uₙ`.

*Condition `𝒜`* (`conditionA_logEchoProcess`, `Dependence/EchoConditionA.lean:367`) holds for the
echo process when `rₙ → ∞`, `rₙ/n → 0` and `log n = o(rₙ)`. By the audit, it fails when `rₙ/log n`
has a finite limit.

*Mixture* (`not_hasExtremalIndex_mixture`, `Dependence/MixtureProcess.lean:218`). Let `(Z_t)` be iid
Pareto(`α`), and let `E` be an event independent of `σ(Z_t : t ∈ ℤ)` with `0 < P(E) < 1`. Put
`X_t = Z_0` on `E` and `X_t = Z_t` off `E`. Then **no** `θ ∈ ℝ` is an extremal index of `X` (D4).
Other theorems in the same file show that `X` is stationary, has a spectral tail process with
`ϑ = 1 − P(E)`, has late-return mass `0` (so `CRₙ → ϑ`), and that anticlustering and `𝒜` fail.

**(c) Caveats.** In the phase transition, the `rₙ/log n` with `n = 0` is junk (`log 0 = 0`),
irrelevant for limits. Case 2 does not assume `rₙ/n → 0` (it follows).

**(d) Questions.**
1. Is this a genuine instance of the phase transition asked about in [BKW24, §1]? Does it answer
   their question, or is their question about a different scale (for example
   `log dₙ / log n → ρ`)?
2. The mixture shows that `η = 0` is strictly weaker than anticlustering and does not imply that `θ`
   exists. Is this already folklore?

## R11. m-dependent sequences: `θ = ϑ`

**(a) Literature.** Standard; for example [KS20, Ch. 7]; [EKM, §8.1] for moving averages.

**(b) Lean, in math.** Let `α > 0`; `X_t`, `Θ_t` measurable; `X` stationary; `X` has spectral tail
process `Θ`; `(X_n)_{n≥0}` is `m`-dependent for some `m`, meaning that `σ(X_t : t ≤ s)` and
`σ(X_t : t ≥ s + m + 1)` are independent for every `s`. Then `(|X_n|)_{n≥0}` has extremal index `ϑ`.

Lean: `ExtremeValueTheory.HasSpectralTailProcess.hasExtremalIndex_of_isMDependent`,
`Dependence/MDependent.lean:210`.

**(c) Caveats.** None. Used to recover the moving maximum (`θ = 1/2`) and finite moving averages
(`θ = max ψ_j^α / Σ ψ_j^α`, `ψ ≥ 0`, nonnegative noise).

**(d) Questions.** None specific.

## R12. `𝒜` from α-mixing at a rate

**(a) Literature.** [BS09, §4]; [KS20, §7.5]; the Leadbetter/Davis–Hsing block argument.

**(b) Lean, in math.** Let `X : ℕ → Ω → ℝ` be stationary and measurable; `rₙ → ∞`, `rₙ/n → 0`,
`lₙ/rₙ → 0`, `(n/rₙ) α(lₙ) → 0`, where `α(h) = sup_s α(σ(X_t : t ≤ s), σ(X_t : t ≥ s + h))` is the
strong mixing coefficient. If `n P(X_0 > uₙ) ≤ C` eventually, then `ConditionA X P u r` holds.

Lean: `ExtremeValueTheory.conditionA_of_alphaMixing`, `Dependence/Mixing.lean:165`.

**(c) Caveats.** Nothing for β-mixing beyond `α ≤ β`.

**(d) Questions.**
1. Is `(n/rₙ) α(lₙ) → 0` the usual rate in this argument?

## R13. Infinite moving averages and AR(1)

**(a) Literature.** Davis–Resnick (1985); [KS20, Ch. 15]; [EKM, §8.1]. For
`X_t = Σ_j ψ_j Z_{t−j}` with regularly varying noise, `θ = max_j ψ_j^α / Σ_j ψ_j^α` (nonnegative
coefficients). For AR(1) with `0 < φ < 1`, `θ = 1 − φ^α`.

**(b) Lean, in math.**
- `InfiniteMovingAverage.hasSpectralTailProcess_and_hasExtremalIndex_of_summable_rpow`
  (`Dependence/InfiniteMovingAverageTailProcess.lean:901`). Let `(Z_i)_{i∈ℤ}` be iid, measurable,
  `Z_i ≥ 0` everywhere, with `P(Z_0 > x)` regularly varying with index `−α`. Let `0 < δ < α`,
  `δ < 1`, `ψ_j ≥ 0`, `Σ_j ψ_j^δ < ∞`, and `ψ_j > 0` for some `j`. Put `X_t = Σ_{j≥0} ψ_j Z_{t−j}`.
  Then `X` has spectral tail process `Θ_t = ψ_{J+t}/ψ_J`, where `P(J = j) = ψ_j^α / Σ_i ψ_i^α`, and
  `(X_n)_{n≥0}` has extremal index `ϑ` (which equals `sup ψ^α / Σ ψ^α`).
- `AR1.hasExtremalIndex_of_pos` (`Dependence/AR1.lean:106`). The same noise hypotheses with `α > 0`
  and `0 < φ < 1`: the stationary AR(1) process `X_t = Σ_j φ^j Z_{t−j}` has extremal index `1 − φ^α`.

**(c) Caveats.** `X_t` is a `∑'`, which would be junk `0` where the series diverges (an a.s. null
event, proved). The condition `Σψ^δ < ∞` with `δ < min(α, 1)` is slightly stronger than the optimal
`Σψ < ∞` when `α > 1`. Nonnegative coefficients and noise only. The name suffix `_of_lt_one` is
inherited and refers to `δ < 1`.

**(d) Questions.**
1. Is the restriction to nonnegative coefficients and noise a significant loss for you, or the main
   case of interest?

---

# Part I-B ★ — The answer to Bai–Kulik–Wang's question, mixing, and short runs (new results)

Please read this part first if you have limited time. It uses the definitions D1 to D7 of Part I. Files
are in `ExtremeValueTheory/Dependence/` unless stated otherwise. Novelty here is provisional, and no
priority is claimed: `docs/NOVELTY2.md` records the search, and lists what could not be read (the
Kulik–Soulier book, the full text of Weissman–Cohen 1995, the published journal version of [BKW24]).

## I-B.0 Definitions

**D8. Echo process and its hypotheses.** `echoProcess L Z` (`EchoProcess/Basic.lean:76`), for a lag `L :
ℝ → ℕ` and `(Z_t)_{t∈ℤ}`:

  `X_t = max( Z_t, sup_{j≥0} e_{t,j} )`, with `e_{t,j} = Z_{t−j−1}` if `L(Z_{t−j−1}) = j + 1`, else `0`.

The supremum is a real `⨆`, which would be the junk value `0` if unbounded; that event is null (R9).
*Hypotheses (E):* `α > 0`; each `Z_t` measurable; `(Z_t)` mutually independent; each `Z_t` has law
Pareto(`α`) (`P(Z_t > z) = z^{−α}` for `z ≥ 1`); and `Z_t(ω) ≥ 0` for **every** `t` and `ω`, not only
almost surely. Two lags are used: `logLag z = ⌊log z⌋₊ + 1` (`EchoProcess.lean:273`) and `powLag γ z =
⌊z^γ⌋₊ + 1` (`EchoPowerLag.lean:303`). In all theorems below `X ≥ 0`, so `|X| = X`.

**D9. Two-sided anticlustering.** `AntiClusteringAt P X u r` (`Anticlustering/Basic.lean:71`): for every
`ε > 0` there is `m` such that eventually in `n`,

  `P(|X_0| > uₙ, ∃ t ∈ ℤ with m ≤ |t| ≤ rₙ and |X_t| > uₙ) ≤ ε P(|X_0| > uₙ)`.

`AntiClustering P X a r` (`Anticlustering/Basic.lean:87`): `AntiClusteringAt` holds along the level
sequence `(aₙ x)ₙ` for **every** `x > 0`. The definition places no condition on `a` or `r`. The
conditioning level and the exceedance level are the same (see R14, caveat 1). `ForwardAntiClusteringAt`
is D5.

**D10. Critical shape.** `echoShape β κ = (β min(κ, 1) − min(κ, 1)^β) / (β − 1)`
(`EchoPowerLag.lean:103`), written `φ_β(κ)`. For `β > 1`: `φ_β(0) = 0`, `φ_β` is continuous, `φ_β(κ) < 1`
for `0 ≤ κ < 1`, and `φ_β(κ) = 1` for `κ ≥ 1`. By direct integration it equals `E[min(κV, 1)]` for `V`
Pareto(`β`).

**D11. β-mixing.** `betaMixingCoeff m₁ m₂ P` (`ForMathlib/Probability/Process/Mixing.lean:85`) is the
supremum over finite measurable partitions `(Aᵢ)` of `m₁` and `(Bⱼ)` of `m₂` of `½ Σᵢ Σⱼ |P(Aᵢ ∩ Bⱼ) −
P(Aᵢ)P(Bⱼ)|`. For `X : ℕ → Ω → ℝ`, `betaMixing X P h = sup_{s∈ℕ} β(σ(X_t : t ≤ s), σ(X_t : t ≥ s + h))`
(`Mixing.lean:244`). The index set is `ℕ`, so the past starts at time `0`. `IsBetaMixing X P` means
`β(h) → 0` (`Mixing.lean:252`), with no rate.

**D12. Blocks and runs estimators** (`ExtremeValueTheory/Statistics/ExtremalIndexEstimators.lean:178,
181`), for `X : ℕ → Ω → ℝ`, sample size `n`, block or run length `r` and threshold `u`:

  `blocksEstimator X n r u = #{j < ⌊n/r⌋ : max_{jr ≤ t < jr + r} X_t > u} / #{i < n : X_i > u}`,

  `runsEstimator X n r u = #{i < n − r : X_i > u, X_{i+1} ≤ u, …, X_{i+r} ≤ u} / #{i < n : X_i > u}`.

`n − r` is truncated subtraction, `⌊n/r⌋` is ℕ-division, and `0/0 = 0` when there is no exceedance.

## R14. Anticlustering exactly for block lengths below `n^{ρ₀}` ★ (proposed answer to [BKW24, §1.4])

**(a) Literature.** [BKW24], arXiv:2409.17966v2, §1.4 "Comments", p. 7, verbatim:

> "It would be very interesting to know whether such a phase transition exists for any other regularly
> varying stochastic processes. It would also be interesting to know whether there are models such that
> the anticlustering condition holds with lim_{n→∞} log d_n / log n = ρ for ρ up to certain ρ₀ < 1 only."

There, `b_n` satisfies `n P(X_0 > b_n) → 1`, the processes are nonnegative, and `AC(d_n, b_n)` reads:
for all `x, y > 0`, `lim_{m→∞} limsup_n P(max_{m≤|j|≤d_n} X_j > b_n x | X_0 > b_n y) = 0`. As read in
`docs/NOVELTY2.md`, their own model has `AC` for `d_n = o(log n)` and failure for `d_n ≫ n^ε`, and they
contrast it with iid and most weakly dependent models, where `AC` holds for every `d_n = o(n)`. The
question as quoted comes from the arXiv version; the published version (AAP 36(4), 2026) could not be
checked.

**(b) Lean, in math.** Throughout: hypotheses (E) of D8, `0 < γ < α`, and `X = echoProcess (powLag γ)
Z`, so the lag is `⌊z^γ⌋₊ + 1`. `CRₙ` and the late-return mass are as in D7.

*The equivalence.* Let `aₙ` be real with `n P(X_0 > aₙ) → τ`, `τ > 0`. Let `ρ ∈ (0, 1)` with `ρ ≠ γ/α`,
and let `rₙ ∈ ℕ` with `log rₙ / log n → ρ`. Then

  `AntiClustering P X a r`  ⟺  `ρ < γ/α`.

Lean: `ExtremeValueTheory.powEchoProcess_antiClustering_iff`, `Dependence/EchoPowerLag.lean:689`. Since
`γ ∈ (0, α)` is free, `γ/α` takes every value `ρ₀ ∈ (0, 1)` (take `γ = ρ₀ α`).

*The cluster ratio on both sides.* Let `uₙ` be real with `n P(X_0 > uₙ) → τ`, `τ > 0`; let `ρ ∈ (0, 1)`,
and `rₙ ∈ ℕ` with `log rₙ / log n → ρ`. Then:
1. if `ρ < γ/α`: `CRₙ → 1`, and `AntiClusteringAt P X u r` holds;
2. if `ρ > γ/α`: `CRₙ → 1/2`, and `ForwardAntiClusteringAt P X u r` fails.

Lean: `ExtremeValueTheory.powEchoProcess_polyBlocks`, `Dependence/EchoPowerLag.lean:651`.

*The critical scale.* Let `uₙ` be real with `n P(X_0 > uₙ) → τ`, `τ > 0`; let `rₙ ∈ ℕ` with `rₙ /
n^{γ/α} → c`, `c > 0`. Put `κ = (2/τ)^{γ/α} / c` and `φ = φ_{α/γ}` (D10). Then all of the following
hold:
1. `CRₙ → (1 + φ(κ))/2`;
2. the late-return mass at `(uₙ, rₙ)` is `(1 − φ(κ))/2`;
3. if `κ < 1`, `ForwardAntiClusteringAt P X u r` fails;
4. if `κ > 1`, `AntiClusteringAt P X u r` holds.

Lean: `ExtremeValueTheory.powEchoProcess_critical`, `Dependence/EchoPowerLag.lean:726`.

*The boundary at all levels.* See R14a: `AntiClustering` at the scale `ρ = γ/α` is decided there.

*The setting.* Under (E) and `0 < γ < α`: `X` is stationary (D1), has spectral tail process `Θ_t = 1{t =
0}` with index `α`, `ϑ = 1`, and `(X_n)_{n≥0}` has extremal index `θ = 1/2` (D4). Lean:
`ExtremeValueTheory.powEchoProcess_theta_lt_vartheta`, `Dependence/EchoPowerLag.lean:484`. The
equivalence is instantiated on a concrete process in `test_nonvacuous_powEchoProcess_antiClustering_iff`
(`Test/NonVacuity/Dependence.lean`), with `τ = 1`, `rₙ = ⌊√n⌋`, and `γ = 3α/4`, `γ = α/4` on the two
sides.

**(c) Caveats.**
1. *One level, not two.* Lean uses the same level for conditioning and exceedance; [BKW24] allow `b_n x`
   and `b_n y`. The two forms should be equivalent by the following elementary argument, which is
   **not** formalized. The case `x = y` gives one direction. Conversely, assume the same-level condition
   at every level. If `y ≥ x`, then `P(max > b_n x, X_0 > b_n y) ≤ P(max > b_n x, X_0 > b_n x)`, and
   `P(X_0 > b_n x)/P(X_0 > b_n y) → (y/x)^α` by regular variation. If `y < x`, then `{max > b_n x} ⊂
   {max > b_n y}`. Please check this.
2. *The failure is stronger than the negation, away from the critical scale.* For `ρ > γ/α`, the proof of
   "AC fails" uses only `x = 1` and only the forward half, so the failure already holds at `aₙ` itself for
   positive lags. The levels `aₙ` with `τ = 1` are `b_n`. This is not so at `ρ = γ/α`: see R14a, caveat 1.
3. *Range of the equivalence.* `ρ = 0` and `ρ = 1` are excluded, and `log rₙ / log n` must converge.
   Filling these in by monotonicity of `AC` in the block length is easy on paper but not formalized. `ρ =
   γ/α` is excluded from this theorem and treated separately in R14a.
4. *The critical theorem is about one level sequence.* `powEchoProcess_critical` concludes
   `AntiClusteringAt` at `(uₙ, rₙ)`, not `AntiClustering` at all levels; that is R14a. So its dependence on
   `c` does not give a value of `c` for which `AC` holds, and this does not affect the answer, since the
   question concerns ranges of `ρ`. The case `κ = 1` at a single level is undecided: there `CRₙ → 1` and
   the late-return mass is `0`, but anticlustering at that level is not settled.
5. *Normalizing levels only.* The equivalence uses `n P(X_0 > aₙ) → τ`. Anticlustering at intermediate
   levels in the style of [KS20] (`rₙ P(X_0 > cₙ) → 0`) is not characterized.
6. *The transition is a step.* `CRₙ` passes from `1` to `1/2` at `ρ₀`, whereas the transition in [BKW24]
   is linear in `ρ`. So this should not be described as the same type of transition.
7. *No claim about the intended class of models.* The process is driven by iid noise and is β-mixing.
   Nothing in the quoted text restricts the class, but the authors may have had something else in mind.

**(d) Questions.**
1. **Is this already known?** Is there an example, in [KS20], in Weissman–Cohen (1995), in a thesis or
   in unpublished work, of a regularly varying stationary process with `AC` for `ρ` below some `ρ₀ ∈ (0,
   1)` and failing above it, or of a delayed echo whose lag grows with the size of the shock?
2. **Does it answer what they meant?** Does the power-lag echo answer the second question of [BKW24,
   §1.4] as intended, or does the question implicitly exclude such a model?
3. Is the one-level `AntiClustering` equivalent to `AC(d_n, b_n)` by caveat 1?
4. Would a theorem at intermediate levels be needed for this to count as an answer?

## R14a. Anticlustering on the critical scale `rₙ ~ c n^{γ/α}` ★ (new)

**(a) Literature.** None; new, and novelty is provisional as for R14. The question quoted in R14 concerns
`ρ` up to `ρ₀` and says nothing about the boundary. The condition is [BKW24]'s `AC(d_n, b_n)`, quoted in
R14, up to R14, caveat 1.

**(b) Lean, in math.** Hypotheses (E) of D8, `0 < γ < α`, `X = echoProcess (powLag γ) Z`. Let `aₙ` be
real with `n P(X_0 > aₙ) → τ`, `τ > 0`, and let `rₙ ∈ ℕ`.

*Failure on the whole scale.* If `rₙ / n^{γ/α} → c` with `c > 0`, then `AntiClustering P X a r` (D9) is
false. Lean: `ExtremeValueTheory.powEchoProcess_not_antiClustering_critical`,
`Dependence/EchoPowerLag.lean:828`.

*Below the scale.* If `rₙ / n^{γ/α} → 0`, then `AntiClustering P X a r` holds. `rₙ → ∞` is not assumed,
and `log rₙ / log n` need not converge, so this includes `rₙ ~ n^{γ/α} / log n`, for which `ρ = γ/α`.
Lean: `ExtremeValueTheory.powEchoProcess_antiClustering_of_tendsto_zero`,
`Dependence/EchoPowerLag.lean:861`.

*Together.* If `rₙ / n^{γ/α} → c` with `c ≥ 0`, then `AntiClustering P X a r ⟺ c = 0`. Lean:
`ExtremeValueTheory.powEchoProcess_antiClustering_iff_critical`, `Dependence/EchoPowerLag.lean:916`.

Instantiated in `test_nonvacuous_powEchoProcess_not_antiClustering_critical`
(`Test/NonVacuity/Dependence.lean`), with `τ = 1`, `γ = α/2`, `rₙ = ⌊c √n⌋ + 1`, for every `c > 0`. The
other two theorems have no test of their own.

**(c) Caveats.**
1. *The failure is at a level that depends on `c`, not necessarily at `aₙ`.* The proof applies
   `powEchoProcess_critical` (R14) at the level `aₙ x`, where `n P(X_0 > aₙ x) → τ x^{−α}`, so that
   `κ(x) = x^γ (2/τ)^{γ/α} / c`, and takes `x` with `κ(x) = 1/2`. It is the failure of the forward half
   at this one `x`. At `x = 1`, R14 gives anticlustering when `κ(1) > 1`, that is for small `c`. So for
   small `c` and `τ = 1`, the condition holds at `b_n` itself and fails at `b_n x` for small `x`: the
   "for all `x`" in the definition is doing the work, and any statement of the boundary at one level
   would read differently.
2. *Relation to [BKW24].* `AC(d_n, b_n)` with `x = y` is `AntiClustering` at `a = b`, so the failure
   passes to their condition directly, by the easy direction of R14, caveat 1. The positive half needs
   the other direction of that caveat, which is not formalized.
3. *Not covered.* Sequences for which `rₙ / n^{γ/α}` has no limit in `[0, ∞)`, in particular
   `rₙ / n^{γ/α} → ∞` with `log rₙ / log n → γ/α`. Failure there should follow on paper by monotonicity
   of `AC` in the block length, comparing with `min(rₙ, ⌊n^{γ/α}⌋)`, but this is not formalized.
4. *This overtakes* an earlier description in this library, that at `ρ = ρ₀` "the answer depends on the
   constant". That is true of one level sequence only, and it is what `powEchoProcess_critical` says.

**(d) Questions.**
1. Is "`AC` fails when `rₙ ~ c n^{ρ₀}` for every `c > 0`, and holds when `rₙ = o(n^{ρ₀})`" the right
   description of the boundary, given that it comes from small `x`?
2. Should a boundary statement quantify over all `x`, as here and in [BKW24], or is the behaviour at
   `x = 1` the more natural object?

## R15. β-mixing without `θ = ϑ` ★ (new example)

**(a) Literature.** [BS09, §4]; [KS20, Ch. 7]: `AC(rₙ)` together with the block condition `𝒜` along the
**same** `rₙ` gives `θ = ϑ` (R5), and mixing is the usual route to `𝒜` (R12). [BW, Remark 1.4], about
their `θ < ϑ` model: "Our results indicate that our model does not enjoy very strong mixing properties."
We know of no statement in the literature that this entry contradicts, and nobody appears to have
conjectured the implication "mixing and `Θ_t → 0` give `θ = ϑ`". The classical related hypothesis is
`D^{(k)}(uₙ)` of Chernick–Hsing–McCormick (1991), whose examples were not read.

**(b) Lean, in math.** `β` is D11, `X` is D8.

*β-mixing for a general lag.* Let each `Z_t` be measurable, `(Z_t)` mutually independent, each `Z_t`
with law Pareto(`α`), `L` measurable, and `Σ_{j≥0} P(L(Z_0) ≥ j + 1) < ∞` (that is, `E L(Z_0) < ∞`).
Then `(echoProcess L Z k)_{k≥0}` is β-mixing. Neither `Z ≥ 0` nor `L ≥ 1` is assumed. Lean:
`ExtremeValueTheory.isBetaMixing_echoProcess`, `Dependence/EchoMixing.lean:225`.

*Geometric rate for the logarithmic lag.* Let `α > 0`, each `Z_t` measurable, `(Z_t)` mutually
independent, each `Z_t` with law Pareto(`α`), and `L = logLag`. Then for every `h ≥ 1`,

  `β(h) ≤ 2 · (2^α e^α / (1 − e^{−α})) · e^{−αh}`.

Lean: `ExtremeValueTheory.betaMixing_logEchoProcess_le`, `Dependence/EchoMixing.lean:250`.

*Incompatibility.* Assume (E), `L = logLag`, and write `𝒜(u, r)` for `ConditionA` of `(|X_k|)_{k≥0}` at
`(uₙ, rₙ)` (D6). Then the rate above holds, `(X_k)_{k≥0}` is β-mixing, and for all real `uₙ` and `τ > 0`
with `n P(X_0 > uₙ) → τ`, and all `rₙ → ∞`:
1. if `rₙ / log n → 0`: `AntiClusteringAt P X u r` holds and `𝒜(u, r)` fails;
2. if `rₙ / log n → c` with `c > 0`: `𝒜(u, r)` fails;
3. if `rₙ / n → 0` and `log n / rₙ → 0`: `𝒜(u, r)` holds and `ForwardAntiClusteringAt P X u r` fails.

Lean: `ExtremeValueTheory.logEchoProcess_betaMixing_incompatible`, `Dependence/EchoMixing.lean:402`.
Instantiated in `test_nonvacuous_logEchoProcess_betaMixing_incompatible`
(`Test/NonVacuity/Dependence.lean`).

*Power lag.* Under (E), `0 < γ < α`, `n P(X_0 > uₙ) → τ > 0`, `ρ ∈ (0, 1)`, `ρ ≠ γ/α`, `log rₙ / log n →
ρ`: `X` is β-mixing, `AntiClusteringAt P X u r ⟺ ρ < γ/α`, and `𝒜(u, r)` and `AntiClusteringAt P X u r`
do not both hold. Lean: `ExtremeValueTheory.powEchoProcess_not_conditionA_and_antiClustering`,
`Dependence/EchoMixing.lean:343`.

**(c) Caveats.**
1. *`θ` and `ϑ` are not in these statements.* The incompatibility theorem does not itself state
   stationarity, `ϑ = 1` or `θ = 1/2`. Those come from R9
   (`logEchoProcess_theta_lt_vartheta`). A single bundled statement with α-mixing in place of β-mixing
   is `Minimality.logEcho_alphaMixing_theta_ne_vartheta` (`Minimality/DependenceMixing.lean:344`).
2. *What the theorem it is compared with assumes.* `θ = ϑ` needs anticlustering **and** `𝒜(uₙ)` along a
   common block sequence, at every level with `n P(|X_0| > uₙ) → τ` (R5). With mixing, `𝒜` is derived
   but anticlustering stays a hypothesis (`HasSpectralTailProcess.hasExtremalIndex_abs_of_alphaMixing`,
   `Minimality/DependenceMixing.lean:309`). So the example shows that the common block sequence cannot
   be dropped; it is not a counterexample to any published theorem we know of.
3. *Block sequences not covered, log lag.* The three cases need `rₙ → ∞` and a limit of `rₙ / log n` in
   `[0, ∞]`; sequences with no such limit are not covered, nor is `rₙ / log n → ∞` without `rₙ = o(n)`.
   In case 2 the theorem says nothing about anticlustering.
4. *Power lag: less is proved than the log lag.* `𝒜` is shown to **fail** for `ρ < γ/α`, and `AC` to
   fail for `ρ > γ/α`. `𝒜` holding for `ρ > γ/α` is **not** proved, so "each holds on its own range of
   scales" is a statement about the log lag only. The scale `ρ = γ/α` is excluded. The rate `β(h) ≲ h^{1 − α/γ}` is a heuristic from
   the coupling bound `betaMixing_echoProcess_le`, not a theorem, and `IsBetaMixing` carries no rate.
5. *One-sided mixing.* D11 uses `(X_k)_{k≥0}`. The two-sided coefficient of the stationary sequence
   `(X_t)_{t∈ℤ}` should agree, but this is not stated.
6. *Not proved.* φ-mixing, and the remark in `docs/NOVELTY2.md` that `D(uₙ)` holds and `D^{(k)}(uₙ)`
   fails for every `k`, are not formalized.

**(d) Questions.**
1. Is an explicit strongly mixing regularly varying sequence with `Θ_t = 1{t = 0}` and `θ < 1` already
   known, for example among the examples of Chernick–Hsing–McCormick (1991), or in Weissman–Cohen (1995)
   if their translations may depend on the shock size?
2. Is "the common block sequence cannot be dropped" the right way to state what this shows?
3. Is D11 (finite partitions, supremum over `s`) the definition of absolute regularity you use, and is
   the one-sided index harmless?

## R16. Short runs: the runs estimator converges to `ϑ`, not to `θ`, on the echo process ★ (new)

**(a) Literature.** Run-length sensitivity is discussed in Smith–Weissman (1994) and Weissman–Novak
(1998), and the estimators in [KS20, Ch. 10]; these references come from the Lean source and were
**not** checked against the texts. According to `docs/NOVELTY.md`, this literature treats the effect as
a bias under mixing and anticlustering, and none of the papers checked there exhibits a limit that
depends on the scale of `rₙ`.

**(b) Lean, in math.** Assume (E), `L = logLag`. Write `pₙ = P(X_0 > uₙ)`. Let:
- `uₙ → ∞`, and `n pₙ → ∞` (intermediate levels);
- `rₙ → ∞`, and `rₙ / log uₙ → 0` (runs shorter than the echo lag of an exceedance);
- `sₙ → ∞`, `log n / sₙ → 0`, and `(rₙ + sₙ)/(n pₙ) → 0`.

Then `runsEstimator (X_k)_{k≥0} n rₙ uₙ → 1` in probability (D12).

Lean: `ExtremeValueTheory.logEcho_tendstoInMeasure_runsEstimator`,
`Statistics/ExtremalIndexEstimators.lean:1254`. Instantiated in
`test_nonvacuous_logEcho_tendstoInMeasure_runsEstimator` (`Test/NonVacuity/Dependence.lean`), with `uₙ =
n^{1/(4α)}`, `rₙ = ⌊√(log n)⌋`, `sₙ = ⌊√n⌋`.

Companion, for blocks: assume (E), `L = logLag`, `uₙ → ∞`, `rₙ → ∞`, `rₙ uₙ^{−α} → 0`, `log uₙ / rₙ →
0`, `log n / rₙ → 0`, `n pₙ → ∞` and `rₙ/(n pₙ) → 0`. Then `blocksEstimator (X_k)_{k≥0} n rₙ uₙ → 1/2`
in probability. Lean: `ExtremeValueTheory.logEcho_tendstoInMeasure_blocksEstimator`,
`Statistics/ExtremalIndexEstimators.lean:1210`.

**(c) Caveats.**
1. The statement only gives the limit `1`. That this differs from the extremal index needs R9 (`θ =
   1/2`), and that it equals `ϑ` needs R9 too (`ϑ = 1`).
2. It concerns this one process. It is not a theorem about the runs estimator in general, about other
   processes, or about data.
3. *Not covered.* A fixed run length (`rₙ → ∞` is assumed). Long runs: there is **no** theorem that the
   runs estimator with long runs tends to `1/2` on the echo process, so the entry does not say that long
   runs work. The claims in `docs/NOVELTY.md` about the intervals and K-gaps estimators on this process
   are not proved.
4. The levels have `n pₙ → ∞`, while `θ` is defined at `n pₙ → τ` (D4). `sₙ` is only an auxiliary
   sequence in the hypotheses; the estimator does not use it.
5. Asymptotic only. Since `log uₙ ≲ (1/α) log n`, the range `rₙ = o(log uₙ)` is narrow. The library says
   nothing about finite samples.

**(d) Questions.**
1. Is this a fair warning about short runs, or would you regard the echo process as too artificial for
   it to matter?
2. Is this inconsistency, on a process that is geometrically β-mixing, known? Do you expect the same for
   K-gaps?
3. Would a theorem for fixed `r`, or the long-run counterpart, be more useful than this one?

---

# Part II — Classical theory

## II.1 Fisher–Tippett–Gnedenko and domains of attraction

`F, G` below are c.d.f.s of probability measures on `ℝ`. An `AffineIncrEquiv` is a map
`A(x) = ax + b` with `a > 0`. `(A • F)(x) = F(A⁻¹x)` is the c.d.f. of `A(X)`. So
`((Aₙ • F)(x))^n = F^n(aₙx + bₙ)` with `Aₙ⁻¹(x) = aₙx + bₙ`, the c.d.f. of `(M_n − bₙ)/aₙ`.

### C1. Fisher–Tippett–Gnedenko

**(a)** [EKM, Thm 3.2.3]: a non-degenerate limit law of normalized maxima of iid variables is of the
type of `Λ`, `Φ_α` or `Ψ_α`.

**(b)** `IsExtremeValueDistr G` means: `G` is non-degenerate (not `{0, 1}`-valued), and there are a
c.d.f. `F` and affine maps `Aₙ` with `F^n(Aₙ⁻¹x) → G(x)` at every continuity point `x` of `G`.
Theorem: if `IsExtremeValueDistr G` then there is an `A` with `A • G = Λ`, or there are `A` and
`ξ > 0` with `A • G = Φ_ξ`, or there are `A` and `ξ > 0` with `A • G = Ψ_ξ`. Here
`Λ(x) = exp(−e^{−x})`, `Φ_ξ(x) = exp(−x^{−ξ})` for `x > 0` (and `0` otherwise), and
`Ψ_ξ(x) = exp(−(−x)^ξ)` for `x < 0` (and `1` otherwise). `A • G = Λ` means `G(x) = Λ(Ax)`.

Lean: `CumulativeDistributionFunction.IsExtremeValueDistr.classification`,
`ExtremeValueTheory/SelfSimilarCDF.lean:583`.

**(c)** Faithful. Based on Kalle Kytölä's ExtremeValueProject.

**(d)** 1. Does the definition of EVD match yours (iid, affine normalization with `a > 0`, weak
convergence)?

### C2. Max-stability and the GEV family

**(a)** [EKM, Thm 3.2.2, Def 3.4.1, Thm 3.4.5]: the max-stable laws are exactly the EVDs, and every
EVD is of the type of `H_ξ`.

**(b)** `IsMaxStable G`: `G` is non-degenerate and for every `n ≥ 1` there are `a > 0` and `b` with
`G(ax + b)^n = G(x)` for all `x`. Theorem 1: `IsMaxStable G ⟺ IsExtremeValueDistr G`. Theorem 2:
every EVD `G` has an `A` and a `ξ ∈ ℝ` with `A • G = H_ξ`, where `H_ξ(x) = exp(−(1+ξx)^{−1/ξ})` on
`1 + ξx > 0`, `H_0 = Λ`, and `H_ξ` is `0` or `1` off the support.

Lean: `CumulativeDistributionFunction.isMaxStable_iff_isExtremeValueDistr` (`GEV/MaxStable.lean:102`);
`CumulativeDistributionFunction.IsExtremeValueDistr.exists_smul_eq_gevCDF` (`GEV/Family.lean:172`).

**(c)** Faithful.  **(d)** None.

### C3. Fréchet domain

**(a)** [EKM, Thm 3.3.7]; [dHF, Thm 1.2.1(1)]: `F ∈ MDA(Φ_α) ⟺ 1 − F ∈ RV_{−α}`.

**(b)** For `α > 0`: (there are affine `Aₙ` with `F^n(Aₙ⁻¹x) → Φ_α(x)` for **every** `x`)
`⟺` `x ↦ 1 − F(x)` is regularly varying with index `−α`.
Lean: `CumulativeDistributionFunction.isInMDAFrechet_iff`, `DomainOfAttraction/Frechet.lean:552`.

**(c)** "For every `x`" is the same as "at continuity points" since `Φ_α` is continuous. Eventual
positivity of `1 − F` (part of RV) encodes `x_F = ∞`.  **(d)** None.

### C4. Weibull domain

**(a)** [EKM, Thm 3.3.12]: `F ∈ MDA(Ψ_α) ⟺ x_F < ∞` and `1 − F(x_F − 1/t) ∈ RV_{−α}`.

**(b)** For `α > 0`: `F ∈ MDA(Ψ_α)` (as in C3) `⟺` there is `x_F ∈ ℝ` with `F(x_F) = 1`,
`F(x) < 1` for all `x < x_F`, and `t ↦ 1 − F(x_F − t^{−1})` regularly varying with index `−α`.
Lean: `CumulativeDistributionFunction.isInMDAWeibull_iff`, `DomainOfAttraction/Weibull.lean:445`.

**(c)** `0^{−1} = 0` only affects `t = 0`, which is irrelevant at `∞`.  **(d)** None.

### C5. Gumbel domain

**(a)** [dHF, Thm 1.1.8 + 1.2.5]; [EKM, Thm 3.3.26]: `F ∈ MDA(Λ)` iff there is `f > 0` with
`(1 − F(t + x f(t)))/(1 − F(t)) → e^{−x}` as `t ↑ x_F`, for all `x`.

**(b)** `F ∈ MDA(Λ)` `⟺` either
(i) `F(x) < 1` for all `x`, and there is `f` with `f(t) > 0` eventually and, for every `x ∈ ℝ`,
`(1 − F(t + x f(t)))/(1 − F(t)) → e^{−x}` as `t → ∞`; or
(ii) there is `x_F` with `F(x) < 1` for `x < x_F`, `F(x_F) = 1`, and `f` with `f(t) > 0` for `t`
near `x_F` from below, and the same limit as `t ↑ x_F`.

Lean: `CumulativeDistributionFunction.isInMDAGumbel_iff`, `DomainOfAttraction/GumbelNecessity.lean:328`.

**(c)** Faithful. `1 − F(t) > 0` along the filter, so there is no division by 0. Von Mises sufficient
conditions are in `isInMDAGumbel_of_vonMises(_nhdsLT)`. The finite-endpoint version needs
`F(t) → 1` as `t ↑ x_F` (no atom at `x_F`), and a counterexample without it is documented.
**(d)** None.

### C6. Pickands–Balkema–de Haan (iff, all `ξ`)

**(a)** [EKM, Thm 3.4.13(b)]; [dHF, Thm 1.1.6]: `F ∈ MDA(H_ξ)` iff there is `β(u) > 0` with
`sup_{0<x<x_F−u} |F̄_u(x) − Ḡ_{ξ,β(u)}(x)| → 0` as `u ↑ x_F`.

**(b)** For every `ξ ∈ ℝ`: `F ∈ MDA(H_ξ)` `⟺` there is `β : ℝ → ℝ` with `β(u) > 0` eventually as
`u ↑ x_F`, and

  `sup_{x≥0} | F̄(u + β(u)x)/F̄(u) − Ḡ_ξ(x) | → 0` as `u ↑ x_F`,

where `F̄ = 1 − F` and `Ḡ_ξ(x) = (max(1 + ξx, 0))^{−1/ξ}` (`e^{−x}` for `ξ = 0`). "`u ↑ x_F`" is the
filter generated by the sets `{y > x : F(y) < 1}` with `F(x) < 1`. It is `atTop` if `x_F = ∞` and
left-neighborhoods of `x_F` otherwise, and it is never empty.

Lean: `CumulativeDistributionFunction.isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival`,
`PeaksOverThreshold/Converse.lean:783`. `IsInMDAGEV ξ` means `MDA(Φ_{1/ξ})`, `MDA(Ψ_{−1/ξ})` or
`MDA(Λ)` according to the sign of `ξ`.

**(c)** After the change of variable `x ↦ β(u)x` this is the textbook form with scale 1. For finite
`x_F`, uniformity over all `x ≥ 0` (beyond `x_F − u`) is at least as strong, since both sides vanish
there. The converse *proves* that there is no atom at `x_F` instead of assuming it.
**(d)** 1. Is the uniform-over-`x ≥ 0` form the one you would state?

### C7. Quantile characterization (extended regular variation)

**(a)** [dHF, Thm 1.1.6, Def B.2.1]: `F ∈ MDA(H_γ)` iff `U = (1/(1−F))^←` is extended regularly
varying with index `γ`.

**(b)** `F ∈ MDA(H_γ)` `⟺` there is `a` with `a(t) > 0` eventually and, for every `x > 0`,
`(U(xt) − U(t))/a(t) → D_γ(x)` as `t → ∞`, where `D_γ(x) = (x^γ − 1)/γ` (`log x` for `γ = 0`) and
`U(t) = inf{y : 1 − F(y) ≤ 1/t}`.

Lean: `CumulativeDistributionFunction.isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile`,
`DomainOfAttraction/Quantile.lean:700`.

**(c)** `U(t)` is junk (`sInf ∅ = 0`) for `t ≤ 0`, which is irrelevant at `∞`.  **(d)** None.

## II.2 Regular variation

### C8. Uniform convergence and representation theorems

**(a)** [BGT, Thm 1.2.1 / 1.5.2] (UCT); [BGT, Thm 1.3.1] (representation).

**(b)** *UCT*: if `f` is regularly varying with index `ρ` and measurable, then for every compact
`K ⊂ (0, ∞)`, `sup_{c∈K} |f(cx)/f(x) − c^ρ| → 0` as `x → ∞`.
*Representation*: for measurable `L`: `L` is slowly varying `⟺` there are `a > 0`, measurable `c`
and `ε`, with `c(x) → c₀ > 0`, `ε(x) → 0`, `t ↦ ε(t)/t` integrable on `[a, x]` for all `x ≥ a`, and
`L(x) = c(x) exp(∫_a^x ε(t)/t dt)` for all `x ≥ a`.

Lean: `ExtremeValueTheory.IsRegularlyVarying.tendstoUniformlyOn_of_measurable`
(`RegularVariation/UniformConvergence.lean:172`);
`ExtremeValueTheory.isSlowlyVarying_iff_exists_representation` (`RegularVariation/Representation.lean:309`).

**(c)** Measurability is required on all of `ℝ`. Integrability is explicit, so the integral is not
junk.  **(d)** None.

### C9. Karamata's theorem (both halves)

**(a)** [BGT, Prop 1.5.10, Thm 1.6.1]: for `f ∈ RV_{−α}`, `α > 1`, locally bounded,
`∫_x^∞ f / (x f(x)) → 1/(α − 1)`; conversely, `x f(x)/∫_x^∞ f → α − 1` implies `f ∈ RV_{−α}`.

**(b)** *Direct*: `F` measurable, `F` regularly varying with index `−α`, `α > 1` ⇒
`(∫_{(x,∞)} F)/(x F(x)) → 1/(α − 1)`.
*Converse*: `F` antitone on `ℝ`, integrable on some `(a, ∞)`, `α > 1`, and
`x F(x)/∫_{(x,∞)} F → α − 1` ⇒ `F` is regularly varying with index `−α`.

*Converse, no monotonicity*: `F` eventually positive, `α > 1`, and `x F(x)/∫_{(x,∞)} F → α − 1` ⇒ `F` is
regularly varying with index `−α`.

Lean: `ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_Ioi_div_of_measurable`
(`RegularVariation/KaramataConverse.lean`);
`ExtremeValueTheory.IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi` (antitone, deprecated) and
`ExtremeValueTheory.IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi_of_pos`
(`KaramataConverse.lean:299`).

**(c)** In the direct half, a non-integrable `F` would make the integral junk `0` and the conclusion
false, so integrability is necessarily proved. The antitone converse is superseded by the third statement.
In that one neither measurability nor integrability is assumed: if `∫_{(x,∞)} F` were junk `0`, the ratio
would be junk `0`, which contradicts the limit `α − 1 > 0`. This was added after this entry was written, and
was read only as a statement.  **(d)** None.

### C10. Breiman's lemma

**(a)** Breiman (1965); Jessen–Mikosch (2006, Lemma 4.2(1)).

**(b)** Let `X, Y` be measurable and independent, `Y ≥ 0` a.s., `α > 0`, `ε > 0`, `P(X > x)`
regularly varying with index `−α`, and `E[Y^{α+ε}] < ∞`. Then
`P(XY > x)/P(X > x) → E[Y^α]`.

Lean: `ExtremeValueTheory.tendsto_measure_mul_div_measure`, `RegularVariation/Breiman.lean:161`.

**(c)** No sign condition on `X`, as in the reference.  **(d)** None.

## II.3 Stable laws and the generalized CLT

Notation: `μ` is the law of `X`, `S_n = X₁ + ⋯ + X_n` iid (`convPow μ n`), `P(|X| > x)` is `absTail`,
`U(x) = E[X² 1{|X| ≤ x}]` is `truncSecondMoment`.

### C11. GCLT (sufficiency)

**(a)** [Feller, XVII.5 Thm 2]; [EKM, Thm 2.2.8].

**(b)** *Symmetric* (`tendsto_map_convPow_of_isRegularlyVarying`, `StableLaws/DomainOfAttraction.lean:431`):
`μ` symmetric, `0 < α < 2`, `P(|X| > x) ∈ RV_{−α}`, `aₙ > 0`, `n P(|X| > aₙ) → 1` ⇒ there is a
symmetric α-stable `ν` with `φ_ν(t) = exp(−C_α|t|^α)`, `C_α = α ∫_0^∞ (1 − cos u)u^{−α−1} du`, and
`law(S_n/aₙ) ⇒ ν`.
*Asymmetric, `1 < α < 2`* (`tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt'`,
`StableLaws/Constants.lean:378`): `P(|X| > x) ∈ RV_{−α}`, `P(X > x)/P(|X| > x) → p`, `aₙ > 0`,
`n P(|X| > aₙ) → 1` ⇒ there is `ν` with
`φ_ν(t) = exp(−Γ(1−α) cos(πα/2) |t|^α (1 − i(2p−1) sign(t) tan(πα/2)))` and
`law((S_n − n E X)/aₙ) ⇒ ν`.
Analogues exist for `0 < α < 1` (no centering) and `α = 1` (centering `n E[X 1{|X| ≤ aₙ}]`, limit
`exp(−(π/2)|t| + i(2p−1)((1−γ_E)t − t log|t|))`, with `γ_E` Euler's constant).

**(c)** For `1 < α < 2`, `Γ(1−α) cos(πα/2) > 0`. This is the [ST] parametrization with `σ^α = C_α`
and `β = 2p − 1`. `C_α` is a Bochner integral, junk outside `(0, 2)`, but used only inside.
**(d)** 1. Is the `α = 1` limit (with the constant `1 − γ_E` from this specific centering) the form
you would expect?

### C12. GCLT converse and domain-of-attraction iff

**(a)** [Feller, XVII.5 Thm 2]; Gnedenko–Kolmogorov §35; [Feller, VI.1 Thm 1].

**(b)**
- *Converse* (`GCLTConverse.exists_isRegularlyVarying_tailBalance_of_tendsto`,
  `StableLaws/GeneralizedCLTConverseAsymmetric.lean:407`): if `aₙ > 0` and
  `law((S_n − bₙ)/aₙ) ⇒ ν` with `ν` not a point mass, then there is `α ∈ (0, 2]` with
  `U ∈ RV_{2−α}`. If moreover `α < 2`, then `P(|X| > x) ∈ RV_{−α}`, `n P(|X| > aₙ) → B` for some
  `B > 0`, and `P(X > x)/P(|X| > x) → p` for some `p ∈ [0, 1]`.
- *DOA iff* (`domainOfAttraction_isStableIndex_iff`, `StableLaws/DomainOfAttractionIff.lean:662`):
  for `0 < α < 2`, (there are `aₙ > 0`, `bₙ` and an α-stable `ν` with `law((S_n − bₙ)/aₙ) ⇒ ν`) `⟺`
  (`P(|X| > x) ∈ RV_{−α}` and `P(X > x)/P(|X| > x) → p` for some `p ∈ [0, 1]`). Here "α-stable" is
  `IsStableIndex α ν`: `ν` is stable and `ν^{*n} = law(n^{1/α} Y + b_n)` for every `n ≥ 1`.
- *Gaussian DOA* (`domainOfAttraction_gaussianReal_iff`, `StableLaws/GaussianDomain.lean:394`):
  (there are `aₙ > 0`, `bₙ`, `m`, `v ≠ 0` with `law((S_n − bₙ)/aₙ) ⇒ N(m, v)`) `⟺` (`μ` is not a
  point mass and `U` is slowly varying).
- *Index* (`IsStable.existsUnique_isStableIndex`, `StableLaws/StableIndex.lean:417`): every stable
  law has a unique `α` with `IsStableIndex α`.

**(c)** `IsStable` excludes point masses. The "not a point mass" condition in the Gaussian iff is
necessary (a point mass at `c ≠ 0` has `U` slowly varying). The limit's shift is identified only up
to existence.
**(d)** 1. Is the `IsStableIndex` definition (norming exactly `n^{1/α}`) an acceptable stand-in for
"α-stable"?

## II.4 Statistics of extremes (iid)

Samples are `X_0, …, X_{n−1}`. `X_{(j+1)}` is the `(j+1)`-th largest (`orderStat x j`; junk `0` if
`j ≥ n`). `k = k(n)` always satisfies `k → ∞`, `k/n → 0`. Estimators use `Real.log`, so `log` of a
non-positive order statistic is junk; this happens only on events of vanishing probability.

### C13. Hill estimator: consistency and asymptotic normality

**(a)** [dHF, Thm 3.2.2] (Mason 1982); [dHF, Thm 3.2.5].

**(b)** `γ̂ = k^{−1} Σ_{i<k} (log X_{(i+1)} − log X_{(k+1)})`.
*Consistency* (`tendstoInMeasure_hill`, `Statistics/Hill.lean:504`): `X_i` measurable, iid,
`P(X_0 > x) ∈ RV_{−α}`, `α > 0` ⇒ `γ̂ → 1/α` in probability.
*Normality* (`tendstoInDistribution_hill`, `Statistics/HillNormality.lean:1221`): `X_i` measurable,
iid, `γ > 0`, `U` second-order regularly varying with indices `(γ, ρ)` and auxiliary function `A`,
and `√k A(n/k) → λ` ⇒ `√k(γ̂ − γ) ⇒ N(λ/(1 − ρ), γ²)`. Here `U(t) = inf{x : P(X_0 > x) ≤ 1/t}` for
`t > 1` (and `0` otherwise). Second-order RV means: `U > 0` eventually, `ρ ≤ 0`, `A → 0` with
eventually constant sign, `|A| ∈ RV_ρ`, and `(U(xt)/U(t) − x^γ)/A(t) → x^γ (x^ρ − 1)/ρ` for every
`x > 0` (`log x` at `ρ = 0`).

**(c)** No positivity assumption on `X`. The second-order definition *assumes* `|A| ∈ RV_ρ` and
constant sign, which dHF derive (Thm 2.3.3).
**(d)** 1. Is building `|A| ∈ RV_ρ` into the definition acceptable?

### C14. Pickands and moment estimators (all `ξ`)

**(a)** [EKM, Thm 6.4.1]; [dHF, §3.3]; [dHF, Thm 3.5.2] (Dekkers–Einmahl–de Haan).

**(b)** *Pickands* (`tendstoInMeasure_pickands`, `Statistics/Pickands.lean:270`):
`ξ̂ = (log 2)^{−1} log((X_{(k+1)} − X_{(2k+1)})/(X_{(2k+1)} − X_{(4k+1)}))`. If the `X_i` are
measurable and iid with c.d.f. `F` and `F ∈ MDA(H_ξ)` for some `ξ ∈ ℝ`, then `ξ̂ → ξ` in probability.
*Moment* (`tendstoInMeasure_momentEstimator_of_isInMDAGEV'`, `Statistics/MomentGeneral.lean:829`):
`γ̂ = M₁ + 1 − ½(1 − M₁²/M₂)^{−1}` with `M_j = k^{−1} Σ_{i<k} (log X_{(i+1)} − log X_{(k+1)})^j`.
If the `X_i` are iid, `F ∈ MDA(H_γ)` and `F(y) < 1` for some `y > 0` (`x_F > 0`), then `γ̂ → γ` in
probability.

**(c)** Consistency only here; normality is S13 and S14. The `+1` in the indices is one off from EKM.
Whether
`k` is the smallest or the largest of the three indices differs between sources, which does not affect
consistency, but does affect the variance in S13.  **(d)** None.

### C15. Weissman extreme-quantile estimator: asymptotic normality

**(a)** Weissman (1978); [dHF, Thm 4.3.1 / §4.3].

**(b)** `x̂_p = X_{(k+1)} (k/(n p))^{γ̂}` with `γ̂` the Hill estimator, and
`x_p = inf{x : P(X_0 > x) ≤ p}`. Let the `X_i` be iid, `γ > 0`, `ρ < 0`, `U` second-order RV
`(γ, ρ, A)`, `√k A(n/k) → λ`, `pₙ > 0` eventually, `dₙ = k/(n pₙ) → ∞`, and `log dₙ/√k → 0`. Then
`(√k / log dₙ)(x̂_{pₙ}/x_{pₙ} − 1) ⇒ N(λ/(1 − ρ), γ²)`.

Lean: `ExtremeValueTheory.tendstoInDistribution_weissman`, `Statistics/ExtremeQuantileSecondOrder.lean:1249`.

**(c)** `ρ < 0` here. A separate `ρ = 0` version assumes extra regularity of `A`
(`tendstoInDistribution_weissman_of_rho_eq_zero`) and was not checked against dHF.
**(d)** 1. Is the `ρ = 0` bias cancellation claimed in the README (Hill bias and extrapolation bias
cancel) known to you?

## II.5 Dependent data: Leadbetter and the Hill estimator

### C16. Leadbetter's theorem and `H^θ`

**(a)** [LLR, Thm 3.4.1, 3.7.1]; [EKM, Thm 4.4.3, 8.1.2].

**(b)** *Leadbetter* (`tendsto_measureReal_partialMax_le_exp`, `Dependence/Leadbetter.lean:431`):
`X` stationary (`ℕ`-indexed) and measurable, `D(uₙ)`, `D'(uₙ)`, `n P(X_0 > uₙ) → τ` ⇒
`P(M_n ≤ uₙ) → e^{−τ}`. `D(uₙ)`: there are `lₙ = o(n)` and `αₙ → 0` with
`|P(max_{A∪B} X ≤ uₙ) − P(max_A X ≤ uₙ)P(max_B X ≤ uₙ)| ≤ αₙ` for all `A, B ⊂ {0, …, n−1}` with
`min B ≥ max A + lₙ`. `D'(uₙ)`: for every `ε > 0` there is `k₀` such that for every `k ≥ k₀`,
eventually `n Σ_{1≤j<⌊n/k⌋} P(X_0 > uₙ, X_j > uₙ) ≤ ε`.
*`H^θ`* (`tendsto_measureReal_partialMax_le_pow`, `Dependence/ExtremalIndex.lean:190`): `X`
stationary and measurable with marginal c.d.f. `F`, `H` an EVD, `F^n(Aₙ⁻¹x) → H(x)` for every `x`,
and `X` has extremal index `θ > 0` ⇒ `P(M_n ≤ Aₙ⁻¹x) → H(x)^θ` for every `x`.

**(c)** `D` quantifies over separated index sets, with the definition's `αₙ` independent of the
sets. `⌊n/k⌋` is ℕ-division.  **(d)** None.

### C17. Hill estimator for dependent data

**(a)** Resnick–Stărică (1995); Rootzén–Leadbetter–de Haan (1998); [KS20, §9.1].

**(b)** *Variance reduction* (`tendstoInMeasure_hill_of_variance`, `Statistics/HillDependent.lean:323`):
`X_i` measurable with identical marginals (no independence or stationarity), `P(X_0 > x) ∈ RV_{−α}`,
`α > 0`, `k → ∞`, `k/n → 0`. Suppose that for every `uₙ → ∞` and `c > 0` with
`n P(X_0 > uₙ)/k → c`, `Var(Σ_{i<n} 1{X_i > uₙ})/k² → 0`. Then `γ̂ → 1/α` in probability.
*α-mixing* (`tendstoInMeasure_hill_of_alphaMixing_rate`, `HillDependent.lean:901`): `X` stationary,
the same RV and `k` conditions, `rₙ ∈ ℕ`, the cluster condition
`Σ_{h=1}^{rₙ} P(X_0 > uₙ, X_h > uₙ) / (P(X_0 > uₙ) k) → 0` for all such `uₙ`, and
`(n/k)² α(rₙ + 1) → 0` ⇒ `γ̂ → 1/α` in probability.

**(c)** The cluster condition is assumed, not derived from the tail process. The mixing rate is a
simple sufficient one, not the sharpest. A version under `S(rₙ, uₙ)` exists
(`tendstoInMeasure_hill_of_alphaMixing_of_sumAntiClustering`) but has no concrete instance yet.
**(d)** 1. Is `(n/k)² α(rₙ + 1) → 0` too strong to cover standard examples (ARMA, GARCH)?

## II.6 Multivariate regular variation and max-stable vectors

### C18. Multivariate regular variation: polar characterization

**(a)** Hult–Lindskog (2006); [Resnick, Thm 6.1]; [KS20, §2.1].

**(b)** `IsRegVarVector P X α μ` means: `P(‖X‖ > x) ∈ RV_{−α}`; `μ{0} = 0`; `μ{‖y‖ > r} < ∞` for
`r > 0`; and `E[f(X/x)]/P(‖X‖ > x) → ∫ f dμ` for every bounded continuous `f` vanishing on a
neighbourhood of `0`. Theorem: for `α > 0`, `X` measurable with values in a separable normed space
`E`: (there is `μ` with `IsRegVarVector P X α μ`) `⟺` (`P(‖X‖ > x) ∈ RV_{−α}`, and there is a
probability `S` on `E` with `law(X/‖X‖ | ‖X‖ > x) ⇒ S`).

Lean: `ExtremeValueTheory.isRegVarVector_iff`, `RegularVariation/Multivariate/Polar.lean:395`.

**(c)** Normalized by `P(‖X‖ > x)` rather than a sequence `aₙ`, so `μ{‖y‖ > 1} = 1`. This is the
`M_0` convergence of Hult–Lindskog. The polar form `μ = α r^{−α−1}dr ⊗ S` is
`IsRegVarVector.eq_polarMeasure`.
**(d)** 1. For infinite-dimensional `E`, is this the right notion?

### C19. Converse Cramér–Wold device (non-integer `α`)

**(a)** Basrak–Davis–Mikosch (2002), Thm 1.1(i).

**(b)** `E` a finite-dimensional real normed space, `X` measurable, `α > 0` not an integer,
`V ∈ RV_{−α}`, `w` a function on linear functionals with `P(L(X) > x)/V(x) → w(L)` for every
continuous linear `L`, and `w(L) ≠ 0` for some `L` ⇒ there is `μ` with `IsRegVarVector P X α μ`.

Lean: `ExtremeValueTheory.CramerWold.isRegVarVector_of_tendsto_linear`,
`RegularVariation/CramerWoldConverse.lean:572`.

**(c)** Normalization by a regularly varying function of a continuous variable instead of
`aₙ`-sequences. The integer-`α` counterexamples (Hult–Lindskog 2006) are not formalized.
**(d)** None.

### C20. Spectral representation of simple max-stable vectors

**(a)** de Haan (1984); [dHF, §6.1]; [Resnick, Prop 5.11].

**(b)** `IsSimpleMaxStable μ` (`ι` finite): `μ` is a probability on `ℝ^ι` with unit Fréchet margins
(`P(Y_i ≤ y) = e^{−1/y}` for `y > 0`) and `F(y)^n = F(y/n)` for every `n ≥ 1` and every `y` with
positive coordinates, where `F(y) = μ(Y ≤ y)`.
- *Existence* (`IsSimpleMaxStable.exists_hasSpectralMeasure`, `MaxStable/Converse.lean:606`): there is
  a finite `H` on `[0, ∞]^ι` with `w_i ≤ 1` and `max_i w_i = 1` `H`-a.e. (sup-norm sphere),
  `∫ w_i dH = 1` for each `i`, and `F(y) = exp(−∫ max_i (w_i/y_i) dH(w))` for `y > 0`.
- *Uniqueness* (`IsSimpleMaxStable.existsUnique_hasSpectralMeasure`, `MaxStable/Uniqueness.lean:458`):
  `H` is unique among finite measures concentrated on `{max_i w_i = 1}` with this representation.
- *Construction* (`exists_isSimpleMaxStable_of_spectralMeasure`, `MaxStable/Spectral.lean:415`): every
  s-finite `H` with `∫ w_i dH = 1` for all `i` arises from some simple max-stable `ν` this way.

**(c)** The integral is `[0, ∞]`-valued and `.toReal`'d, but it is bounded by `Σ_i 1/y_i < ∞`, so it
is never junk. The library's Pickands-function convention puts the weight `t` on coordinate 0 (a
mirror of some texts). Processes are covered through finite-dimensional laws; the marking theorem is
not formalized.
**(d)** None.

## II.7 Point processes

### C21. Point process of exceedances

**(a)** [Resnick, Cor 4.19]; [EKM, Thm 5.3.2].

**(b)** Let the `X_i` be measurable, independent, with common c.d.f. `F`, and
`F^n(Aₙ⁻¹x) → G(x)` for every `x`. Fix `u` with `G(u) > 0` and let `N'` be a Poisson random measure
with intensity `Leb|_{(0,1]} ⊗ μ_G` on `ℝ²`, where `μ_G` is carried by `(u, ∞)` with
`μ_G(a, b] = log G(b) − log G(a)`. Let `Nₙ = Σ_{i<n} δ_{((i+1)/n, Aₙ(X_i))}`. Then for any finitely
many pairwise disjoint rectangles `R_j = (s_j, t_j] × C_j` with `0 ≤ s_j ≤ t_j ≤ 1`, where each `C_j`
is `(a, b]` or `(a, ∞)` with `u ≤ a` and `G ∈ (0, 1)` at its finite endpoints, and any counts
`m_j ∈ ℕ`: `P(Nₙ(R_j) = m_j for all j) → P(N'(R_j) = m_j for all j)`.

Lean: `ExtremeValueTheory.tendsto_measureReal_sumDiracRange_timeSpace_eq`,
`PointProcess/Exceedances.lean:364`.

**(c)** This is convergence of finite-dimensional count laws on a class of rectangles, not
convergence in the vague topology on the compactified state space.
**(d)** 1. For the EVT applications you know, is the fdd-count form enough?

### C22. Binomial point processes → Poisson random measure

**(a)** [Resnick, Prop 3.21]; Kallenberg Thm 4.11.

**(b)** `E` locally compact Hausdorff regular, `μₙ` probability measures, `n μₙ → ν` vaguely
(`∫ f d(nμₙ) → ∫ f dν` for compactly supported continuous `f`), `ν` regular, `N'` a PRM(`ν`). Then
`Σ_{k<n} δ_{Z_k}` (`Z_k` iid `μₙ`) converges to `N'` in the sense: for all pairwise disjoint
measurable `B_1, …, B_k` with compact closure and `ν(∂B_j) = 0`, the joint count probabilities
converge.

Lean: `ProbabilityTheory.tendstoInLawVaguely_sumDiracRange`,
`ForMathlib/Probability/PointProcessConvergence.lean:114`.

**(c)** fdd-count formulation on disjoint sets only. `IsPoissonRandomMeasure` requires independent
Poisson counts on disjoint finite-intensity sets, plus `N(A) = ∞` a.s. when `ν(A) = ∞`.
**(d)** None.

## II.8 Skorokhod space and the tail empirical process

### C23. `D[0, 1]` is Polish

**(a)** [Billingsley, Thms 12.1–12.2].

**(b)** For a complete separable (e)metric space `E`, `D([0, 1], E)` with the `J₁` topology is a
Polish space. Lean: `SkorokhodSpace.instPolishSpace`, `ForMathlib/Topology/Skorokhod/Complete.lean:692`.

**(c)** `J₁` is defined via time changes that are order isomorphisms of `[0, 1]`. Also proved:
separability (Thm 12.2) and Borel σ-algebra equal to the projection σ-algebra (Thm 12.5).
**(d)** None.

### C24. Tail empirical process → Brownian motion

**(a)** [dHF, Thm 5.1.4]; Einmahl (1992).

**(b)** Let `U_i` be iid Uniform`[0, 1]`, `k → ∞`, `k/n → 0`, and
`Wₙ(t) = √k (k^{−1} Σ_{i<n} 1{U_i ≥ 1 − (k/n)t} − t)`, `t ∈ [0, 1]`. Let `B` be any measurable
random element of `D[0, 1]` whose finite-dimensional laws are Gaussian with covariance `min(s, t)`.
Then `Wₙ ⇒ B` in `D[0, 1]` with the `J₁` topology.

Lean: `ExtremeValueTheory.tendstoInDistribution_tailEmpiricalPath`,
`Statistics/TailEmpiricalProcess.lean:1167`.

**(c)** Uniform, unweighted version only. The weighted (Chibisov–O'Reilly) version and the process
for regularly varying `F` are not done. `≥` rather than `>` in the indicator, for càdlàg paths.
**(d)** 1. Which extension would be most valuable: weighted, or general regularly varying `F`?

## II.9 Likelihood inference for the GPD and GEV

`gpdLogLikE` / `gevLogLikE` are log-likelihoods valued in `[−∞, ∞)`, equal to `−∞` exactly when a
data point is outside the support (the real-valued versions instead use `log 0 = 0`, which is why the
extended-real ones are used here).

### C25. GPD and GEV MLE: strong consistency

**(a)** Wald (1949); Smith (1985).

**(b)** *GPD* (`ae_tendsto_gpdMLE'`, `Statistics/GPDJointMLE.lean:539`): `K` compact with
`ξ > −1`, `σ > 0` on `K`, `θ₀ ∈ K`, and the `X_i` independent with law GPD`(θ₀)`. Then almost surely
the following holds: for every sequence `θ̂ₙ ∈ K` and every `εₙ → 0` with
`ℓₙ(θ₀) ≤ ℓₙ(θ̂ₙ) + n εₙ` eventually, we have `θ̂ₙ → θ₀`.
*GEV* (`ae_tendsto_gevMLE`, `Statistics/GEVMLE.lean:607`): the same, with parameters `(ξ, μ, σ)`
and `ξ > −1`, `σ > 0` on `K`.

**(c)** The null set does not depend on the estimator sequence. The approximate-maximizer condition
only compares with `θ₀`, which is weaker than maximizing over `K`. Restriction to a compact `K` is
standard because the likelihood is unbounded for `ξ < −1`.
**(d)** 1. Is "on a compact `K ⊂ {ξ > −1}`" the form of consistency you would cite?

### C26. GPD MLE: joint asymptotic normality

**(a)** Smith (1985); Coles, Ch. 4. For `ξ₀ > −1/2`, `√n(θ̂ − θ₀) ⇒ N(0, I(θ₀)^{−1})`.

**(b)** Let `K` be compact with `ξ > −1`, `σ > 0` on `K`; `(ξ₀, σ₀)` in the interior of `K`;
`−1/2 < ξ₀`, `ξ₀ ≠ 0`, `σ₀ > 0`; the `X_i` iid GPD(`ξ₀, σ₀`); and `W ~ N(0, I^{−1})` with
`I^{−1} = (1 + ξ₀)[[1 + ξ₀, −σ₀], [−σ₀, 2σ₀²]]`. Then there are measurable maps
`gₙ : ℝⁿ → K` such that `gₙ(x)` maximizes `ℓₙ` over `K` for **every** sample `x`, and
`√n(gₙ(X) − (ξ₀, σ₀)) ⇒ W`.

Lean: `ExtremeValueTheory.exists_gpdMLE_tendstoInDistribution`, `Statistics/GPDMLENormality.lean:246`.

**(c)** This theorem states existence of *some* measurable maximizer that is asymptotically normal.
Every almost everywhere measurable maximizer is covered by `tendstoInDistribution_gpdMLE_all` (see S8).
`ξ₀ = 0` is not covered. Joint normality for the GEV is S10.
**(d)** 1. Is the measurable-maximizer form of S8 adequate? 2. How important is `ξ₀ = 0`?

---

# Part III — Statistics: return levels, intervals, estimators of `θ`, likelihood, GARCH, tail dependence

All files are in `ExtremeValueTheory/Statistics/` unless stated otherwise. The scope of these results is
often narrower than the name of the theorem suggests: several are the continuous mapping theorem or the
delta method applied to a hypothesis. The caveats say so. References in (a) come from the Lean source
and were **not** checked against the texts. The entries are numbered in the order they were written, so
S10, the main likelihood theorem, comes after S7, on which it builds. S16 is classical, and is here because
it connects the library's definition of a domain of attraction with the textbook's.

Notation. `TendstoInDistribution` compares a sequence on `(Ω, P)` with a limit on another space; below
we write `⇒`. `N(0, V)` is `multivariateGaussian 0 V`, or `gaussianReal 0 v` in dimension one, where the
variance `v` is a `.toNNReal`. `GPD(ξ, σ)` is `gpdMeasure ξ σ`, the law of `σ(e^{ξE} − 1)/ξ` for `E`
standard exponential (`σE` at `ξ = 0`). `h_ξ(x) = boxCox ξ x = (x^ξ − 1)/ξ`, with `h_0 = log`. `ℓₙ` is
the `[−∞, ∞)`-valued log-likelihood of II.9.

## S1. The delta method

**(a) Literature.** [vdV, Thm 3.1].

**(b) Lean, in math.** *General* (`MeasureTheory.TendstoInDistribution.delta_method`,
`ForMathlib/Probability/DeltaMethod.lean:117`). Let `l` be a countably generated filter, `E` a normed
space with opens measurable, `F` a second-countable normed space with its Borel σ-algebra, `θ̂ᵢ : Ω → E`
on one probability space, `rᵢ → ∞` real, `rᵢ(θ̂ᵢ − θ) ⇒ Z`, `g : E → F` Fréchet differentiable at `θ`
with derivative `g'`, and each `g(θ̂ᵢ)` almost everywhere measurable. Then `rᵢ(g(θ̂ᵢ) − g(θ)) ⇒ g'(Z)`.

*Gaussian* (`MeasureTheory.TendstoInDistribution.delta_method_gaussian`, `DeltaMethod.lean:200`). Let
`θ̂ᵢ` take values in `ℝ^κ`, `κ` finite, `S` positive semidefinite, `Z ~ N(0, S)`, `rᵢ(θ̂ᵢ − θ) ⇒ Z`, `rᵢ
→ ∞`, `g : ℝ^κ → ℝ` with gradient `a` at `θ`, `g(θ̂ᵢ)` almost everywhere measurable, and `W ~ N(0,
aᵀSa)`. Then `rᵢ(g(θ̂ᵢ) − g(θ)) ⇒ W`.

**(c) Caveats.** Differentiability at the single point `θ`. A zero gradient gives a point mass limit,
not a higher-order expansion; second-order delta is not covered.

**(d) Questions.** None specific.

## S2. GEV and Gumbel return levels: the delta method, with parameter normality assumed

The theorem with no such assumption, for the maximum likelihood estimator, is S11. This entry is the general
form it is derived from, and it is still the only form for `ξ₀ = 0`.

**(a) Literature.** [Coles, §3.3.3]. `z_m = μ − (σ/ξ)(1 − y_m^{−ξ})`, `y_m = −log(1 − 1/m)` (`z_m = μ −
σ log y_m` at `ξ = 0`), and `√n(ẑ_m − z_m) ⇒ N(0, ∇zᵀV∇z)`.

**(b) Lean, in math.** Definitions: `gevReturnLevel ξ μ σ m = μ + σ r(ξ, m)`, with `r(ξ, m) = (y_m^{−ξ}
− 1)/ξ`, and `r(0, m) = −log y_m` (`ReturnLevelNormality.lean:160`, `ExtremeQuantile.lean:752`).
Gradient in `(ξ, μ, σ)`: `∇z = (σ ∂_ξ h_ξ(1/y_m), 1, r(ξ, m))`, with `∂_ξ h_ξ(x) = x^ξ log x / ξ − (x^ξ
− 1)/ξ²` (`gevReturnLevelGrad`).

*GEV.* Let `ξ₀ ≠ 0`, `m > 1`; `θ̂ₙ = (ξ̂ₙ, μ̂ₙ, σ̂ₙ)` almost everywhere measurable on `(Ω, P)`; `V`
positive semidefinite; `Z ~ N(0, V)`; `√n(ξ̂ₙ − ξ₀, μ̂ₙ − μ₀, σ̂ₙ − σ₀) ⇒ Z`; `W ~ N(0, ∇zᵀV∇z)`, with
`∇z` at `(ξ₀, σ₀, m)`. Then `√n(gevReturnLevel θ̂ₙ m − gevReturnLevel ξ₀ μ₀ σ₀ m) ⇒ W`. Lean:
`ExtremeValueTheory.tendstoInDistribution_gevReturnLevel`, `ReturnLevelNormality.lean:448`.

*Gumbel.* Let `θ̂ₙ = (μ̂ₙ, σ̂ₙ)` be almost everywhere measurable, `V` positive semidefinite, `Z ~ N(0,
V)`, `√n(μ̂ₙ − μ₀, σ̂ₙ − σ₀) ⇒ Z`, and `W ~ N(0, aᵀVa)` with `a = (1, −log y_m)`. Then
`√n(gevReturnLevel 0 μ̂ₙ σ̂ₙ m − gevReturnLevel 0 μ₀ σ₀ m) ⇒ W`. Lean:
`ExtremeValueTheory.tendstoInDistribution_gumbelReturnLevel`, `ReturnLevelNormality.lean:477`.

**(c) Caveats.**
1. **No data appear in these statements.** Parameter normality is a hypothesis, `θ̂ₙ` is any estimator,
   and `V` is any positive semidefinite matrix. They are the delta method for a specific `g`. The hypothesis
   is discharged for the GEV maximum likelihood estimator at `ξ₀ ≠ 0` by S10, which gives S11. At `ξ₀ = 0`,
   nothing in the library discharges it, for either statement: the Gumbel statement here has the shape
   fixed at `0`, and joint normality at `ξ₀ = 0` is not proved.
2. `σ₀ > 0` is not assumed, and the Gumbel statement does not assume `m > 1`; for `m ≤ 1` the level is a
   junk value, though the statement is still true, since `z` is linear in `(μ, σ)`.
3. `m` is fixed as `n → ∞`, so there is no extrapolation with `m = mₙ → ∞`. The three-parameter version
   at `ξ₀ = 0` is not covered.
4. The non-vacuity tests (`Test/NonVacuity/StatisticsReturnLevels.lean`) use a synthetic estimator `θ₀ +
   Z/√n`, `Z ~ N(0, V)`, for every positive semidefinite `V`: since no data appear in the statements, this
   only shows that the hypotheses are jointly satisfiable. The GEV maximum likelihood estimator satisfies
   them
   at `ξ₀ ≠ 0`, by S10. The known answers (`Test/KnownAnswers/ReturnLevels.lean`) reproduce Coles' Port
   Pirie
   level and variance, from his own covariance matrix, not from `gevMLECov`.

**(d) Questions.** 1. Is the Gumbel statement (shape fixed at `0`) the form you would use?

## S3. POT return level: normality of the GPD maximum likelihood version

**(a) Literature.** [Coles, (4.12), §4.3.3]; Smith (1985). `x_N = u + (σ/ξ)((Nζ)^ξ − 1)`, with `ζ = P(X
> u)`.

**(b) Lean, in math.** `gpdReturnLevel u ξ σ ζ N = u + σ h_ξ(Nζ)` (`ReturnLevelNormality.lean:278`).
`gpdReturnLevelVar ξ σ ζ N` (`:360`) is `(1 + ξ)((1 + ξ)a² − 2σab + 2σ²b²)`, with `a = σ ∂_ξ h_ξ(Nζ)`,
`b = h_ξ(Nζ)`; it equals `∇xᵀ I⁻¹ ∇x` by `dotProduct_gpdReturnLevelGrad`, with `I⁻¹` as in C26.

Let `K ⊂ ℝ²` be compact, with `ξ > −1` and `σ > 0` on `K`; `(ξ₀, σ₀)` in the interior of `K`; `ξ₀ >
−1/2`, `ξ₀ ≠ 0`, `σ₀ > 0`; `(X_i)` mutually independent, each with law GPD(`ξ₀, σ₀`); `θ̂ₙ : Ω → ℝ²`
almost everywhere measurable, with `θ̂ₙ(ω) ∈ K` and `θ̂ₙ(ω)` a maximizer over `K` of `ℓₙ` at `(X_0(ω),
…, X_{n−1}(ω))`, for **all** `n` and `ω`; `u, ζ, N` real with `Nζ > 0`; `W ~ N(0, gpdReturnLevelVar ξ₀
σ₀ ζ N)`. Then

  `√n(gpdReturnLevel u θ̂ₙ ζ N − gpdReturnLevel u ξ₀ σ₀ ζ N) ⇒ W`.

Lean: `ExtremeValueTheory.tendstoInDistribution_gpdReturnLevel`, `ReturnLevelNormality.lean:548`.

**(c) Caveats.**
1. **The data are exactly GPD excesses.** `X_i` is an exact iid GPD sample of deterministic size `n`.
   There is no parent law `F` and no hypothesis linking `ζ` or `u` to the data: `ζ` is a known constant
   and `u` an additive constant. The random number of exceedances, the approximation error of the GPD
   above a finite threshold, and the estimation of `ζ` are not accounted for.
2. With estimated `ζ`, `tendstoInDistribution_gpdReturnLevel₃` (`ReturnLevelNormality.lean:579`) assumes
   joint normality of `(ζ̂, ξ̂, σ̂)` as a hypothesis.
3. `N` is fixed as `n → ∞`. `Nζ > 0` allows `Nζ = 1`, where the gradient vanishes and the limit is a
   point mass, and `Nζ < 1`, where the level lies below `u`. `Nζ > 1` is what the interval in S4 needs.
4. `ξ₀ = 0` is not covered. Maximization is over a compact set assumed to contain `θ₀` in its interior.

**(d) Questions.** 1. Which of the omissions in caveat 1 matters most to you?

## S4. Wald intervals for the return level and the tail index

**(a) Literature.** [Coles, §3.3.3, §4.3.3]; [dHF, §3.2].

**(b) Lean, in math.** In both statements `z` is any real number, and `N(0, 1)[−z, z]` is `gaussianReal
0 1 (Icc (−z) z)` (empty for `z < 0`, with limit `0`).

*POT return level.* Under the hypotheses of S3, with `Nζ > 1` in place of `Nζ > 0`, and with `ŝₙ =
√(gpdReturnLevelVar θ̂ₙ ζ N)` (plug-in):

  `P(x_N ∈ [x̂_N − z ŝₙ/√n, x̂_N + z ŝₙ/√n]) → N(0, 1)[−z, z]`,

where `x_N = gpdReturnLevel u ξ₀ σ₀ ζ N` and `x̂_N = gpdReturnLevel u θ̂ₙ ζ N`. Lean:
`ExtremeValueTheory.tendsto_measure_mem_gpdReturnLevelInterval`, `ConfidenceIntervals.lean:120`.

*Hill.* Let `X_i` be measurable, mutually independent, identically distributed; `γ > 0`; `U(t) = inf{x :
P(X_0 > x) ≤ 1/t}` for `t > 1` (and `0` otherwise); `U` second-order regularly varying with indices `(γ,
ρ)` and auxiliary function `A` (C13); `kₙ → ∞`, `kₙ/n → 0`, `√kₙ A(n/kₙ) → 0`. With `γ̂ₙ` the Hill
estimator (C13),

  `P(γ ∈ [γ̂ₙ − z γ̂ₙ/√kₙ, γ̂ₙ + z γ̂ₙ/√kₙ]) → N(0, 1)[−z, z]`.

Lean: `ExtremeValueTheory.tendsto_measure_mem_hillInterval`, `ConfidenceIntervals.lean:57`.

A third version, `tendsto_measure_mem_gevReturnLevelInterval` (`ConfidenceIntervals.lean:177`), assumes
parameter normality and a consistent standard error `Ŝₙ → s > 0`. For the maximum likelihood estimator
the first assumption is removed in S11; the second is not.

**(c) Caveats.**
1. Return level: all caveats of S3. At `ξ̂ₙ = 0` the plug-in variance uses a junk derivative (`∂_ξ h`
   has `ξ` in denominators, so it evaluates to `0`); this is irrelevant in the limit because `ξ₀ ≠ 0`.
2. Hill: no bias only (`λ = 0`). The second-order definition requires `A` to have an eventually constant
   nonzero sign, so **exact Pareto data do not satisfy it** (`FAITHFULNESS.md`), and the theorem does
   not apply to them.
3. Symmetric Wald intervals only in this entry. Profile-likelihood sets for the POT return level are S12,
   for
   `ξ₀ > 0`; for the GEV return level they are not covered. Coverage is pointwise at a fixed parameter, not
   uniform.
4. Non-vacuity: `test_nonvacuous_tendsto_measure_mem_gpdReturnLevelInterval` (iid `GPD(1/4, 3/2)`, the
   library's measurable maximizers), `test_nonvacuous_tendsto_measure_mem_hillInterval` (shifted Pareto,
   `U(t) = t + 1`), and `test_nonvacuous_tendsto_measure_mem_gevReturnLevelInterval` (synthetic estimator,
   as in S2).

**(d) Questions.** 1. Is the form `γ̂ ± zγ̂/√k` the one you use? 2. Is the absence of a uniform
statement significant?

## S5. Blocks and runs estimators: consistency for an assumed population limit

**(a) Literature.** Hsing (1991); Smith–Weissman (1994); Weissman–Novak (1998); [KS20, §10.2].

**(b) Lean, in math.** Estimators as in D12. Write `pₙ = P(X_0 > uₙ)`. In both theorems `α(h)` is
`alphaMixing X P h` (R12), `X : ℕ → Ω → ℝ` is measurable and stationary (D1), `rₙ/n → 0`, `n pₙ → ∞`,
and `θ` is **any real number**.

*Blocks.* Assume `rₙ > 0` eventually, and there is `sₙ ∈ ℕ` with:
- `P(max_{t<rₙ} X_t > uₙ) / (rₙ pₙ) → θ`;
- `Σ_{1≤h≤sₙ} P(X_0 > uₙ, X_h > uₙ) / (n pₙ²) → 0`;
- `Σ_{sₙ<h<n} α(h) / (n pₙ²) → 0`;
- `α(rₙ + 1) / (rₙ pₙ)² → 0`.

Then `blocksEstimator X n rₙ uₙ → θ` in probability. Lean:
`ExtremeValueTheory.tendstoInMeasure_blocksEstimator`, `ExtremalIndexEstimators.lean:658`.

*Runs.* Assume there is `sₙ ∈ ℕ` with:
- `P(X_0 > uₙ, X_1 ≤ uₙ, …, X_{rₙ} ≤ uₙ) / pₙ → θ`;
- `Σ_{1≤h≤rₙ+sₙ} P(X_0 > uₙ, X_h > uₙ) / (n pₙ²) → 0`;
- `Σ_{sₙ<h<n} α(h) / (n pₙ²) → 0`.

Then `runsEstimator X n rₙ uₙ → θ` in probability. Lean:
`ExtremeValueTheory.tendstoInMeasure_runsEstimator`, `ExtremalIndexEstimators.lean:685`.

*Limit `ϑ`.* `HasSpectralTailProcess.tendstoInMeasure_blocksEstimator` (`:994`) and
`HasSpectralTailProcess.tendstoInMeasure_runsEstimator` (`:1022`): for `X : ℤ → Ω → ℝ` measurable with
shift-invariant windows (D1) and spectral tail process `Θ`, `α > 0`, `uₙ → ∞`, `rₙ → ∞`, forward
anticlustering at `(uₙ, rₙ)`, `rₙ/n → 0`, `n P(|X_0| > uₙ) → ∞`, and the conditions above for `|X|`
except the first bullet, the estimator applied to `|X|` tends to `ϑ`.

**(c) Caveats.**
1. **The limit is not identified with the extremal index.** `θ` above is only the assumed limit of the
   population ratio. Nothing in the first two theorems involves `HasExtremalIndex`. On the echo process
   the two limits differ: blocks with long blocks give `1/2`, and short runs give `1` (R16).
2. **The bridge to `θ` is not a corollary.** These theorems use levels with `n pₙ → ∞`, whereas R5 needs anticlustering and `𝒜`
   along a common block sequence at **every** level with `n pₙ → τ`. Those are different hypotheses, to
   be verified separately.
3. `rₙ → ∞` is not assumed in the first two theorems. It is needed in practice for the population ratio
   to have the intended meaning.
4. The cluster and mixing conditions are hypotheses. They are automatic for `m`-dependent sequences
   (`tendstoInMeasure_blocksEstimator_of_isMDependent`,
   `tendstoInMeasure_runsEstimator_of_isMDependent`) and verified on the logarithmic echo (R16). The
   non-vacuity tests of the first two theorems use an iid exponential sequence, and those of the limit `ϑ`
   the moving maximum (`ϑ = 1/2`). No GARCH or ARMA example is treated. The
   mixing rate is simple, not sharp.
5. No rate of convergence, and no choice of `uₙ` or `rₙ`.

**(d) Questions.**
1. Is `n pₙ → ∞` what you expect? (At `n pₙ → τ` the counts are asymptotically Poisson, so no estimator
   is consistent.)
2. Are the conditions, particularly `α(rₙ + 1) = o((rₙ pₙ)²)`, close to those of [KS20, Ch. 10], or too
   strong for your examples?

## S6. Intervals estimator: the continuous mapping step only

**(a) Literature.** [FS03, Thm 1]: under a mixing condition, `P(X_0 > uₙ) T ⇒ (1 − θ)δ₀ + θ Exp(θ)` for
inter-exceedance times `T`, which leads to `θ̂₁ = 2(Σ T_i)²/(m Σ T_i²)`.

**(b) Lean, in math.** `ferroSegersLaw θ = (1 − θ)⁺ δ₀ + θ⁺ Exp(mean 1/θ)`
(`ExtremalIndexEstimatorsIntervals.lean:61`), with first moment `1` and second moment `2/θ` for `θ > 0`
(`integral_id_ferroSegersLaw`, `integral_sq_ferroSegersLaw`). `intervalsEstimator₁ T = 2(Σ_i T_i)²/(m
Σ_i T_i²)` for `T ∈ ℝ^m`.

Let `mₙ > 0` eventually; let `Tₙ : Ω → ℝ^{mₙ}` be arbitrary; `cₙ ≠ 0` eventually; `θ > 0`. If

  `mₙ⁻¹ Σ_i cₙ Tₙ,ᵢ → ∫ x dFS(θ)` and `mₙ⁻¹ Σ_i (cₙ Tₙ,ᵢ)² → ∫ x² dFS(θ)` in probability,

then `intervalsEstimator₁ Tₙ → θ` in probability. Lean:
`ExtremeValueTheory.tendstoInMeasure_intervalsEstimator₁`, `ExtremalIndexEstimatorsIntervals.lean:164`.

**(c) Caveats.**
1. **No process, no exceedance times and no extremal index appear.** `Tₙ` are any functions, without
   even measurability. Since `θ̂₁ = 2M₁²/M₂`, this is the continuous mapping theorem plus scale
   invariance.
2. [FS03, Thm 1] and the laws of large numbers for the two moments are not formalized. Weak convergence
   would not give the second moment anyway, so the hypothesis is where the difficulty lies.
3. `θ ≤ 1` is not required. For `θ > 1`, `ferroSegersLaw θ` is not a probability measure, though the two
   integrals are unchanged.
4. Only `θ̂₁`. `intervalsEstimator₂` and the combined rule `intervalsEstimator` are defined, with no
   consistency theorem. The non-vacuity test uses iid draws from `ferroSegersLaw (1/2)`.

**(d) Questions.** 1. Should this be presented as consistency of the intervals estimator at all, or only
as its algebra?

## S7. GEV likelihood: strong consistency on a compact set

**(a) Literature.** Wald (1949); Smith (1985); Bücher–Segers (2017, Thm 2), as cited in the source.

**(b) Lean, in math.** `gevLogDensityE ξ μ σ x` is `log(σ⁻¹ h((x − μ)/σ))`, with value `−∞` where the
density is `0`; `h` is the standard GEV density, with the Gumbel density at `ξ = 0`. `ℓₙ` is the sum in
`[−∞, ∞)` over `X_0, …, X_{n−1}`. Let `K ⊂ ℝ³` be compact, with `ξ > −1` and `σ > 0` on `K`; `θ₀ = (ξ₀,
μ₀, σ₀) ∈ K`; `(X_i)` mutually independent, each with c.d.f. `gevFun ξ₀ ((x − μ₀)/σ₀)`. Then almost
surely: for every sequence `θ̂ₙ ∈ K` and every real `εₙ → 0` with `ℓₙ(θ₀) ≤ ℓₙ(θ̂ₙ) + n εₙ` eventually,
`θ̂ₙ → θ₀`.

Lean: `ExtremeValueTheory.ae_tendsto_gevMLE`, `GEVMLE.lean:607`. (Also C25.) Exact maximizers exist:
`exists_isMaxOn_gevLogLikE`.

**(c) Caveats.**
1. **The data are exactly GEV and iid.** Maxima of finite blocks from a law in a domain of attraction,
   and dependent block maxima, are not covered.
2. The null set does not depend on the estimator, and `θ̂ₙ` need not be measurable. `θ₀` need not be
   interior to `K`.
3. Consistency only in this entry; unlike S10, it also covers `ξ₀ = 0` and `ξ₀ ≤ −1/2`, down to `ξ₀ > −1`.
   Joint normality for `ξ₀ > −1/2`, `ξ₀ ≠ 0`, is S10, which uses this theorem. Likelihood over the whole
   parameter space is not proved.

**(d) Questions.** 1. See S10, question 5.

## S8. GPD likelihood: joint asymptotic normality

**(a) Literature.** Smith (1985); [Coles, §4.3.3]. See also C26.

**(b) Lean, in math.** Let `K ⊂ ℝ²` be compact, with `ξ > −1`, `σ > 0` on `K`; `(ξ₀, σ₀)` in the
interior of `K`; `ξ₀ > −1/2`, `ξ₀ ≠ 0`, `σ₀ > 0`; `(X_i)` mutually independent, each with law GPD(`ξ₀,
σ₀`); `W ~ N(0, I⁻¹)`, with `I⁻¹ = (1 + ξ₀)[[1 + ξ₀, −σ₀], [−σ₀, 2σ₀²]]` (`gpdFisherInfoInv`). Then
there are measurable maps `gₙ : ℝⁿ → ℝ²` such that for all `n` and **all** `x ∈ ℝⁿ`, `gₙ(x) ∈ K` and
`gₙ(x)` maximizes `ℓₙ(·; x)` over `K`; and `√n(gₙ(X_0, …, X_{n−1}) − (ξ₀, σ₀)) ⇒ W`.

Lean: `ExtremeValueTheory.exists_gpdMLE_tendstoInDistribution`, `GPDMLENormality.lean:246`.

*Every maximizer.* Under the same hypotheses, if `θ̂ₙ : Ω → ℝ²` is almost everywhere measurable, with
`θ̂ₙ(ω) ∈ K` a maximizer of `ℓₙ` at `(X_i(ω))_{i<n}` for all `n` and `ω`, then `√n(θ̂ₙ − (ξ₀, σ₀)) ⇒ W`.
Lean: `ExtremeValueTheory.tendstoInDistribution_gpdMLE_all`, `GPDMLENormality.lean:175`.

**(c) Caveats.**
1. The first statement's conclusion is an existence; the statement for every maximizer is the second
   theorem.
2. The maximizer property must hold for **every** `ω`, not eventually or almost surely, which is
   stronger than a theorem about laws needs, although the first theorem shows that such maximizers
   exist.
3. `ξ₀ = 0` is excluded, and so is the non-regular range `ξ₀ ≤ −1/2`. Exact GPD data only (see S3,
   caveat 1). Maximization over a compact `K` with `θ₀` in its interior.

**(d) Questions.** 1. See C26. 2. Would a statement for near-maximizers, or local roots, be more useful?

## S9. GARCH(1,1) squared volatility: tail exponent and two-sided tail bounds

**(a) Literature.** Nelson (1990); Bougerol–Picard (1992); Mikosch–Stărică (2000); [BDM16, Thm 4.3.1];
Kesten (1973), Goldie (1991): under standard conditions, `P(σ² > x) ~ c x^{−κ}`, where `E(α₁Z² + β₁)^κ =
1`.

**(b) Lean, in math.** Let `Z ~ ζ`, `ζ` a probability measure on `ℝ`, and `A = α₁Z² + β₁`
(`SRE.GARCH.coeff`). `stationaryLaw (coeffLaw α₀ α₁ β₁ ζ)` is the law of `Σ_{k≥0} A_0 ⋯ A_{k−1} α₀`,
with `(A_i)` iid (`Dependence/SRE.lean:256`).

*Existence of `κ`.* Let `α₁ ≥ 0`, `β₁ ≥ 0`, `log A` integrable, `E log A < 0`, `A ≠ 0` a.s., `S > 0`,
`A^S` integrable, `E A^S > 1`. Then there is `κ ∈ (0, S)` with `A^κ` integrable and `E A^κ = 1`. Lean:
`ExtremeValueTheory.SRE.GARCH.exists_tail_index`, `Dependence/SREGarch.lean:223`. Uniqueness:
`SRE.kesten_exponent_unique` (when `A` is not a.s. `1`).

*Tail bounds.* Let `α₁ ≥ 0`, `β₁ ≥ 0`, `log A` integrable, `E log A < 0`, `α₀ > 0`, `κ > 0`, `A^κ`
integrable, `E A^κ = 1`, and not `A = 1` a.s. With `Y` having the stationary law:
1. for every `s ∈ (0, κ)` there is `C ≥ 0` with `P(|Y| > x) ≤ C x^{−s}` for all `x > 0`;
2. for every `s > κ` there are **no** `C ≥ 0` and `x₀ > 0` with `P(|Y| > x) ≤ C x^{−s}` for all `x ≥
   x₀`.

Lean: `ExtremeValueTheory.SRE.GARCH.tail_bounds`, `Dependence/SREGarch.lean:198`.

**(c) Caveats.**
1. **`κ` is an exponent, not a proved regular-variation index.** The sharp Kesten–Goldie asymptotics `c
   x^{−κ}` is not proved, nor regular variation of the tail, nor anything at `s = κ`. Part 2 only gives
   that the tail is not `O(x^{−s})`.
2. It concerns the stationary squared volatility `σ²`, not the returns `X_t = σ_t Z_t`. No tail for
   `X_t`, no tail process and no extremal index of GARCH are proved.
3. `log 0 = 0` in Lean, so `E log A < 0` is stronger than the textbook condition when `P(A = 0) > 0`
   (`FAITHFULNESS.md`).
4. Non-vacuity: a two-point `Z` (values `1/3` and `2`) with `α₁ = 1`, `β₁ = 0`, i.e. ARCH(1) with `S = 1`;
   and `test_nonvacuous_garch_gaussian`: `Z ~ N(0, 1)`, `α₁ = 7/10`, `β₁ = 1/5`, `S = 2`, where `E A² =
   179/100`. That is one parameter pair; `E A^S > 1` is not derived for Gaussian `Z` in general.

**(d) Questions.** 1. Without Kesten–Goldie, is the name "tail index" misleading? 2. Is the two-sided
bound useful to you?

## S10. GEV likelihood: joint asymptotic normality ★

**In one paragraph.** This is the theorem behind the standard errors of a GEV fit. It is proved for an
exact iid GEV sample, with `ξ₀ > −1/2`, `ξ₀ ≠ 0`, and maximizers over a compact set `K` with the truth in
its interior. Block maxima from a law that is merely in a domain of attraction are **not** covered: that
is the case a practitioner actually has.

**(a) Literature.** Smith, Biometrika 72 (1985); Prescott–Walden, Biometrika 67 (1980), for the
information matrix; Bücher–Segers, Extremes 20 (2017); [Coles, §3.3.3]. No theorem numbers were checked.
For iid data from `GEV(ξ₀, μ₀, σ₀)` in the regular range `ξ₀ > −1/2`, `√n(θ̂ₙ − θ₀) ⇒ N(0, I(θ₀)⁻¹)`.

**(b) Lean, in math.** Data and likelihood are those of S7: `gevLocScaleCDF ξ μ σ` is the law with c.d.f.
`gevFun ξ ((x − μ)/σ)`; `ℓₙ(θ; x) = gevLogLikE` is the sum in `[−∞, ∞)` of `log(σ⁻¹ h((xᵢ − μ)/σ))`, with
value `−∞` where the density `h` vanishes. Points of `ℝ³` are written `(ξ, μ, σ)`.

*The information matrix.* `gevFisherInfo ξ σ` (`GEVFisherInformation.lean:522`) is, **in the order
`(μ, σ, ξ)`**, the symmetric matrix with

  `I_μμ = p/σ²`,  `I_μσ = (Γ(2 + ξ) − p)/(ξ σ²)`,  `I_σσ = (1 − 2Γ(2 + ξ) + p)/(ξ² σ²)`,

  `I_μξ = −(q − p/ξ)/(σ ξ)`,  `I_σξ = −(1 − γ_E + (1 − Γ(2 + ξ))/ξ − q + p/ξ)/(σ ξ²)`,

  `I_ξξ = (π²/6 + (1 − γ_E + 1/ξ)² − 2q/ξ + p/ξ²)/ξ²`,

where `p = (1 + ξ)² Γ(1 + 2ξ)` (`gevInfoP`), `q = Γ(2 + ξ)(ψ(1 + ξ) + (1 + ξ)/ξ)` (`gevInfoQ`),
`ψ = Γ'/Γ` (`realDigamma`), and `γ_E` is Euler's constant. For `σ > 0`, `ξ ≠ 0`, `ξ > −1/2`, it is proved
that this is the covariance of the score, `E[∂_i ℓ ∂_j ℓ] = I_ij` (`integral_gevScore_mul_gevScore`,
`:718`), minus the expected Hessian (`integral_gevHess_eq_neg_gevFisherInfo`, `GEVHessian.lean:527`), and
positive definite (`posDef_gevFisherInfo`, `:808`).

*The covariance.* `gevMLECov ξ σ` (`GEVMLENormality.lean:575`) is `I⁻¹` with rows and columns rearranged
to **the order `(ξ, μ, σ)`**: writing `J = (gevFisherInfo ξ σ)⁻¹` in the order `(μ, σ, ξ)`,

  `gevMLECov = [[J_ξξ, J_ξμ, J_ξσ], [J_μξ, J_μμ, J_μσ], [J_σξ, J_σμ, J_σσ]]`.

*The theorem.* Let `K ⊂ ℝ³` be compact, with `ξ > −1` and `σ > 0` on `K`; `θ₀ = (ξ₀, μ₀, σ₀)` in the
interior of `K`; `−1/2 < ξ₀`, `ξ₀ ≠ 0`, `σ₀ > 0`; `(X_i)` mutually independent, each with law
`gevLocScaleCDF ξ₀ μ₀ σ₀`; `θ̂ₙ : Ω → ℝ³` almost everywhere measurable, with `θ̂ₙ(ω) ∈ K` and `θ̂ₙ(ω)` a
maximizer over `K` of `ℓₙ(·; X_0(ω), …, X_{n−1}(ω))`, for **all** `n` and `ω`; and `W` on another
probability space, with law `N(0, gevMLECov ξ₀ σ₀)`. Then

  `√n(ξ̂ₙ − ξ₀, μ̂ₙ − μ₀, σ̂ₙ − σ₀) ⇒ W`.

Lean: `ExtremeValueTheory.tendstoInDistribution_gevMLE`, `GEVMLENormality.lean:775`. The same in the
order `(μ, σ, ξ)`, with limit `N(0, I⁻¹)`: `tendstoInDistribution_gevMLE_muSigmaXi` (`:792`).

*Existence.* Under the same hypotheses on `K`, `θ₀`, `X` and `W`, there are measurable `gₙ : ℝⁿ → ℝ³`
such that, for all `n` and **all** `x ∈ ℝⁿ`, `gₙ(x) ∈ K` and `gₙ(x)` maximizes `ℓₙ(·; x)` over `K`; and
`√n(gₙ(X_0, …, X_{n−1}) − θ₀) ⇒ W`. Lean: `ExtremeValueTheory.exists_gevMLE_tendstoInDistribution`,
`GEVMLENormality.lean:834`.

*Local maximizers, no `K`.* Let `−1/2 < ξ₀`, `ξ₀ ≠ 0`, `σ₀ > 0`, `(X_i)` and `W` as above, and let `θ̂ₙ`
be almost everywhere measurable, such that:
- almost surely, `θ̂ₙ → θ₀` (strong consistency is a hypothesis);
- almost surely, for all large `n`, `θ̂ₙ` is a local maximizer of `ℓₙ(·; X_0, …, X_{n−1})` on `ℝ³`;
- almost surely, for all large `n` and all `i < n`, `1 + ξ̂ₙ (X_i − μ̂ₙ)/σ̂ₙ > 0` (`gevU`).

Then `√n(ξ̂ₙ − ξ₀, μ̂ₙ − μ₀, σ̂ₙ − σ₀) ⇒ W`. Lean:
`ExtremeValueTheory.tendstoInDistribution_gevLocalMLE`, `GEVMLENormality.lean:691`.

**(c) Caveats.**
1. **Exact GEV data.** The `X_i` are iid with exactly a GEV law. Maxima of finite blocks from a law in a
   domain of attraction, with the resulting bias, and dependent block maxima, are not covered.
2. **`ξ₀ = 0` is excluded**, although `K` may contain points with `ξ = 0` (the test's `K` does): the
   excluded thing is a true Gumbel law. The scores and `gevFisherInfo` have `ξ` in denominators, and
   their limit at `ξ = 0` is not formalized. For `ξ₀ = 0`, S7 gives consistency only.
3. **`ξ₀ ≤ −1/2` is excluded**: the boundary, and the nonregular case `−1 < ξ₀ < −1/2`, where the rate is
   not `√n`. `K` itself may extend below `−1/2`, and only `ξ > −1` is required on it.
4. **Compact `K`, truth in the interior.** The global statement is about maximizers over `K`, not over
   the whole parameter space. In the local statement, consistency is assumed, and the existence of a
   consistent sequence of local maximizers without a compact `K` is not formalized. So the only
   unconditional statement is the one over `K`. The local theorem has no test of its own; it is exercised
   through the global one, which it implies. The third local hypothesis is needed: at a parameter where
   some observation is off the support, `ℓₙ = −∞`, and if that holds on a neighbourhood the point is
   trivially a "local maximizer".
5. **Every `ω`.** The maximizer property is required for all `n` and all `ω`, not almost surely. This is
   stronger than a statement about laws needs, but it is satisfiable, by `exists_measurable_gevMLE`.
6. **No closed form for the covariance.** `⁻¹` is Mathlib's matrix inverse, which is junk `0` for a
   singular matrix; positive definiteness rules that out under the hypotheses. No entry of `J` is written
   out.
7. **Order.** `I` is `(μ, σ, ξ)`; `gevMLECov` and the theorem are `(ξ, μ, σ)`. The permutation is checked
   by an `example` at the end of `Test/NonVacuity/StatisticsLikelihood.lean`, with the entries `ξξ`,
   `μμ`, `σσ` and `ξμ`.
8. **What was tested, and what was not.** `test_nonvacuous_exists_gevMLE_tendstoInDistribution_pos`
   (`ξ₀ = 1/4`, `μ₀ = 1/2`, `σ₀ = 3/2`, `K = [−1/2, 1/2] × [0, 1] × [1, 2]`) and
   `test_nonvacuous_exists_gevMLE_tendstoInDistribution_neg` (`ξ₀ = −2/5`) discharge all hypotheses. **No
   Lean test compares the full matrix with a number from outside.** `test_gevFisherInfoMuSigma` covers
   the `2 × 2` block, and `test_gevReturnLevelVariance_portPirie` uses Coles' covariance, not
   `gevMLECov`. As an informal check outside the repository, in floating point: the closed form agrees
   with a finite-difference Fisher information of the density, to relative error `5 × 10⁻⁵` or better, at
   `(ξ, σ) = (1/4, 3/2), (1/10, 1), (−1/20, 0.198), (−1/5, 2)`. At Coles' Port Pirie estimates
   (`ξ = −0.05`, `σ = 0.198`, `n = 65`), `I⁻¹/n` has variances `0.000747, 0.000379, 0.00674` for
   `(μ, σ, ξ)`, and covariances with the same signs as his matrix (as copied in
   `Test/KnownAnswers/ReturnLevels.lean`), whose variances are `0.000780, 0.000410, 0.00965`. Coles uses
   observed information, which may explain the `30%` gap on `ξ` at `n = 65`, but we have not shown that
   it does.
9. Nothing here is about estimating `I` from data: no plug-in `I(θ̂ₙ)`, no Wald interval for the
   parameters. The convergence is at a fixed `θ₀`, and is not uniform.

**(d) Questions.**
1. **Fisher information.** Is the matrix above the one of Prescott–Walden (1980), entry by entry? As we
   recall, they parametrize by `k = −ξ`, so the signs of `I_μξ` and `I_σξ` deserve attention. The source
   cites the paper, which was not checked. Since the matrix is proved equal to the covariance of the
   score, an error here would be in the citation, or in the score, not in the algebra.
2. **Covariance order.** Do you agree with the order of the limit, `(ξ, μ, σ)`, against `(μ, σ, ξ)` for
   the matrix? Does a statement with two orders invite a mistake that a single order would avoid?
3. **Smith's regularity range.** Is `ξ₀ > −1/2` with the rate `√n` exactly Smith's regular case, under
   the translation of his shape to `ξ`? Is anything in his hypotheses missed by this statement, or does
   it matter that `K` may extend into `(−1, −1/2]`?
4. **Form.** Is "maximizers over a compact `K` with the truth in its interior" a form you would cite, or
   do you need the local-root form without assuming consistency? What does Bücher–Segers (2017) state
   exactly?
5. **The main gaps.** Which matters most: `ξ₀ = 0`, or block maxima from a domain of attraction, and what
   form of theorem would you want for the latter?

## S11. GEV return levels: unconditional normality for the maximum likelihood estimator

**(a) Literature.** [Coles, §3.3.3]; Smith (1985). `√n(ẑ_m − z_m) ⇒ N(0, ∇zᵀV∇z)`, with `V` the
asymptotic covariance of the maximum likelihood estimator, and the interval `ẑ_m ± z ŝ/√n`.

**(b) Lean, in math.** `gevReturnLevel` and `gevReturnLevelGrad` are as in S2, in the order `(ξ, μ, σ)`,
the same as `gevMLECov`. Define `gevReturnLevelVar ξ σ m = ∇zᵀ (gevMLECov ξ σ) ∇z`, with
`∇z = gevReturnLevelGrad ξ σ m = (σ ∂_ξ h_ξ(1/y_m), 1, r(ξ, m))` (`GEVReturnLevelNormality.lean:58`). It
is positive for `σ > 0`, `ξ ≠ 0`, `ξ > −1/2` and every real `m` (`gevReturnLevelVar_pos`), since the `μ`
component of `∇z` is `1`.

*Normality.* Let `K`, `θ₀`, `(X_i)` and `θ̂ₙ` be exactly as in S10; let `m > 1`, and let `W` be on
another probability space, with law `N(0, gevReturnLevelVar ξ₀ σ₀ m)`. Then

  `√n(gevReturnLevel θ̂ₙ m − gevReturnLevel θ₀ m) ⇒ W`.

Lean: `ExtremeValueTheory.tendstoInDistribution_gevMLEReturnLevel`, `GEVReturnLevelNormality.lean:105`.
With existence of the estimator: `exists_gevMLE_returnLevel_tendstoInDistribution`. For consistent local
maximizers, under the hypotheses of the local theorem of S10:
`tendstoInDistribution_gevLocalMLEReturnLevel`.

*Interval.* Let `K`, `θ₀`, `(X_i)`, `θ̂ₙ` and `m` be as above. **Let `Sₙ : Ω → ℝ` be almost everywhere
measurable, with `Sₙ → √(gevReturnLevelVar ξ₀ σ₀ m)` in probability.** Let `z` be any real number. Then

  `P(z_m ∈ [ẑ_m − z Sₙ/√n, ẑ_m + z Sₙ/√n]) → N(0, 1)[−z, z]`,

where `z_m = gevReturnLevel θ₀ m` and `ẑ_m = gevReturnLevel θ̂ₙ m`. Lean:
`ExtremeValueTheory.tendsto_measure_mem_gevMLEReturnLevelInterval`, `GEVReturnLevelNormality.lean:147`.

**(c) Caveats.**
1. All the caveats of S10 apply: this is S10 plus the delta method (S1).
2. **The consistency of the standard error is an assumption.** `Sₙ` is any measurable sequence with the
   right limit in probability. **No estimator is shown to satisfy it**: the plug-in
   `√(gevReturnLevelVar θ̂ₙ m)` needs the continuity of `gevFisherInfo` in the parameters, which is not
   formalized. The non-vacuity test (`test_nonvacuous_tendsto_measure_mem_gevMLEReturnLevelInterval`)
   takes `Sₙ` to be the true value, a constant that a statistician does not know. So, unlike S4 for the
   GPD, this theorem does **not** yet justify any computable interval.
3. `m > 1` is fixed as `n → ∞`, where `n` is the number of blocks. Extrapolation with `m = mₙ → ∞` is not
   covered. Block size does not appear: the data are exact GEV.
4. `ξ₀ = 0` is out of scope (S2 has only the delta method there). Symmetric Wald form only; there are no
   profile-likelihood sets for the GEV. The profile sets of S12 are for the GPD.
5. Non-vacuity: `test_nonvacuous_exists_gevMLE_returnLevel` (`ξ₀ = 1/4`, `m = 100`).

**(d) Questions.**
1. Is the plug-in standard error, or the profile likelihood, the more valuable thing to add?
2. Does the fact that `√n` counts blocks and `m` is fixed match how you read Coles' statement?

## S12. Wilks' theorem and profile likelihood for the GPD, `ξ₀ > 0`

**(a) Literature.** [Coles, §2.6.5–2.6.6, §4.3.3]; [vdV, §16]. The deviance at the true parameter is
asymptotically `χ²_d`, and the profile deviance `χ²_1`. The set `{ψ : D_p(ψ) ≤ c}` is the
profile-likelihood interval, usually preferred to Wald for return levels. These hold in the regular case,
`ξ₀ > −1/2`.

**(b) Lean, in math.** `chiSquared k` (`ForMathlib/Probability/ChiSquared.lean:48`) is the law of `‖Z‖²`,
`Z` standard Gaussian in `ℝᵏ`. `gpdLogLikE` is `ℓₙ` of II.9, valued in `[−∞, ∞)`.
`gpdLogLikN ξ σ x n = Σ_{i<n} log gpdDensity ξ σ (x_i)` is real-valued, with the junk `log 0 = 0` off the
support.

Throughout, *hypotheses (W)*: `K ⊂ ℝ²` compact, with `ξ > −1`, `σ > 0` on `K`; `(ξ₀, σ₀)` in the interior
of `K`; **`ξ₀ > 0`**, `σ₀ > 0`; `(X_i)` mutually independent, each with law GPD(`ξ₀, σ₀`).

*Wilks.* Assume (W). Let `θ̂ₙ : Ω → ℝ²` be almost everywhere measurable, with `θ̂ₙ(ω) ∈ K` a maximizer
over `K` of `gpdLogLikE(·; X_0(ω), …, X_{n−1}(ω))`, for all `n` and `ω`, and let `Z` have law
`chiSquared 2`. Then

  `2(gpdLogLikN θ̂ₙ X n − gpdLogLikN (ξ₀, σ₀) X n) ⇒ Z`.

Lean: `ExtremeValueTheory.tendstoInDistribution_gpdDeviance`, `GPDWilks/Profile.lean:309`.

*Chart.* `IsGPDProfileChart g ξ₀ σ₀ s₀ φ γ₁ γ₂ t₁ t₂` (`GPDWilks/Profile.lean:330`), with `g, φ : ℝ² → ℝ`
and `γ₁, γ₂, t₁, t₂ : ℝ → ℝ`, means: `φ(ξ₀, σ₀) = s₀`; `φ` is continuous at `(ξ₀, σ₀)`; for `p` near
`(ξ₀, σ₀)`, if `g(p) = g(ξ₀, σ₀)` then `(γ₁, γ₂)(φ(p)) = p`; for `s` near `s₀`,
`g(γ₁(s), γ₂(s)) = g(ξ₀, σ₀)`; for `s` near `s₀`, `γ₁` and `γ₂` are differentiable at `s`, with
derivatives `t₁(s)`, `t₂(s)`; `t₁`, `t₂` are continuous at `s₀`; and `(t₁(s₀), t₂(s₀)) ≠ 0`. Three are
constructed: the shape (`isGPDProfileChart_shape`, `g(ξ, σ) = ξ`), the scale (`isGPDProfileChart_scale`,
`g(ξ, σ) = σ`), and, for `ξ₀ ≠ 0` and `Nζ > 1`, the return level (`isGPDProfileChart_returnLevel`,
`g = gpdReturnLevel u · · ζ N`, curve `s ↦ (s, σ₀ h_{ξ₀}(Nζ)/h_s(Nζ))`).

*Profile Wilks.* Assume (W), let `g` be continuous on `K` with a chart as above, and let `θ̂ₙ` be as in
Wilks. Let `θ̃ₙ : Ω → ℝ²` be almost everywhere measurable, with `θ̃ₙ(ω) ∈ K ∩ {g = g(ξ₀, σ₀)}` a
maximizer of `gpdLogLikE` over that set, for all `n` and `ω`, and let `Z` have law `chiSquared 1`. Then

  `2(gpdLogLikN θ̂ₙ X n − gpdLogLikN θ̃ₙ X n) ⇒ Z`.

Lean: `ExtremeValueTheory.tendstoInDistribution_gpdProfileDeviance`, `GPDWilks/Profile.lean:436`.

*The sets, defined from data.* For `x ∈ ℝⁿ`, `gpdMaxLogLik K x = sup_{p∈K} gpdLogLikE(p; x)`, in
`[−∞, ∞]`, with `sup ∅ = −∞`, and `gpdProfileLogLik K g ψ x = gpdMaxLogLik (K ∩ {g = ψ}) x`. Then, for
real `c`:

  `gpdProfileInterval K g c x = {ψ ∈ ℝ : −∞ < sup_K ℓ < ∞ and 2(sup_K ℓ − ℓ_p(ψ)) ≤ c}`
  (`GPDWilks/Coverage.lean:66`),

  `gpdDevianceRegion K c x = {θ ∈ K : −∞ < sup_K ℓ < ∞ and 2(sup_K ℓ − ℓ(θ)) ≤ c}` (`Coverage.lean:76`).

Differences are in `[−∞, ∞]`, so a `ψ` not attained on `K` has `ℓ_p(ψ) = −∞`, deviance `+∞`, and is
excluded.

*Coverage.* Assume (W), and let `c` be any real number. Then:
- for `g`, continuous on `K` with a chart: `P(g(ξ₀, σ₀) ∈ gpdProfileInterval K g c X) → χ²₁((−∞, c])`
  (`tendsto_measure_mem_gpdProfileInterval`, `Coverage.lean:145`);
- for the shape: `P(ξ₀ ∈ gpdProfileInterval K fst c X) → χ²₁((−∞, c])`
  (`tendsto_measure_mem_gpdShapeProfileInterval`, `Coverage.lean:204`), and likewise for the scale
  (`tendsto_measure_mem_gpdScaleProfileInterval`, `:215`);
- for the POT return level, with `u, ζ, N` real and `Nζ > 1`:
  `P(gpdReturnLevel u ξ₀ σ₀ ζ N ∈ gpdProfileInterval K (p ↦ gpdReturnLevel u p ζ N) c X) → χ²₁((−∞, c])`
  (`ExtremeValueTheory.tendsto_measure_mem_gpdReturnLevelProfileInterval`, `Coverage.lean:229`);
- for the full parameter: `P((ξ₀, σ₀) ∈ gpdDevianceRegion K c X) → χ²₂((−∞, c])`
  (`tendsto_measure_mem_gpdDevianceRegion`, `:247`).

No estimator appears in the coverage statements. Level forms: for `α ∈ (0, 1)` there is `c > 0` with
`χ²₁((−∞, c]) = 1 − α` (`exists_tendsto_measure_mem_gpdProfileInterval`), and `c = −2 log α` for the
region (`tendsto_measure_mem_gpdDevianceRegion_of_alpha`).

**(c) Caveats.**
1. **`ξ₀ > 0` only.** This is narrower than S8 and the literature, which have `ξ₀ > −1/2`. For every `ξ`
   near `ξ₀ > 0`, the support is `[0, ∞)`, so the moving endpoint, which is the difficult part of S10,
   does not arise. The case `−1/2 < ξ₀ < 0`, and `ξ₀ = 0`, are not covered. There is no Wilks theorem for
   the GEV.
2. **Exact GPD data.** All of S3, caveat 1: exact iid GPD excesses, deterministic `n`, with `u` and `ζ`
   known constants.
3. **Confidence sets, not shown to be intervals.** Despite the name `gpdProfileInterval`, nothing proves
   that the set is an interval, that the profile likelihood is unimodal, or that the set is asymmetric.
   The docstring of the return-level theorem says the set "can be asymmetric": that is a remark, not a
   theorem.
4. **A chart, not a smooth `g`.** The implicit function theorem step is not formalized, so a new interest
   parameter needs a new chart. `g` itself need not be differentiable, and a nonzero gradient is not a
   hypothesis.
5. **Two likelihoods.** The maximizers are of `gpdLogLikE`, and the deviance limits are stated with the
   real-valued `gpdLogLikN`. On data in the support of `(ξ₀, σ₀)`, `ξ₀ > 0`, a maximizer has finite
   likelihood, so the two agree; the coverage proofs establish this. The sets are stated with
   `gpdLogLikE`.
6. **A definition that was wrong.** `gpdProfileInterval` was all of `ℝ` for an empty `K`, or a sample
   impossible on `K`, because `⊥ − ⊥ = ⊥` in `EReal`, and `gpdDevianceRegion` contained points outside
   `K`. An independent review found this; the eighth audit records it, and both now have the finiteness
   conditions and membership in `K` shown above. The coverage theorems were not affected. Tests:
   `test_gpdProfileInterval_empty`, `test_gpdProfileInterval_of_neg`,
   `test_gpdProfileInterval_beyond_endpoint`, `test_gpdDevianceRegion_subset`.
7. **The sets depend on `K`.** They lie in `g(K)` or in `K`, so in a finite sample a set can be cut off
   at the boundary of `K`. Coverage is at a fixed parameter, not uniform.
8. **Critical values.** `χ²₁` quantiles exist (`exists_chiSquared_one_Iic_eq`), but no numerical value
   such as `3.84` is in these statements. `tendsto_measure_le_of_noAtoms` is used with no-atom instances
   for `k = 1, 2` only.
9. Non-vacuity (`Test/NonVacuity/ProfileLikelihood.lean`): iid GPD(`1/4, 3/2`),
   `K = [1/8, 1/2] × [1, 2]`, for the deviance, the shape, the scale, the region, and the return level at
   `u = 5`, `ζ = 1/2`, `N = 10`. The profile deviance theorem itself is exercised through the coverage
   theorems. `test_gpdDeviance_singleton` checks the deviance at the MLE of a one-point model.

**(d) Questions.**
1. How much is lost for you by `ξ₀ > 0`? Is `−1/2 < ξ₀ < 0` the case that matters, for bounded tails?
2. Is the definition of the set, with `sup_K ℓ` and `ℓ_p(ψ)` both over the compact `K`, the one you would
   use? Should empty and infinite cases be treated otherwise?
3. Is a chart an acceptable substitute for "smooth with nonzero gradient"?
4. Would you want a proof that the set is an interval, under what condition on the likelihood, or do you
   regard it as a side issue?

## S13. Pickands estimator: asymptotic normality

**(a) Literature.** Pickands (1975); Dekkers–de Haan, Ann. Statist. 17 (1989); [dHF, Thm 3.3.5] (not
checked against the book). `√k(γ̂_P − γ) ⇒ N(λ b_{γ,ρ}, σ²_γ)`, under a second-order condition with
`√k A(n/k) → λ`.

**(b) Lean, in math.**
`γ̂_P = pickands x k = (log 2)⁻¹ log((X_{(k+1)} − X_{(2k+1)})/(X_{(2k+1)} − X_{(4k+1)}))`, with
`X_{(j+1)}` the `(j+1)`-th largest of `x` (`orderStat x j`; junk `0` if `j ≥ n`) (`Pickands.lean:59`).
`U = survivalQuantile (survival P X_0)`: `U(t) = inf{x : P(X_0 > x) ≤ 1/t}` for `t > 1`, and `0`
otherwise. `D_γ = boxCox γ`.

*Second-order condition.* `extSecondOrderLimit γ ρ x = H_{γ,ρ}(x) = ∫_1^x s^{γ−1} D_ρ(s) ds`
(`PickandsNormality.lean:399`). `IsExtSecondOrderRegularlyVarying U γ ρ a A`
(`PickandsNormality.lean:415`) means: `a(t) > 0` eventually; `A(t) → 0`; `A(t) ≠ 0` eventually; and

  `((U(xt) − U(t))/a(t) − D_γ(x))/A(t) → H_{γ,ρ}(x)` as `t → ∞`, **locally uniformly** in `x ∈ (0, ∞)`.

*Constants.* `pickandsVariance γ = (2 · 2^{2γ} + 1)/(4 D_γ(2)² (log 2)²)` (`PickandsNormality.lean:804`),
which is `γ²(2^{2γ+1} + 1)/(2(2^γ − 1) log 2)²` for `γ ≠ 0` (`pickandsVariance_of_ne`), and
`3/(4 (log 2)⁴)` for `γ = 0` (`pickandsVariance_zero`).

`pickandsBias γ ρ = (log 2)⁻¹ [(H(1) − H(1/2))/(D_γ(1) − D_γ(1/2)) − (H(1/2) − H(1/4))/(D_γ(1/2) − D_γ(1/4))]`
(`PickandsNormality.lean:631`), which is `D_{γ+ρ}(2)/D_γ(2) · 2^{−ρ}(1 − 2^{−ρ})/(ρ log 2)` for `ρ ≠ 0`
(`pickandsBias_of_ne`), and `1` for `ρ = 0` (`pickandsBias_zero_right`).

*The theorem.* Let `X_i` be measurable, mutually independent and identically distributed; `γ, ρ, λ` real;
`a, A` with `IsExtSecondOrderRegularlyVarying U γ ρ a A`; `kₙ ∈ ℕ`, `kₙ → ∞`, `kₙ/n → 0`,
`√kₙ A(n/kₙ) → λ`; and `Z` on another probability space with law
`N(λ pickandsBias γ ρ, pickandsVariance γ)`. Then

  `√kₙ (γ̂_P − γ) ⇒ Z`.

Lean: `ExtremeValueTheory.tendstoInDistribution_pickands`, `PickandsNormality.lean:1058`. For `λ = 0`:
`tendstoInDistribution_pickands_of_tendsto_zero`.

**(c) Caveats.**
1. **Uniformity is assumed.** According to the Lean source, [dHF, Def 2.3.1] is pointwise in `x`, and
   uniformity is a theorem there. That implication is not formalized, so this hypothesis is formally
   stronger.
2. **Indexing.** `k` is the **smallest** of the three indices, and it is the `k` in `√k` and in `A(n/k)`.
   If instead the largest index is called `K = 4k`, then on paper the variance is multiplied by `4`, and
   if `|A|` is regularly varying of index `ρ`, the mean becomes `λ_K 4^ρ b_{γ,ρ}`, with
   `λ_K = lim √K A(n/K)`. This translation is a remark in the source, not a theorem, and nor is the
   version with `⌊K/4⌋, ⌊K/2⌋, K`. The Lean docstrings attribute the closed form of the variance to [dHF,
   Thm 3.3.5]. The book was not available, so if it indexes by the largest order statistic, that
   attribution needs the factor just described.
3. **The definition has less in it than the textbook.** `ρ` is an unconstrained real, and neither a
   constant sign of `A` nor regular variation of `|A|` is assumed or used. According to the Lean source,
   the book assumes the sign, and concludes `ρ ≤ 0` and the regular variation ([dHF, Thm 2.3.3]). The
   limit is exactly `H_{γ,ρ}`, with no free constants, which fixes the normalization of `a` and `A`.
4. **Exact GPD data do not satisfy it.** If `U = D_γ` then
   `(U(xt) − U(t))/a(t) − D_γ(x) = (t^γ/a(t) − 1) D_γ(x)`, so the limit would be a multiple of `D_γ`, and
   `H_{γ,ρ}` is not. This is our own remark, not a theorem in the library. The second-order framework is
   the same as in the book; it just means the theorem says nothing for a sample with no second-order
   term.
5. Junk: order statistics with `4k ≥ n`, and `log` of a nonpositive ratio or of `0`, occur on events of
   vanishing probability. `k` is a deterministic sequence; no choice of `k` from data.
6. Non-vacuity: for every `γ`, the model `U = D_γ + D_{γ−1}`, with `kₙ = ⌊√n⌋` and `λ = 0`
   (`test_nonvacuous_tendstoInDistribution_pickands`), and `kₙ = ⌊n^{2/3}⌋` and `λ = −1`
   (`test_nonvacuous_tendstoInDistribution_pickands_bias`). `isExtSecondOrderRegularlyVarying_add_boxCox`
   proves the hypothesis for `U = D_γ + c D_{γ+ρ}`, `ρ < 0`, `c > 0`. No named law other than this model
   is verified.

**(d) Questions.**
1. **Locally uniform.** Is assuming locally uniform convergence acceptable? Could any law of interest
   satisfy the pointwise condition, but fail the uniform one in a way that matters?
2. **Indexing.** Is `k, 2k, 4k`, with `√k` and `A(n/k)` at the smallest index, consistent with your
   source? In particular, which index does [dHF, Thm 3.3.5] use, and does its variance match
   `γ²(2^{2γ+1} + 1)/(2(2^γ − 1) log 2)²` at that index?
3. Is `H_{γ,ρ}`, with exactly this normalization, the form in your source, or does your source's bias
   differ by a constant from `b_{γ,ρ}` for that reason?

## S14. Moment estimator: asymptotic normality, `γ > 0`, ratio form

**(a) Literature.** Dekkers–Einmahl–de Haan (1989); [dHF, Thm 3.5.4] (not checked against the book). For
`γ > 0`, `√k(γ̂_M − γ) ⇒ N(λ (γ − γρ + ρ)/(γ(1 − ρ)²), 1 + γ²)`.

**(b) Lean, in math.** `γ̂_M = momentEstimator x k = M₁ + 1 − ½(1 − M₁²/M₂)⁻¹`, with
`M_j = k⁻¹ Σ_{i<k} (log X_{(i+1)} − log X_{(k+1)})^j` (`Moment.lean:77`). `U` is as in S13.
`IsSecondOrderRegularlyVarying U γ ρ A` (`RegularVariation/SecondOrder.lean:96`) is the **ratio form**:
`U(t) > 0` eventually; `ρ ≤ 0`; `A(t) → 0`; `A` of eventually constant sign; `|A|` regularly varying with
index `ρ`; and for every `x > 0`,

  `(U(xt)/U(t) − x^γ)/A(t) → x^γ D_ρ(x)` as `t → ∞`.

`momentBias γ ρ = (γ − γρ + ρ)/(γ(1 − ρ)²)` (`MomentNormality.lean:394`).

Let `X_i` be measurable, mutually independent and identically distributed; **`γ > 0`**; `ρ, λ` real;
`IsSecondOrderRegularlyVarying U γ ρ A`; `kₙ → ∞`, `kₙ/n → 0`, `√kₙ A(n/kₙ) → λ`; and `Z` on another
probability space with law `N(λ momentBias γ ρ, 1 + γ²)`. Then

  `√kₙ (γ̂_M − γ) ⇒ Z`.

Lean: `ExtremeValueTheory.tendstoInDistribution_momentEstimator`, `MomentNormality.lean:766`.

**(c) Caveats.**
1. **`γ > 0` only.** `γ ≤ 0`, where the estimator is chiefly of interest, is not proved. C14 has
   consistency for every `γ`, but there is no normality outside `γ > 0`. Pickands normality (S13) does
   cover every `γ`.
2. **The ratio form.** The textbook states its condition through `(U(xt) − U(t))/a(t)`. The two have
   different auxiliary functions, so `λ` and `momentBias` here are those of the ratio form, not stated in
   terms of the textbook's `A`. The translation is not formalized.
3. As in C13, `|A| ∈ RV_ρ` and constant sign are in the definition, and exact Pareto data do not satisfy
   it (S4, caveat 2).
4. Non-vacuity: `test_nonvacuous_tendstoInDistribution_momentEstimator`: shifted Pareto, `γ = 1`,
   `ρ = −1`, `kₙ = ⌊√n⌋`, `λ = 0`, through `tendstoInDistribution_momentEstimator_of_tendsto_zero`. The
   bias term has no test of its own.

**(d) Questions.**
1. Does `momentBias` agree with [dHF, Thm 3.5.4] at `γ > 0` once the two auxiliary functions are related,
   and how are they related?
2. How much is `γ ≤ 0` worth to you, compared with what S13 gives there?

## S15. Nonparametric tail dependence: consistency of the rank-based estimators

**(a) Literature.** Huang (1992); Drees–Huang, JMVA 64 (1998); [dHF, §7.2];
Beirlant–Goegebeur–Segers–Teugels, *Statistics of Extremes* (2004), §8.2.2, §9.4.1. The empirical stable
tail dependence function is consistent for `k → ∞`, `k/n → 0`.

**(b) Lean, in math.** Throughout `ι` is a finite type, and `X_i : Ω → ℝ^ι`. Files:
`Statistics/StableTailDependence.lean`, `Multivariate/StableTailDependence.lean`.

*The empirical function* (`Statistics/StableTailDependence.lean:94–106`). With ranks
`R_i^j = #{m < n : X_m^j ≤ X_i^j}`,

  `ℓ̂ₙ(x) = empiricalStableTailDependence X n k x = k⁻¹ #{i < n : R_i^j > n − k x_j for some j}`.

The comparison is in `ℝ`, and `k⁻¹ = 0` at `k = 0`. Equivalently (`empiricalTailCount_eq`), fewer than
`k x_j` observations are strictly above `X_i^j`, for some `j`.

*The population function.* `marginal μ j` is the c.d.f. of the `j`-th coordinate of `μ`.
`HasStableTailDependence μ ℓ` (`Multivariate/StableTailDependence.lean:71`) means: for every `x` with all
`x_j > 0`,

  `t⁻¹ μ{y : F_j(y_j) > 1 − t x_j for some j} → ℓ(x)` as `t ↓ 0`.

It says nothing about `ℓ` where some `x_j ≤ 0`.

*Common hypotheses (T).* `P` and `μ` probability measures, `μ` on `ℝ^ι`; `X_i` measurable, mutually
independent, identically distributed, with `X_0` of law `μ`; `marginal μ j` continuous for every `j`;
`kₙ ∈ ℕ`, `kₙ → ∞`, `kₙ/n → 0`.

*Pointwise.* Assume (T) and `HasStableTailDependence μ ℓ`, and let all `x_j > 0`. Then `ℓ̂ₙ(x) → ℓ(x)` in
probability. Lean: `ExtremeValueTheory.tendstoInMeasure_empiricalStableTailDependence`,
`Statistics/StableTailDependence.lean:462`.

*Uniform.* Assume (T) and `HasStableTailDependence μ ℓ`, and let `T` be real and `ε > 0`. Then

  `P(∃ x ∈ (0, T]^ι with |ℓ̂ₙ(x) − ℓ(x)| ≥ ε) → 0`,

with `P` the outer measure, since measurability of the event is not needed. Lean:
`ExtremeValueTheory.tendsto_measure_exists_abs_empiricalStableTailDependence_sub`,
`Statistics/StableTailDependence.lean:585`.

*Tail dependence coefficient.* `ι = {0, 1}`; `χ̂ₙ = tailDependenceEstimator X n k = 2 − ℓ̂ₙ(1, 1)`.
Assume (T) and `HasStableTailDependence μ ℓ`. Then `χ̂ₙ → 2 − ℓ(1, 1)` in probability. Lean:
`ExtremeValueTheory.tendstoInMeasure_tailDependenceEstimator`, `:888`. That `2 − ℓ(1, 1)` is the limit of
`P(F_1(X_1) > u | F_0(X_0) > u)` as `u ↑ 1` is `HasStableTailDependence.hasUpperTailDependence`.

*Domain of attraction.* `IsMDAWith μ ν a b` (`Multivariate/DomainOfAttraction.lean:128`) means:
`a_n^j > 0` for all `n`, `j`, and `μ(y ≤ a_n x + b_n)^n → ν(y ≤ x)` at every continuity point `x` of the
c.d.f. of `ν`, coordinatewise. Non-degeneracy is not part of it. `frechetStandardization ν` is the law of
`(−1/log G_j(Y_j))_j`, `Y ~ ν`. `V(y) = maxStableExponent ν₀ y = −log ν₀(z ≤ y)`.

Let `ι = {0, 1}`, `IsMDAWith μ ν a b`, with `ν` a probability measure and the marginals of **both** `μ`
and `ν` continuous; `X` and `k` as in (T); `0 < t < 1`. Put
`Âₙ(t) = pickandsRankEstimator X n k t = ℓ̂ₙ(t, 1 − t)`, and let `ν₀ = frechetStandardization ν`. Then

  `Âₙ(t) → pickandsDependence ν₀ t` in probability,

where `pickandsDependence ν₀ t = V(1/t, 1/(1 − t))` for `0 < t < 1`. Lean:
`ExtremeValueTheory.IsMDAWith.tendstoInMeasure_pickandsRankEstimator`,
`Statistics/StableTailDependence.lean:916`. Under the same hypotheses, for any finite `ι` and `x > 0`,
`ℓ̂ₙ(x) → V(1/x)` (`IsMDAWith.tendstoInMeasure_empiricalStableTailDependence`, `:835`, with a uniform
version at `:850`), and for `ι = {0, 1}`, `χ̂ₙ → 2 − V(1, 1)`
(`IsMDAWith.tendstoInMeasure_tailDependenceEstimator`, `:902`).

**(c) Caveats.**
1. **Consistency only.** No rate, no second-order condition, no asymptotic normality of `ℓ̂ₙ` or `χ̂ₙ`
   (for which the literature has results). iid data only.
2. **Faces are left out.** The textbook supremum runs over the closed box `[0, T]^ι`. Here it is over
   `(0, T]^ι`, since `ℓ` is unconstrained on the faces. It is uniform up to them.
3. **Continuous marginals are assumed**, for `μ`, and in the domain-of-attraction forms for `ν`. For `ν`,
   it is what the standardization uses. A limit with nondegenerate margins has them automatically, but
   `IsMDAWith` does not exclude degenerate ones, so it is a hypothesis.
4. **Conventions.** `n − k x_j` here; others write `n + 1/2 − k x_j`, or use order statistics.
   `tendstoInMeasure_empiricalStableTailDependence_of_tendsto` covers convergence along `yₙ → x`, and
   `tendstoInMeasure_empiricalStableTailDependenceOrderStat` is the order-statistics form. The library's
   Pickands function puts the weight `t` on coordinate `0` (C20), a mirror of some texts.
5. **Not the same as Pickands' 1981 estimator**, which has known margins (`pickandsDependenceEstimator`),
   and has no entry here. `Âₙ` is only pointwise in `t`, and no convexity is imposed on it.
6. The limit `2 − ℓ(1, 1)` need not be positive: `χ = 0` for asymptotic independence is consistent with
   the theorem, which says nothing about testing it.
7. Non-vacuity: iid bivariate comonotone and independent Gumbel sequences, `kₙ = ⌊√n⌋`
   (`test_nonvacuous_tendstoInMeasure_empiricalStableTailDependence_comono`,
   `test_nonvacuous_tendstoInMeasure_empiricalStableTailDependence_indep`,
   `test_nonvacuous_tendstoInMeasure_tailDependenceEstimator_indep`,
   `test_nonvacuous_isMDAWith_pickandsRankEstimator`). Known answers: `ℓ̂ₙ(1, 1) = 1` on a comonotone
   sample, and `2` on a countermonotone one (`test_empiricalStableTailDependence_comonotone`,
   `test_empiricalStableTailDependence_countermonotone`).

**(d) Questions.**
1. Is the definition of `ℓ̂ₙ`, with `>` and `R_i^j = #{m : X_m^j ≤ X_i^j}`, the one in your source? Is
   any convention difference more than `o_P(1)`?
2. Is the open box acceptable, given that `ℓ` on the faces is determined by the limit from the interior?
3. Is `Âₙ(t) = ℓ̂ₙ(t, 1 − t)` the estimator you mean by "rank-based Pickands", with `t` on the first
   coordinate?

## S16. Domains of attraction: the textbook form, the normal law, sample maxima, uniqueness

**(a) Literature.** [dHF, Thm 1.1.3]; [EKM, Thm 3.2.3, Thm 3.4.5]; for the normal constants, [EKM, Ex.
3.3.29], as recalled and not checked.

**(b) Lean, in math.** `IsInMDAGEV ξ`, for a c.d.f. `F`, is defined by the sign of `ξ` (C6):
`MDA(Φ_{1/ξ})`, `MDA(Ψ_{−1/ξ})` or `MDA(Λ)`. `gevCDF ξ` is the c.d.f. `H_ξ` of C2. `A • F` is as in the
Primer, with `(A • F)(x) = F(A⁻¹x)`. Files are in `ExtremeValueTheory/DomainOfAttraction/`.

*Textbook form.* For every c.d.f. `F` and `ξ ∈ ℝ`: `IsInMDAGEV F ξ` `⟺` there are affine `Aₙ` with
`((Aₙ • F)(x))^n → H_ξ(x)` for every `x`. That is, `F(aₙx + bₙ)^n → H_ξ(x)` with `aₙ > 0` for every `n`.
Lean: `CumulativeDistributionFunction.isInMDAGEV_iff_exists_tendsto_gevCDF`, `GEVDomain.lean:127`. The
form at continuity points is `isInMDAGEV_iff_exists_tendsto_gevCDF_of_continuousAt`, and every point is a
continuity point (`continuous_gevCDF`).

*Uniqueness.* If `IsInMDAGEV F ξ` and `IsInMDAGEV F η`, then `ξ = η`. Lean:
`CumulativeDistributionFunction.IsInMDAGEV.unique`, `GEVDomain.lean:186`.

*Sample maxima.* Let `F` be a c.d.f., `X : ℕ → Ω → ℝ`, with `F(x) = P(X_0 ≤ x)` for every `x`, `(X_i)`
mutually independent, and each `X_t` identically distributed with `X_0`; let `ξ ∈ ℝ`. Then
`IsInMDAGEV F ξ` `⟺` there are real `aₙ, bₙ` with `aₙ > 0` for all `n` and, for every `x`,

  `P((M_n − bₙ)/aₙ ≤ x) → H_ξ(x)`,

where `M_n = blockMax X n 0 = max_{i<n} X_i` (junk `0` for `n = 0`). Lean:
`CumulativeDistributionFunction.isInMDAGEV_iff_exists_tendsto_sampleMax`, `SampleMaxima.lean:73`.

*The normal law.* Let `Φ = standardNormalCDF`, `aₙ = normalScale n = (2 log n)^{−1/2}`, and
`bₙ = normalLocation n = √(2 log n) − (log log n + log 4π)/(2√(2 log n))`. Then for every `x`,

  `Φ(aₙx + bₙ)^n → exp(−e^{−x})`.

Lean: `CumulativeDistributionFunction.tendsto_standardNormalCDF_pow`, `Examples.lean:194`. Membership:
`isInMDAGEV_standardNormalCDF`, and `isInMDAGEV_ofMeasure_gaussianReal` for `N(m, v)`, `v ≠ 0`.

**(c) Caveats.**
1. These are bridges, not new theorems: they show that the library's case-split `IsInMDAGEV` is the
   textbook definition. C6, C7 and C14 use the case-split form.
2. `P` is not declared a probability measure in the sample-maxima theorem; the hypotheses on `F` and
   independence are what the proof uses. It is stated for `aₙ > 0` at **every** `n`, which is no
   restriction, since finitely many `n` do not matter.
3. Explicit constants exist only for the **standard** normal law here. `N(m, v)` is a membership
   statement. The formulas are junk for small `n` (`log 0 = 0`, so `a₀ = a₁ = 0`, and `log log n` is junk
   or negative for `n ≤ 2`), which does not affect the limit. So, for this statement, `aₙ > 0` holds only
   eventually, and passing to the textbook form uses `isInMDAGumbel_of_tendsto_mul_one_sub`.
4. The sign convention is `ξ = 1/α` (Fréchet), `ξ = −1/α` (Weibull). `test_isInMDAGEV_sign_convention`
   tests it. `test_normal_not_isInMDAGEV` and `test_cauchy_not_isInMDAGEV_zero` use uniqueness on
   concrete laws.

**(d) Questions.**
1. Are the normal constants as in your reference, in particular the `log 4π`, and are you content with
   `aₙ` as a formula valid only for large `n`?
2. Is there any variant of the domain of attraction you use, for example a limit of the type of `H_ξ`
   rather than `H_ξ` itself, that these forms do not reach?
   (`exists_isInMDAGEV_and_smul_eq_of_tendsto_sampleMax` handles a general limit `G`.)

---

## Summary of known deviations (from `FAITHFULNESS.md` and this guide)

| Area | Deviation | Effect |
|---|---|---|
| Regular variation | measurability separate from the definition | hypothesis added where needed |
| Karamata converse | none now: `F` eventually positive (the antitone version is deprecated) | as in BGT for `α > 1` (C9) |
| Second-order RV | `|A| ∈ RV_ρ` and constant sign assumed | one derived property built in |
| Weissman (far tail) | `ρ < 0` (or extra regularity at `ρ = 0`) | special case |
| Hill (α-mixing) | cluster condition assumed; simple mixing rate | sufficient, not sharp |
| `𝒜`, `D(uₙ)` | hypotheses, derived from α-mixing / m-dependence | standard |
| Infinite MA / AR(1) | `ψ ≥ 0`, noise `≥ 0`, `Σψ^δ < ∞`, `δ < min(α, 1)` | special case |
| Point processes | fdd-count convergence on interval classes | weaker formulation |
| Tail empirical process | uniform, unweighted | special case |
| GPD MLE normality | `ξ₀ ≠ 0`; measurable maximizers on compact `K` | stated scope |
| Answer to [BKW24] | one level instead of two; `ρ ∉ {0, 1}`; at `ρ = γ/α` only when `rₙ/n^{γ/α}` has a finite limit; normalizing levels only | **please check** (R14, R14a) |
| Echo, mixing | `𝒜` on long blocks for the power lag not proved; no rate for the power lag | sufficient for the example (R15) |
| GEV, Gumbel return levels, general form | parameter normality is a hypothesis; discharged by S10 for the GEV MLE at `ξ₀ ≠ 0`, nowhere at `ξ₀ = 0` | delta method only (S2) |
| GEV return level, MLE | as for S10; `m > 1` fixed | stated scope (S11) |
| GEV return level interval | consistency of the standard error assumed; no estimator shown to satisfy it, and the test uses the true value | **no computable interval justified yet** (S11) |
| POT return level, interval | exact iid GPD excesses, deterministic `n`, `ζ` known, `N` fixed, Wald form only | idealized (S3, S4) |
| Hill interval | `λ = 0`; exact Pareto excluded by the second-order definition | special case (S4) |
| Blocks, runs estimators | population limit assumed, not identified with the extremal index | **weaker than the name** (S5) |
| Intervals estimator | empirical moment limits assumed; no process in the statement | **weaker than the name** (S6) |
| GEV MLE, consistency | exact iid GEV sample, compact `K` | stated scope (S7) |
| GEV MLE, joint normality | exact iid GEV sample, `ξ₀ > −1/2`, `ξ₀ ≠ 0`, compact `K` with truth interior; block maxima from a domain of attraction not covered; information matrix not compared numerically in Lean with an outside source | **please check** (S10) |
| GPD Wilks, profile likelihood | `ξ₀ > 0`, narrower than the literature's `ξ₀ > −1/2`; exact GPD; a chart in place of a smooth `g`; confidence sets, not shown to be intervals | special case (S12) |
| Pickands normality | locally uniform second-order condition assumed; `k` is the smallest index; exact GPD excluded by the condition | **please check** (S13) |
| Moment normality | `γ > 0` only; second-order condition in ratio form, not translated to the textbook's `A` | special case (S14) |
| Nonparametric tail dependence | consistency only, iid, continuous margins; open box `(0, T]^ι` | stated scope (S15) |
| Normal norming constants | standard normal only; junk for small `n` | special case (S16) |
| GARCH(1,1) | squared volatility only; exponent bounds, not `c x^{−κ}` | **weaker than Kesten–Goldie** (S9) |
| Literature checks | [KS20, Lemma 7.5.4], [PS18, Lemma 4.1] and the [BS09] erratum not read directly; [BKW24] published version and Part III references, in particular Smith (1985), Prescott–Walden (1980), Bücher–Segers (2017) and [dHF, Thms 3.3.5, 3.5.4], not checked | **please check** |

## How to send feedback

Please email Federico Carrone or open a GitHub issue. Cite the entry number (for example "R6") and,
if possible, the precise reference you are comparing against. If a statement is wrong or
non-standard, a one-line description of the correct statement is enough; we will fix it and rerun
the checker.
