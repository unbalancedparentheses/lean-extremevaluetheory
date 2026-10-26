# Expert review guide: *Extreme Value Theory in Lean*

Repository: `https://github.com/unbalancedparentheses/lean-extremevaluetheory` (blueprint:
`https://unbalancedparentheses.github.io/lean-extremevaluetheory`). Snapshot: commit `9a3bfe3`.

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

**Priority.** Part I (the extremal index `θ` versus the candidate extremal index `ϑ`) contains
**new results** that are not in the textbooks: an exact formula for the gap `ϑ − θ`, an explicit
process with `θ = 1/2 < ϑ = 1`, and a block-length phase transition. Those are the entries where an
expert's check matters most, and where the literature attributions were *not* verified against the
original papers. They are marked ★. If you have limited time, please review Part I (about 2 to 3
hours) and skip the rest.

References used throughout: [EKM] Embrechts–Klüppelberg–Mikosch, *Modelling Extremal Events*;
[dHF] de Haan–Ferreira, *Extreme Value Theory: An Introduction*; [BGT] Bingham–Goldie–Teugels,
*Regular Variation*; [LLR] Leadbetter–Lindgren–Rootzén, *Extremes and Related Properties of Random
Sequences and Processes*; [Feller] Feller, *An Introduction to Probability Theory*, Vol. II; [ST]
Samorodnitsky–Taqqu, *Stable Non-Gaussian Random Processes*; [BS09] Basrak–Segers, SPA 119 (2009);
[KS20] Kulik–Soulier, *Heavy-Tailed Time Series* (2020); [PS18] Planinić–Soulier, *The tail
process revisited*, Extremes 21 (2018); [BKW24] Bai–Kulik–Wang, arXiv:2409.17966; [BW]
Bai–Wang, arXiv:2110.07499; [Resnick] Resnick, *Extreme Values, Regular Variation and Point
Processes*; [Billingsley] *Convergence of Probability Measures*, 2nd ed.

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
The process is a stationary factor of iid noise, so it is ergodic-theoretically mixing (not
formalized). `𝒜` holds for long blocks (R10).

**(d) Questions.**
1. Is this example (or an equivalent one) already in the literature? It seems much simpler than
   [BW].
2. Is this a convincing counterexample to "`|Y_t| → 0` ⇒ `θ = ϑ`"? Is that implication claimed or
   suggested anywhere in the literature?
3. Should we also prove strong (α- or β-) mixing for this process, to show that the gap is not an
   artifact of weak dependence assumptions?

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

Lean: `ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_Ioi_div_of_measurable`
(`RegularVariation/KaramataConverse.lean:396`);
`ExtremeValueTheory.IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi` (`KaramataConverse.lean:196`).

**(c)** In the direct half, a non-integrable `F` would make the integral junk `0` and the conclusion
false, so integrability is necessarily proved. The converse assumes `F` antitone, a special case of
BGT's locally integrable `f`.  **(d)** 1. Is the antitone converse enough for EVT uses (survival
functions)?

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

**(c)** The Pickands indexing follows dHF, one off from EKM.  **(d)** None.

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
*GEV* (`ae_tendsto_gevMLE`, `Statistics/GEVMLE.lean:602`): the same, with parameters `(ξ, μ, σ)`
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

**(c)** Existence of *some* measurable maximizer that is asymptotically normal, not "every
maximizer". `ξ₀ = 0` is not covered. For the GEV, only the location–scale Fisher information and its
score CLT are done (no joint GEV normality).
**(d)** 1. Is the "there exists a measurable MLE on `K`" form adequate, or should it be "every
measurable maximizer"? 2. How important is `ξ₀ = 0`?

---

## Summary of known deviations (from `FAITHFULNESS.md`)

| Area | Deviation | Effect |
|---|---|---|
| Regular variation | measurability separate from the definition | hypothesis added where needed |
| Karamata converse | `F` antitone | special case of BGT |
| Second-order RV | `|A| ∈ RV_ρ` and constant sign assumed | one derived property built in |
| Weissman (far tail) | `ρ < 0` (or extra regularity at `ρ = 0`) | special case |
| Hill (α-mixing) | cluster condition assumed; simple mixing rate | sufficient, not sharp |
| `𝒜`, `D(uₙ)` | hypotheses, derived from α-mixing / m-dependence | standard |
| Infinite MA / AR(1) | `ψ ≥ 0`, noise `≥ 0`, `Σψ^δ < ∞`, `δ < min(α, 1)` | special case |
| Point processes | fdd-count convergence on interval classes | weaker formulation |
| Tail empirical process | uniform, unweighted | special case |
| GPD MLE normality | `ξ₀ ≠ 0`; existence of a measurable maximizer on compact `K` | stated scope |
| Literature checks | [KS20, Lemma 7.5.4], [PS18, Lemma 4.1] and the [BS09] erratum not read directly | **please check** |

## How to send feedback

Please email Federico Carrone or open a GitHub issue. Cite the entry number (for example "R6") and,
if possible, the precise reference you are comparing against. If a statement is wrong or
non-standard, a one-line description of the correct statement is enough; we will fix it and rerun
the checker.
