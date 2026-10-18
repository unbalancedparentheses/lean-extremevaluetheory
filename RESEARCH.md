# Research targets

Open problems and correction targets in extremes of dependent sequences, collected from a literature
search on 2026-10-17. "Open" means a source explicitly states the question as open. Items marked
*unverified* were not checked against the full text.

## Primary target

**Candidate extremal index.** For a stationary regularly varying sequence with spectral tail process
`Θ`, let `ϑ = E[sup_{k≥0} |Θ_k|^α − sup_{k≥1} |Θ_k|^α]`. Then `θ ≤ ϑ` (Kulik–Soulier 2020,
Lemma 7.5.4, exact hypotheses *unverified*), with equality under anticlustering. Planinić–Soulier
(2018, Lemma 4.1) is cited for ϑ under `|Y_t| → 0`. **Correction:** an earlier version of this file
read it as saying `|Y_t| → 0` can replace anticlustering in `θ = ϑ`; that is false — the echo process
(`Dependence/EchoProcess.lean`) has `|Y_t| → 0` and `θ = 1/2 < ϑ = 1`. PS18's lemma concerns `ϑ > 0` /
equivalent formulas for `ϑ`, not `θ = ϑ` (to be checked against the paper). The model of Bai–Wang
([arXiv:2110.07499](https://arxiv.org/abs/2110.07499)) has `θ < ϑ`, and no characterization of
`θ = ϑ` is known.

Plan: tail process → spectral tail process → time-change formula → `ϑ` and the formula under
`|Y_t| → 0` → link with the block extremal index `θ` → machine-checked record of which hypotheses
each step uses.

Progress (2026-10-17): the tail process, the spectral tail process, the Basrak–Segers polar
decomposition, the time-change formula, and `ϑ` with `ϑ ≤ 1`, `ϑ = P(sup_{k≥1}|Y_k| ≤ 1)`, `ϑ = 1`
for iid sequences and `ϑ > 0` when `Θ_t → 0` are proved (`Dependence/TailProcess.lean`,
`TimeChange.lean`). The block extremal index `θ` and Leadbetter's theorem are in
`Dependence/ExtremalIndex.lean`. Done since: `θ = ϑ` under forward anticlustering and condition `𝒜`, and `θ ≤ ϑ` without
anticlustering (`Dependence/Anticlustering.lean`), checked on the moving maximum (`θ = ϑ = 1/2`).

Hypothesis bookkeeping (the research value of the formal proofs):
- The cluster ratio `P(M_{rₙ} > uₙ)/(rₙ P(|X₀| > uₙ)) → ϑ` needs only stationarity, the tail process,
  `uₙ, rₙ → ∞` and *forward* anticlustering at *one* level sequence: no mixing, no `rₙ/n → 0`.
- `Θ_t → 0` follows from forward anticlustering at one level, without stationarity.
- `θ ≤ ϑ` (`le_candidateExtremalIndex'`) needs only stationarity, the spectral tail process and the
  existence of `θ` for `|X|`: no anticlustering, no mixing, no block condition, no block lengths.
  This matches KS20 Lemma 7.5.4 as described by Bai–Kulik–Wang (2024); an earlier version
  (`le_candidateExtremalIndex`) also assumed condition `𝒜`. The level sequences needed are supplied by
  regular variation (`hasExceedanceLevels_of_isRegularlyVarying`).

Also done: `𝒜` from α-mixing at a rate; for every stationary m-dependent sequence with a spectral tail
process, `|X|` has extremal index `ϑ`; through it, the moving maximum (`θ = 1/2`) and finite moving averages
(`θ = max ψ^α/Σψ^α`) recover the classical values.

Also done: Hill consistency under dependence (P2-adjacent), reduced to a variance bound on
exceedance counts; m-dependent and α-mixing versions (`Statistics/HillDependent.lean`). The
log-excess functional needed no separate variance treatment: it is squeezed deterministically between
exceedance counts.

Also done: infinite-order moving averages (`α < 1`) and AR(1), `θ = 1 − φ^α`, by m-dependent truncation.

Open next steps (updated): infinite-order linear processes for `α ≥ 1`; Markov chains (geometric β-mixing);
the backward limit
`Θ_{−t} → 0`; then the Bai–Wang-type `θ < ϑ` question (P1).

Progress on P1 (the gap θ < ϑ), 2026-10-17:
- **Gap formula** (`Dependence/ThetaGap.lean`): with the *escape mass* `η` (conditional mass of returns
  inside the block at lags growing with the level), the cluster ratio tends to `L` iff `η = ϑ − L`, with
  no anticlustering or mixing; under condition `𝒜`, `θ = ϑ − η`, so `θ < ϑ` iff `η > 0`.
- **Echo process** (`Dependence/EchoProcess.lean`): iid Pareto shocks, each reappearing once after a lag
  `⌊log z⌋ + 1` growing with its size. Stationary, regularly varying, spectral tail process
  `Θ_t = 1{t = 0}` (so `ϑ = 1`, `|Y_t| → 0`), extremal index `θ = 1/2`, escape mass `1/2`. This is a much
  simpler mechanism for `θ < ϑ` than the Bai–Wang stable-regenerative model (novelty not checked
  against the literature).
- **Block-length phase transition** (`Dependence/EchoPhaseTransition.lean`): for the echo process the
  cluster ratio tends to `1 = ϑ` for `rₙ = o(log n)`, to `(1 + min(1/(cα), 1))/2` for `rₙ/log n → c`, and to
  `1/2 = θ` for `log n = o(rₙ)`: a continuous transition with a kink at `c = 1/α`, the scale of the echo
  lag `(1/α) log n`. Condition `𝒜` fails whenever `rₙ → ∞` and `rₙ/log n` has a finite limit, and holds for long blocks with `rₙ = o(n)`
  (`Dependence/EchoConditionA.lean`), where `θ = ϑ − η` then applies through the general theorem.
  This is a concrete instance of the block-length phase transitions asked about in P1.
- **Mixture** (`Dependence/MixtureProcess.lean`): constant with probability `p`, iid otherwise. `η = 0`
  (cluster ratio → `ϑ = 1 − p`), but anticlustering and `𝒜` fail and no extremal index exists (maxima
  converge to `p + (1−p)e^{−τ}`). So `η = 0` is strictly weaker than anticlustering and does not imply
  that `θ` exists.

### Novelty assessment (literature check, 2026-10-18; full report in [`docs/NOVELTY.md`](docs/NOVELTY.md))

- **`θ ≤ ϑ`: known** (Kulik–Soulier 2020, Lemma 7.5.4, cited by Bai–Kulik–Wang as "always holds"; the
  argument goes back to O'Brien 1987 and Segers 2006). Our contribution is a machine-checked proof
  with minimal hypotheses; the exact hypotheses of Lemma 7.5.4 remain unverified.
- **Gap formula: partly known.** Close to a reformulation of the O'Brien/Segers averaging identity;
  the named two-sided statement was not found in the literature. The name "escape of mass" is used by
  Abadi–Freitas–Freitas for a different phenomenon, so ours should be renamed (e.g. "late-return
  mass") or explicitly distinguished.
- **Echo process: likely new.** Bai–Wang (2023) know of no other example with `θ < ϑ`; Bai–Kulik–Wang
  call their model qualitatively different from all known examples. The echo process would be the
  second mechanism, and the first with a trivial spectral tail process. Still to check: the examples
  and exercises of Kulik–Soulier (2020) in a physical copy, or with an expert.
- **Block-length phase transition: type known (Bai–Kulik–Wang, polynomial scale), ours likely new**
  (logarithmic scale, kink at `c = 1/α`).
- **Mixture: known** (non-ergodic mixtures; Leadbetter 1983).

**Next opportunity.** A power lag `L(z) = ⌈z^γ⌉`, `γ < α`, is already covered by the Lean echo theorem
(`θ = 1/2`, `ϑ = 1`). Heuristically, anticlustering then holds exactly for blocks shorter than
`n^{γ/α}`, which would answer Bai–Kulik–Wang's second open question for every exponent in `(0,1)`.
Also unformalized: the echo process should be geometrically β-mixing, giving a sharp counterexample
to "mixing plus a vanishing tail process implies `θ = ϑ`". Recommended write-up: a short arXiv note
centred on the echo process (title suggestion: "An echo process: a simple regularly varying sequence
whose extremal index is invisible to its tail process").

### Minimal hypotheses: classical and statistics results (`Minimality/Classical*.lean`, namespace `ExtremeValueTheory.Minimality`)

| Theorem | Hypothesis | Status | Witness |
|---|---|---|---|
| Karamata (`tendsto_integral_Ioi_div`) | `α > 1` | needed: fails for every `F` when `α < 1`; ratio → ∞ when `α = 1` | `not_tendsto_integral_Ioi_div_of_lt_one`, `tendsto_integral_Ioi_div_atTop_of_neg_one` |
| Karamata | `F` antitone | dropped (measurable and locally bounded suffice) | `tendsto_integral_Ioi_div_of_measurable` |
| Breiman | `E Y^{α+ε} < ∞` | cannot be weakened to `E Y^α < ∞` | `breiman_counterexample` |
| Breiman | same, when `x^α P(X > x) → c > 0` | dropped to `E Y^α < ∞` | `tendsto_measure_mul_div_measure_of_tendsto_rpow_mul` |
| Gumbel von Mises, finite endpoint | no atom at `x_F` | needed | `atomCDF_vonMises_counterexample` |
| Generalized CLT, asymmetric | tail balance | needed for any non-degenerate limit | `not_tendsto_of_not_tailBalance` |
| Hill consistency | `k → ∞` | needed, even for exact Pareto (and sufficient there) | `tendstoInMeasure_hill_pareto_iff` |
| Hill consistency | `k/n → 0` | needed | `not_tendstoInMeasure_hill_of_le_mul` |

### Minimal hypotheses: dependence results (`Minimality/Dependence*.lean`)

| Theorem | Hypothesis | Status | Witness |
|---|---|---|---|
| cluster ratio → `ϑ` (`tendsto_blockRatio`) | forward anticlustering | needed (cannot be dropped) | `logEcho_blockRatio_ne` |
| same | anticlustering as a necessary condition | not necessary (exact condition: escape mass `0`) | `mixture_tendsto_blockRatio_of_not_antiClustering` |
| same | `rₙ → ∞` | needed | `movingMax_blockRatio_const_one` |
| `Θₜ → 0` from anticlustering | anticlustering | sufficient, not necessary | `logEcho_tendsto_zero_of_not_antiClustering` |
| `θ = ϑ` (`hasExtremalIndex_abs`) | condition `𝒜` under anticlustering | needed, even for `θ` to exist | `scaleMixture_needs_conditionA` |
| Leadbetter's theorem | `D′(uₙ)` | needed | `leadbetter_needs_conditionD'` |
| Hill under α-mixing | the mixing condition | needed | `mixture_hill_needs_mixing` |
| m-dependent `θ = ϑ` | m-dependence → α-mixing | true if anticlustering is kept (`hasExtremalIndex_abs_of_alphaMixing`); anticlustering does **not** follow from mixing | `logEcho_alphaMixing_theta_ne_vartheta` |

New findings: (1) the log-lag echo process is strongly mixing at a geometric rate (`α(h) ≤ C e^{−αh}`,
`alphaMixing_echoProcess_le`) yet has `θ = 1/2 ≠ ϑ = 1`, so mixing plus a vanishing tail process does
not give `θ = ϑ`; (2) a scale mixture with anticlustering and `ϑ = 1` has no extremal index, so `𝒜`
is needed for existence, not only identification. Novelty of (1) not yet checked against the
literature.

## Open problems

1. **The gap between `θ` and `ϑ`, and phase transitions.** Bai, Kulik, Wang (2024),
   [arXiv:2409.17966](https://arxiv.org/abs/2409.17966), §1: whether the mesoscopic phase transition
   of their model occurs for other regularly varying processes, and whether anticlustering can hold
   with `lim log d_n / log n = ρ` only for `ρ` up to some `ρ₀ < 1`.
2. **Sliding-blocks cluster estimators.** Cissokho, Kulik (2020),
   [arXiv:2005.11378](https://arxiv.org/abs/2005.11378), §5.3: consistency without β-mixing;
   unbounded cluster functionals (partly addressed by Chen–Kulik,
   [arXiv:2308.16270](https://arxiv.org/abs/2308.16270)); whether peaks over threshold always beats
   block maxima in variance.
3. **Bias of ℓᵖ-block cluster inference.** Buriticá, Wintenberger,
   [arXiv:2212.13521](https://arxiv.org/abs/2212.13521) (stated as a research direction).
4. **Self-normalized M1 limits with clustering**, [arXiv:2405.01318](https://arxiv.org/abs/2405.01318)
   (needs the Skorokhod M1 topology).

## Errata (formalization targets)

1. **Drees, Rootzén (2010)**, Ann. Statist. 38(4). Correction note
   [arXiv:1510.09090](https://arxiv.org/abs/1510.09090): the proof of Lemma 5.2(vii) fails under the
   stated conditions, and the fix assumes φ-mixing.
2. **Basrak, Segers (2009)**, SPA 119. Erratum SPA 121(4) (2011) 896–898,
   DOI 10.1016/j.spa.2010.12.009. Content *unverified*; read it before relying on the original
   statements.
3. **Gomes, de Haan, Pestana (2004)**, J. Appl. Probab. 41. Correction J. Appl. Probab. 43(4) (2006),
   DOI 10.1239/jap/1165505221. Content *unverified*.

## Resolved results worth verifying

- Hsing's (1993) null-variance conjecture for cluster-index estimators of linear models, proved by
  Buriticá–Wintenberger ([arXiv:2212.13521](https://arxiv.org/abs/2212.13521)).
- **Formalized:** the converse Cramér–Wold device of Basrak–Davis–Mikosch (2002), Thm 1.1(i), for every
  non-integer `α` (`RegularVariation/CramerWoldConverse.lean`). Related: the Basrak–Davis–Mikosch (2002) Cramér–Wold conjecture for nonnegative regularly varying vectors,
  proved by Boman–Lindskog ([arXiv:0802.4373](https://arxiv.org/abs/0802.4373)). The device fails for
  integer `α` in general (Hult–Lindskog 2006).
- Anticlustering is not essential for the tail-process limit (Planinić–Soulier,
  [arXiv:1706.04767](https://arxiv.org/abs/1706.04767), §4); dissipative representations
  (Dombry–Hashorva–Soulier, [arXiv:1710.08358](https://arxiv.org/abs/1710.08358)).
- Markov chains with `θ = 0` (Kulik–Soulier–Wintenberger,
  [arXiv:1511.04903](https://arxiv.org/abs/1511.04903)); Smith's (1988) counterexample to
  "`θ` = 1 / mean cluster size".

## Infrastructure

Present in the Mathlib version used here: Brownian motion, Kolmogorov extension, Ionescu-Tulcea,
infinite products, Poisson pmf, Lévy–Prokhorov, Portmanteau, Prokhorov, tightness, Cramér–Wold,
the central limit theorem, measure-preserving maps and ergodic theory.

Absent: point processes and random measures, Poisson random measures, vague convergence, the
Skorokhod space, mixing coefficients, and a stationary-sequence API. General infrastructure written
here goes in `ExtremeValueTheory/ForMathlib/` (Mathlib imports only, Mathlib style) for upstreaming.
