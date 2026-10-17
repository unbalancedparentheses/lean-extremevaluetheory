# Research targets

Open problems and correction targets in extremes of dependent sequences, collected from a literature
search on 2026-10-17. "Open" means a source explicitly states the question as open. Items marked
*unverified* were not checked against the full text.

## Primary target

**Candidate extremal index.** For a stationary regularly varying sequence with spectral tail process
`Θ`, let `ϑ = E[sup_{k≥0} |Θ_k|^α − sup_{k≥1} |Θ_k|^α]`. Then `θ ≤ ϑ` (Kulik–Soulier 2020,
Lemma 7.5.4, exact hypotheses *unverified*), with equality under anticlustering. Planinić–Soulier
(2018, Lemma 4.1) need only `|Y_t| → 0` instead of anticlustering. The model of Bai–Wang
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
- `θ ≤ ϑ` needs no anticlustering: besides stationarity, the spectral tail process and the
  existence of `θ` (for `|X|`), it uses condition `𝒜` along one level sequence with
  `nP(|X₀|>uₙ) → τ > 0`, `rₙ → ∞` and `rₙ/n → 0`.

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
- The Basrak–Davis–Mikosch (2002) Cramér–Wold conjecture for nonnegative regularly varying vectors,
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
