# Roadmap

Four tracks: the **textbook layer** of extreme value theory, **research** (open problems, with
priority to ones practitioners care about), **verification** (evidence that the statements are the
right ones), and **code quality and outreach**. See [`THEOREMS.md`](THEOREMS.md) for what is proved
and [`RESEARCH.md`](RESEARCH.md) for the research results.

`[x]` done, `[~]` partial, `[>]` in progress, `[ ]` missing.

## Next up

1. [>] Finish the statistics batch: Pickands and moment estimator normality, full GEV maximum
   likelihood (which makes GEV return-level intervals unconditional), L-moments and mean excess.
2. [ ] Practical open problem #1: block and run length for extremal-index estimators (see B).
3. [ ] Consolidation pass and specification tests for the newest results (see C and D).
4. [ ] Parametric stable family; Brown–Resnick and related max-stable processes.

---

## A. The textbook layer

Goal: the core results of the standard references: Embrechts, Klüppelberg and Mikosch, *Modelling
Extremal Events* (EKM); de Haan and Ferreira, *Extreme Value Theory* (dHF); Bingham, Goldie and
Teugels, *Regular Variation* (BGT); Leadbetter, Lindgren and Rootzén (LLR); Resnick, *Extreme Values,
Regular Variation and Point Processes* (1987) and *Heavy-Tail Phenomena* (2007); Kulik and Soulier,
*Heavy-Tailed Time Series* (KS); Beirlant, Goegebeur, Segers and Teugels, *Statistics of Extremes*
(BGST); Coles, *An Introduction to Statistical Modeling of Extreme Values* (2001).

### 1. Classical theory of maxima and regular variation
- [x] Fisher–Tippett–Gnedenko, max-stability, GEV family and moments
- [x] Domains of attraction (Fréchet, Weibull, Gumbel), von Mises conditions, quantile form
- [x] Regular variation: UCT, representation, Potter, Karamata (both halves), Breiman
- [x] Extended regular variation; second-order regular variation (`ρ ≤ 0`, one-sided bounds)
- [ ] de Haan's Π-variation theory in full (BGT ch. 3, dHF App. B): representation, uniform bounds
- [ ] Two-sided uniform second-order inequalities (dHF Thm 2.3.9 / Drees) for all `ρ ≤ 0`
- [ ] Rates of convergence of maxima (EKM §3.3 / Resnick ch. 2: penultimate approximation)

### 2. Peaks over threshold and likelihood
- [x] Pickands–Balkema–de Haan (equivalence, every shape)
- [x] GPD / GEV densities, Wald consistency, Fisher information, joint normality (GPD `ξ ≠ 0`)
- [x] GEV: full 3×3 Fisher information (digamma), positive definite, `E[∇²ℓ] = −I`, trivariate score CLT
- [ ] GEV: joint normality of the 3-parameter MLE (missing: Hessian domination near a moving endpoint,
      a preliminary √n rate, a 3×3 Slutsky step); then GEV return-level normality becomes unconditional
- [~] Likelihood at `ξ = 0`: GEV/GPD log-densities and scores continuous at 0 and true derivatives there;
      Gumbel (μ, σ) Fisher information and score CLT. Missing: the σξ and ξξ entries at 0 (need
      `ψ''(1) = −2ζ(3)`, not in Mathlib), Hessian continuity, MLE normality at `ξ = 0`
- [x] Probability-weighted moments and L-moments: GPD and GEV closed forms (Hosking's `k = −ξ`), strong
      consistency of the sample PWMs and of the Hosking–Wallis GPD estimator (continuous `F`)
- [x] Mean excess: GPD linearity, the converse for unbounded support (EKM 3.4.13(e)), empirical consistency
- [ ] L-moments follow-ups: unbiasedness of `b_r`; asymptotic normality of PWMs and the PWM estimator
      (`ξ < 1/2`); ties/atoms; GEV `(ξ, μ, σ)` by solving `τ₃(ξ̂) = t₃`; mean-excess converse for `ξ < 0`
- [ ] GEV maximum likelihood over the whole parameter space, not a compact set (Carl–Padoan–Rizzelli
      2025); removes the compact-set caveat of the current theorems
- [ ] Number of exceedances modelled as random in peaks over threshold

### 3. Statistics of extremes
- [x] Hill: consistency, normality, dependent data; Pickands; moment estimator; Weissman
- [>] Asymptotic normality of the Pickands and moment estimators (dHF Thms 3.3.5, 3.5.4)
- [x] Delta method (general and Gaussian), Wald intervals with asymptotic coverage; Hill and POT
      return-level intervals
- [~] Return levels: POT normality unconditional (from GPD MLE); GEV/Gumbel conditional on GEV MLE
      normality (in progress, see A.2)
- [ ] Profile-likelihood intervals (Coles §2.6.6)
- [ ] Hill confidence interval with bias (`λ ≠ 0`)
- [ ] Bias-reduced estimators (second-order: Gomes et al., Feuerverger–Hall), and their normality
- [~] Extremal-index estimators: blocks and runs consistent (general, m-dependent, via the tail
      process); intervals estimator consistent given Ferro–Segers Thm 1
- [ ] Ferro–Segers Theorem 1: limit law of normalized inter-exceedance times (makes the intervals
      estimator fully proved)

### 4. Heavy tails and stable laws
- [x] Subexponential laws, random sums, ruin, lognormal, `𝒮*`, convolution roots
- [x] Generalized CLT, converse, domain-of-attraction iff, stable index, normal domain
- [ ] The parametric stable family `S(α, β, σ, μ)`: characteristic function, closure properties
- [ ] Tails of stable laws (`P(X > x) ~ C x^{−α}`), series representation (LePage)

### 5. Dependence
- [x] Leadbetter, extremal index, tail process, time change, `θ = ϑ`, mixing, m-dependence
- [x] Linear processes, AR(1), ARMAX, Markov chains, tail chain
- [~] Stochastic recurrence equations: stationary solution, uniqueness, tail index exactly `κ`,
      GARCH(1,1)/ARCH(1)
- [ ] Sharp Kesten–Goldie tails `P(X > x) ~ c x^{−κ}` (needs the key renewal theorem, which Mathlib
      lacks: a project of its own)
- [ ] Point process of clusters (Davis–Hsing 1995): cluster point process convergence
- [ ] Cluster functionals and their limit theory (KS ch. 6, 9)
- [ ] Stochastic volatility models; regularly varying time series beyond linear (KS ch. 14–15)

### 6. Multivariate extremes
- [x] Multivariate regular variation, polar decomposition, converse Cramér–Wold (non-integer `α`)
- [x] Max-stable vectors: spectral representation (existence, uniqueness), Pickands function
- [x] Multivariate domains of attraction (dHF ch. 6.2)
- [x] Multivariate POT and the multivariate GPD (Rootzén–Tajvidi; sequence thresholds, pointwise)
- [ ] Nonparametric estimation: empirical tail dependence function / stable tail dependence
      function, CFG and Pickands estimators with estimated margins, and their consistency
- [ ] Hidden regular variation and asymptotic independence (Resnick 2002, Ledford–Tawn)

### 7. Point processes and functional limits
- [x] Vague convergence, Poisson random measures, exceedance point processes
- [x] Skorokhod space (Polish), weak convergence in `D`, tail empirical process ⇒ Brownian motion
- [~] Weighted tail empirical process (tail bound near 0 done; weighted weak convergence missing);
      tail empirical quantile process (dHF ch. 5)
- [ ] Point-process approach to sums: stable limits via point processes (Resnick 2007 ch. 7)
- [ ] Records and record times as point processes (Resnick ch. 4)

### 8. Max-stable processes
- [x] Spectral construction (de Haan 1984) on finite-dimensional laws
- [ ] Named models: Brown–Resnick, Schlather, extremal-t (finite-dimensional laws, stationarity)
- [ ] Domains of attraction for processes (dHF ch. 9)

---

## B. Research

### Done
- [x] The echo process: `θ = 1/2 < ϑ = 1` with an iid tail process; block-length phase transition
- [x] Answer to Bai–Kulik–Wang (2024), §1.4 Q2: anticlustering exactly below any block exponent
      `ρ₀ ∈ (0,1)` (power-lag echo process)
- [x] β-mixing without `θ = ϑ`
- [x] Minimal hypotheses for the classical, statistics and dependence theorems
- [x] Short runs estimate `ϑ`, not `θ`, on the echo process (a proved warning for practitioners)

### Practical open problems
From the survey in [`docs/PRACTICAL_OPEN_PROBLEMS.md`](docs/PRACTICAL_OPEN_PROBLEMS.md), ranked:
1. [ ] **Block and run length for extremal-index estimators** ("remains an open problem",
       Markovich–Rodionov 2020). Target: a theorem that no polynomial run-length rule works for every
       model, and that long blocks are safe. Closest to what is already proved.
2. [ ] **Sliding-blocks estimators without β-mixing** (Cissokho–Kulik, §5.3); the estimator behind
       `exdex::spm`.
3. [ ] **Is peaks over threshold always more precise than block maxima?** (Cissokho–Kulik); a possible
       counterexample for linear models.
4. [ ] **GEV likelihood on the whole parameter space** (see A.2).
5. [ ] **Annual maxima with a seasonally varying upper bound** (Stein 2017); the fitted GEV shape can
       differ from the daily tail shape.
6. [ ] Threshold selection by minimum Kolmogorov–Smirnov distance (Clauset et al.; Danielsson et
       al.; Drees–Janßen–Resnick–Wang 2020 conjecture).

### Theoretical open problems
- [ ] The critical case `κ = 1` of the power-lag echo process (completes the Bai–Kulik–Wang answer)
- [ ] Bai–Kulik–Wang §1.4 Q1: other processes with a mesoscopic phase transition (partly answered
      by the two echo processes)
- [ ] Can a regularly varying Markov chain have `θ < ϑ`?
- [ ] The weakest condition for `θ = ϑ`, via the gap formula `θ = ϑ − η`
- [ ] Breiman's lemma under the Denisov–Zwart condition: is it necessary?

### Publication
- [ ] Finish the novelty check of the Bai–Kulik–Wang answer (Weissman–Cohen 1995; Kulik–Soulier
      examples; published wording)
- [ ] arXiv note: the echo process, the answer to Bai–Kulik–Wang, mixing without `θ = ϑ`

---

## C. Verification

- [x] Lean kernel at build time; independent re-check of all 718,274 declarations with `con-leche`
      (nightly and on every code change)
- [x] Six faithfulness audits against the textbooks ([`FAITHFULNESS.md`](FAITHFULNESS.md))
- [x] Specification tests in CI ([`Test/`](Test/README.md)): non-vacuity (92), known answers (158),
      junk-value audit (one bug found and fixed), mutation checks (323 mutants, no real weakness)
- [ ] Specification tests for the newest results: return levels, confidence intervals, SRE/GARCH,
      extremal-index estimators, and each statistics result as it lands
- [ ] Seventh faithfulness audit covering everything added since the sixth
- [ ] **Human expert review** with [`docs/REVIEW.md`](docs/REVIEW.md): the one check that is
      independent of the AI that wrote the statements

---

## D. Code quality and outreach

### Consolidation
- [ ] Unify the three tail-quantile definitions
- [ ] One namespace for the `Minimality` results (`Classical*` files use `ExtremeValueTheory.Minimality`,
      `Dependence*` files do not)
- [ ] Rename "escape mass" (clashes with Abadi–Freitas–Freitas)
- [ ] Rename `gpdSurvival` / `gpdSurvival'` so the `ξ < 0` case cannot be picked by mistake
- [ ] Fix misleading `_of_lt_one` names; remove duplicate helpers
- [ ] Promote helper lemmas from the test files into the library (e.g. the exponential law is not
      subexponential; uniqueness of the regular-variation index)

- [>] Design pass (running): one representation of laws with a complete bridge; one definition
      per concept; names and namespaces; oversized files split (outside `Statistics/`); test helpers
      promoted; conventions in `docs/DESIGN.md`
- [ ] **Afterwards:** split the oversized `Statistics/` files (deferred while statistics agents edit
      them); migrate remaining uses off the `@[deprecated]` aliases and then delete the aliases; rebase
      the in-flight agent branches onto the new names

### Documentation
- [ ] `THEOREMS.md` and the website's "What is proved" list: add the newest results
- [ ] Every new file has a blueprint entry

### Outreach and Mathlib
- [ ] Announce the library on the Lean Zulip
- [ ] Upstream `ForMathlib/` (vague convergence, Poisson random measures, mixing, Skorokhod space,
      delta method, Wald intervals, …) as a series of small PRs; plan in
      [`UPSTREAMING.md`](ExtremeValueTheory/ForMathlib/UPSTREAMING.md)
- [ ] Then regular variation and the EVT core
