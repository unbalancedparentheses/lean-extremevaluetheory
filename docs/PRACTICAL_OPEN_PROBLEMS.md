# Practically relevant open problems in EVT reachable by the Lean library

Literature search of 2026-10-18. I read these repository files to see what is already formalized:
`README.md`, `THEOREMS.md`, `ROADMAP.md`, `RESEARCH.md`, `docs/PRACTITIONERS.md`, `docs/NOVELTY2.md`,
and the headers of `Statistics/ExtremalIndexEstimators.lean` and `Dependence/EchoPowerLag.lean`.

**Labels.**
- **OPEN-EXPLICIT**: a source states the problem as open, conjectured, or left for future research. The quote is given.
- **OPEN-IMPLICIT**: no theorem exists, but no source calls it an open problem.
- **RESOLVED**: a later paper claims to solve it. Such items are verification targets, not research targets.

I quote only what I read in the full text, and I mark everything else.

Quotes come from arXiv HTML or PDF text that I extracted myself. Mathematical symbols have been flattened to
LaTeX alt-text, so check page numbers and exact typography against the published versions before citing.

---

## 0. Bai–Kulik–Wang (2024), arXiv:2409.17966v2: every open question, verbatim

Source: https://arxiv.org/abs/2409.17966. Text taken from the arXiv HTML of v2, https://arxiv.org/html/2409.17966v2.
The PDF build is dated "August 24, 2026" (LaTeX `\today`). The repository's notes give the journal version as
AAP 36(4) 2026; I did not check that here.

1. **§1.4 "Comments", first question.**
   > "It would be very interesting to know whether such a phase transition exists for any other regularly varying stochastic processes."

   "Such a phase transition" is the mesoscopic transition of `P(max_{k≤d_n} X_k > b_n)` with `d_n ≍ n^ρ`, `ρ ∈ [0,1]`.
2. **§1.4, second question.**
   > "It would also be interesting to know whether there are models such that the anticlustering condition holds with $\lim_{n\to\infty}\log d_{n}/\log n=\rho$ for $\rho$ up to certain $\rho_{0}<1$ only."

   **Status: answered by the library** for every `ρ₀ ∈ (0,1)`, by the power-lag echo process (`powEchoProcess_antiClustering_iff`).
3. **Introduction, a research direction that partly repeats question 1.**
   > "It is left to further research that whether other models with weak extremal dependence but violating the anticlustering condition may exhibit a similar phase transition at mesoscopic level as revealed here."
4. **Introduction, a motivating question.**
   > "Second, it is natural to ask for a further explanation on the discrepancy between the two indices."

   The two indices are `θ` and `ϑ`. The library's gap formula `θ = ϑ − η` under condition `𝒜` (`ThetaGap.lean`) is one such explanation.
5. **End of §1.3, a stated belief (conjecture) about their own model.**
   > "...in the presence of asymptotic tail independence of block maxima, which we believe to hold when $\log d_{n}/\log n\to 1$ and $d_{n}=o(n)$ , one has $\mathbb{P}(\max_{k\le n}X_k/b_n\le x)\sim(1-\mathbb{P}(\max_{k\le d_n}X_k/b_n>x))^{\lfloor n/d_n\rfloor}\to\exp(-\vartheta_{1}x^{-\alpha})$."

   This is specific to the stable-regenerative double-stable model, which the library does not have. Out of reach.
6. **Remark 1.1, a research direction.**
   > "Another interesting direction is to consider extremes of stable-regenerative models with other types of tails, and the extremes have recently been shown to have new scaling limits [8, 9]."

   Out of reach.

Also relevant, though not phrased as a question: for their own model, anticlustering holds for `d_n = o(log n)` and fails for
`d_n ≫ n^ε` (Cor. 1.6). The range `log n ≪ d_n ≪ n^ε` is left open (repository reading in `docs/NOVELTY2.md`).

**What the library can still add on questions 1 and 3:**
- The log-lag echo has a continuous transition with a kink at `c = 1/α`.
- The power-lag echo has a step transition at `ρ₀ = γ/α`.

So "another regularly varying process with a mesoscopic transition" is already in hand. What it is not is "the same linear interpolation as BKW".
The one gap that is formally open in the library is the boundary case `κ = 1` of `powEchoProcess_critical`.
Practical relevance of this whole cluster is modest. It feeds candidate C2 below.

---

## 1. Candidates

### C1. Asymptotic variance of PoT versus block-maxima cluster estimators: is PoT always better? (OPEN-EXPLICIT)
- **Statement.** Take estimators of a cluster index such as the extremal index. Is the asymptotic variance of the peaks-over-threshold
  (PoT) blocks estimator, with threshold `u_n` set from marginal order statistics, always at most that of every block-maxima-type (BM)
  estimator? BM-type means a threshold from block-maxima quantiles `c_{r_n}`, the Northrop or Berghaus–Bücher sliding estimators, and similar.
- **Source.** Cissokho & Kulik, "Estimation of cluster functionals for regularly varying time series: sliding blocks estimators",
  arXiv:2005.11378 (EJS 2021), §5.3 "Open questions", https://arxiv.org/abs/2005.11378:
  > "In view of the behaviour of $\widetilde{\vartheta}_{n,1}(u_n)$ and $\widetilde{\vartheta}_{n,1}(c_{r_n})$, it would be interesting to know if (whenever possible) the PoT method always gives a smaller variance than the block maxima ones."

  They give the formulas
  `σ₁² = −ϑ + ϑ² Σ_j P(Y_j>1)` (PoT) and
  `σ₃² = e^{−ϑ}(1−e^{−ϑ}) − 2ϑe^{−ϑ} + ϑ² Σ_j P(Y_j>1)` (BM threshold),
  and note σ₁² < σ₃².
- **Still open?** I found no resolution.
  - Chen & Kulik (arXiv:2309.03163) confirm only that sliding and disjoint PoT blocks have equal variance, while in the BM framework sliding is strictly better than disjoint.
  - **Possible lead (my inference, verify):** Buriticá & Wintenberger (arXiv:2212.13521, Thm 5.6) prove that their ℓᵖ-block estimators,
    whose thresholds come from order statistics of *block* norms (a BM-type threshold), have **null** asymptotic variance for
    short-memory linear processes. This settles Hsing's 1993 conjecture.
  - By my hand calculation (unchecked), the PoT formula σ₁² is **not** zero for MA(1). With `x = ψ^α`, `ϑ = 1/(1+x)` and
    `Σ_j P(Y_j>1) = 1 + 2x/(1+x)`, so `ϑ Σ = (1+3x)/(1+x)² > 1` for `x ∈ (0,1)`, giving σ₁² > 0.
  - If both normalizations really are comparable (√(#exceedances) against √(#extreme blocks)), this is a **negative answer** for linear models.
- **Why practitioners care.** Hydrology and finance users choose between `exdex::spm` (sliding BM, Northrop/Berghaus–Bücher) and
  blocks, runs or intervals estimators (`extRemes`, `evd`). Which has the smaller standard error is a daily decision.
- **Library has.**
  - Spectral tail processes, with closed forms for finite and infinite moving averages, AR(1) and ARMAX.
  - `ϑ = P(sup_{k≥1}|Y_k| ≤ 1)`.
  - Consistency of the blocks and runs estimators for their population targets.
- **Missing.**
  - CLTs for the cluster estimators, which are far off.
  - The Berghaus–Bücher variance formula.
  - `Σ_j P(Y_j>1)` as a functional of the tail process for the moving-average family.
- **Feasibility.**
  - *Medium* for the model-level algebra: closed forms of σ₁², σ₃² and BM-type variances on MA(q), AR(1) and ARMAX from the library's
    tail processes, treating the published variance formulas as definitions. This yields a "conditional formal counterexample".
  - *Hard* for unconditional statements, which need the CLTs.
- **Outcome.** A practical recommendation ("for linear or short-memory models, BM-thresholded estimators can be super-efficient")
  or a warning, plus machine-checked known-answer variance tables for testing software.

### C2. Choosing the block or run length for extremal-index estimation (OPEN-EXPLICIT; the library already has strong partial results)
- **Statement.** Give a rule for the block or run length `r_n` under which the blocks, runs or sliding-BM estimators are consistent for `θ`
  across a broad model class. Or show that no universal rule exists.
- **Sources.**
  - Markovich & Rodionov, "Threshold selection for extremal index estimation", arXiv:2009.02318, §1, https://arxiv.org/abs/2009.02318:
    > "The semiparametric maxima estimators (Berghaus and Bücher 2018; Northrop 2015) depend on the block size only. The choice of the latter remains an open problem."
  - Bücher & Zhou, "A horse race between the block maxima method and the peak-over-threshold approach", Stat. Sci. 36 (2021),
    arXiv:1807.00282, §6 "Open problems":
    > "Block length choice and bias reduction for BM."
  - Ferro and others note that run-length choice for runs declustering is ad hoc in practice. I saw this only in secondary sources and did not verify a primary quote.
- **Why practitioners care.** Runs declustering with a *fixed* run length (for example r = 3 days, the Coles 2001 practice; `extRemes::decluster`,
  `evd::exi`) is the standard POT workflow for rainfall, river flow and wind. Return levels scale with θ.
- **Library has (much of this is done).**
  - `logEcho_tendstoInMeasure_runsEstimator`: for the geometrically α-mixing log-lag echo process, runs with `r_n = o(log u_n)`,
    including every fixed run length, are consistent for `ϑ = 1`, not `θ = 1/2`.
  - `logEcho_tendstoInMeasure_blocksEstimator`: long blocks (`log n = o(r_n)`) are consistent for `θ`.
  - `powEchoProcess_polyBlocks`: a step transition at `r_n ≍ n^{γ/α}`, at macroscopic levels (`nP(X>u_n) → τ`).
  - Under anticlustering, both estimators target `ϑ` (`HasSpectralTailProcess.tendstoInMeasure_runsEstimator`).
- **Missing.**
  - Estimator-level results for the **power-lag** echo at *intermediate* thresholds (`nP(X>u_n) → ∞`). The cutoff then becomes
    `r_n ≍ u_n^γ ≍ (n/k_n)^{γ/α}`. This needs an α-mixing rate bound for the power-lag echo good enough for the concentration
    conditions; the library has β-mixing (`isBetaMixing_echoProcess`), so that rate needs checking.
  - A clean "no universal rule" packaging.
- **Feasibility.** *Easy–medium.* It is a power-lag copy of the log-echo estimator proofs, plus a mixing-rate lemma.
- **Outcome.** A **warning theorem**:
  > For every ρ₀ < 1, there is a stationary β-mixing regularly varying sequence with `θ = 1/2` for which any runs or blocks rule
  > with `r_n ≤ (n/k_n)^{ρ}`, `ρ < ρ₀`, converges to 1.

  So no polynomial run-length rule is universally consistent, and fixed run lengths are never safe without anticlustering.
  The **recommendation** half is the existing positive result: long blocks are consistent for `θ`.
  - *Caveat:* the echo is a constructed model. The practical message is "short-lag diagnostics cannot certify θ", not "real data contain echoes".

### C3. Consistency of sliding-blocks cluster estimators without β-mixing (OPEN-EXPLICIT)
- **Source.** Cissokho & Kulik, arXiv:2005.11378, §5.3:
  > "For the sliding blocks estimators, obtain consistency under minimal conditions (that is, without relying on $\beta$-mixing)."

  Unbounded functionals are partly handled by Chen & Kulik (arXiv:2308.16270), which is already recorded in `RESEARCH.md`.
- **Why practitioners care.** `exdex::spm`, the default sliding-BM estimator, is widely used. GARCH-type and Markov models are
  usually proved α-mixing, and β-mixing is harder to establish.
- **Library has.** A Chebyshev-based consistency framework for disjoint-blocks and runs estimators under **α-mixing rates**, plus cluster conditions
  (`tendstoInMeasure_blockCount_div`, `variance_sum_ite_mem_le`, the m-dependent versions), and Hill consistency from a variance bound.
- **Missing.** The variance bound for *overlapping* block sums (sliding blocks), and the passage from bounded indicator functionals to general bounded `H`.
- **Feasibility.** *Medium.* Covariances of overlapping blocks are controlled by the same lag-sum bounds. The main work is bookkeeping.
- **Outcome.** A **validity theorem**: sliding-blocks estimators (extremal index, possibly the cluster-size distribution) are consistent under α-mixing at a rate.
- **Caveats.** Whether this is new for the extremal index is uncertain. Robert, Segers & Ferro (2009, EJS 3) may already use α-type mixing for
  their sliding estimator; I did not check this. The question as stated (general cluster functionals) is open.

### C4. GEV maximum likelihood over the full parameter space: consistency and uniqueness (RESOLVED 2025; verify)
- **Source.** Carl, Padoan & Rizzelli, "Asymptotic theory for the likelihood-based block maxima method in time series", arXiv:2506.17448 (2025),
  https://arxiv.org/abs/2506.17448:
  > "Notably, even in the independence case, whether the MLE—computed over the full parameter space—is consistent and uniquely maximizes the likelihood has remained an open question. We resolve this question for both independent and dependent data, thereby closing a long-standing gap in the literature."

  Their Corollary 3.6 states that the MLE is the unique global maximiser over `Θ_n` with probability tending to one, and that it is
  asymptotically normal with bias `λ₀θ₀^{ρ₀} I⁻¹ b₀`. The paper also reports that naive Bayesian intervals for the extremal index have
  poor coverage, and it proposes an adjusted posterior. I do not know the paper's publication status.
- **Why practitioners care.** Every annual-maximum analysis (flood, wind, temperature) fits the GEV with an unconstrained optimizer
  (`extRemes::fevd`, `ismev`, `scipy`). The library's theorems assume a compact parameter set, an assumption flagged in `PRACTITIONERS.md` §4.7.
- **Library has.**
  - GEV identifiability.
  - Strong consistency of the 3-parameter MLE on compact sets for ξ > −1 (`ae_tendsto_gevMLE`).
  - A Wald framework that also covers extended-real values and parameter-dependent supports.
  - The location–scale Fisher information.
- **Missing.**
  - The shape-parameter Fisher information (digamma terms) and joint normality.
  - Global-uniqueness arguments, which need concavity-type or local bounds near the truth plus control of the likelihood at the boundary as `σ → 0` and `|ξ| → ∞`.
- **Feasibility.** *Medium–hard* for the iid, well-specified case. *Hard* for their misspecified, serially dependent block-maxima setting.
- **Outcome.** A **validity theorem** covering what software actually computes. It removes a standing scope caveat.

### C5. Annual maxima under within-season non-stationarity (Stein 2017), and its dependent version (OPEN-EXPLICIT for the dependent case)
- **Statement.**
  - Stein proves the iid result with triangular arrays: for daily values whose upper endpoint varies smoothly within the season, the block maximum
    still has a GEV limit, but with a *different* shape from the daily tail. The example in Bücher & Zanger has shape −2/11.
  - Open: does the same hold under serial dependence?
- **Sources.**
  - Stein, "Should annual maximum temperatures follow a generalized extreme value distribution?", Biometrika 104 (2017) 1–16, https://doi.org/10.1093/biomet/asw070.
  - The conjecture is reported in Bücher & Zanger, "On the disjoint and sliding block maxima method for piecewise stationary time series",
    arXiv:2110.15576, §4 (I believe it is published in Ann. Statist. 2023, unverified):
    > "In the case of serially independent observations, the limiting distribution was found to be GEV again, despite with an unexpected shape parameter; see Theorem 1. Extensions to serial dependence were not worked out explicitly, but it was conjectured that similar phenomena arise."

    Their future-research item (a) proposes generalizing the sampling scheme to "certain forms of inner-seasonal non-stationarity".
- **Why practitioners care.** Climate attribution and heat-wave studies fit the GEV to annual maxima (TXx) and interpret the shape ξ.
  Seasonal non-stationarity changes ξ systematically, so the fitted ξ is not the daily tail shape.
- **Library has.** GEV and max-stability, Weibull-domain characterization (finite endpoint), Leadbetter's `D(u_n)`/`D′(u_n)` theorem,
  m-dependence and α-mixing to condition `𝒜`, and `H^θ` limits.
- **Missing.** Triangular-array (non-identically distributed) maxima, and Stein's endpoint-variation computation.
- **Feasibility.**
  - *Medium* for the iid theorem: a product of non-identical c.d.f.s, Riemann-sum arguments, Weibull-type tails.
  - *Medium–hard* for an **m-dependent** or `D/D′` extension, which would be a genuine (small) advance on the stated conjecture.
    The library's Leadbetter machinery for stationary sequences would need a non-stationary version.
- **Outcome.** A **warning theorem**:
  > The GEV shape of seasonal maxima ≠ the daily tail index; the size of the shift is explicit.

  With dependence, it becomes a validity theorem for the conjecture.

### C6. Minimum-KS-distance threshold selection (Clauset et al.; Danielsson et al. KS method) (OPEN-EXPLICIT conjecture plus an unproved hypothesis)
- **Statement.** Choose `k*` to minimize the Kolmogorov–Smirnov distance between the empirical tail and the Pareto fit, then use the Hill estimator at `k*`.
  1. Is the joint limit of `(k*/n, √n(α̂_{k*} − α))` as conjectured?
  2. Does `t ↦ sup_s |Z₁(s,t)|` have a unique minimizer almost surely? Corollary 2 is conditional on this.
  3. What happens under general second-order regular variation, beyond exact Pareto and "Pareto above a break point"?
- **Sources.**
  - Drees, Janßen, Resnick & Wang, "On a minimum distance procedure for threshold selection in tail analysis", SIAM J. Math. Data Sci. 2 (2020),
    arXiv:1811.06433, https://arxiv.org/abs/1811.06433. The abstract:
    > "theoretical justifications for this selection procedure remain scant"

    Corollary 2 begins:
    > "If $t\mapsto\sup_{0<s\le1}|Z_1(s,t)|$ has a unique point of minimum $T$ a.s., then ..."

    Eq. (11) is introduced with:
    > "we conjecture that $(k_n^*/n, n^{1/2}(\hat\alpha_{n,k_n^*}-\alpha))\to(T^*, \ldots)$ weakly."

    On network data:
    > "asymptotic normality of the Hill estimator in this setting remains an open problem"

    (preferential attachment; status today unverified).
  - Danielsson, Ergun, de Haan & de Vries, "Tail index estimation: quantile-driven threshold selection", Bank of Canada SWP 2019-28,
    https://www.bankofcanada.ca/2019/08/staff-working-paper-2019-28/. This is a simulation horse race only; the paper proves no asymptotic theory for the KS-selected `k*`.
  - Belzile & Davison, "Choosing the threshold in extreme value analysis", arXiv:2606.28540 (June 2026), https://arxiv.org/abs/2606.28540,
    review §3.3/§5.2. In their simulations the KS variant of Danielsson et al. gives the lowest MSE for ξ < 0.25.
- **Why practitioners care.** The Clauset–Shalizi–Newman `poweRlaw` method is used across network science, and the Danielsson KS method in
  finance (`tea::mindist`). Drees et al. show that for exact Pareto data it chooses thresholds that are too high and has a non-normal limit.
- **Library has.** Hill consistency and normality, the exact-Pareto Hill iff (`tendstoInMeasure_hill_pareto_iff`), the Rényi representation, the
  uniform tail empirical process converging to Brownian motion in `D[0,1]`, and the Skorokhod space.
- **Missing.** Weighted approximations at the √n scale uniformly in `t` (Drees et al. Thm 1), argmin continuous-mapping theorems,
  and Hill at a *random* `k`.
- **Feasibility.**
  - *Medium* for a weaker formal warning: for exact Pareto, `k*/n` does not tend to 0 in probability, so the procedure does not reduce to an intermediate sequence.
  - *Hard* for conjecture (11) and the uniqueness hypothesis, which is a fine Brownian-functional question.
- **Outcome.** A **warning** (a widely used rule selects non-intermediate `k` and gives non-normal errors, so its usual CIs are invalid), or settling an explicit conjecture.

### C7. Bücher–Zhou "horse race" open list: rates, tests, and BM/POT second-order relations (OPEN-EXPLICIT)
- **Source.** Bücher & Zhou, Stat. Sci. 36(3) 360–378 (2021), https://doi.org/10.1214/20-STS795, arXiv:1807.00282, §6. Verbatim items:
  - "Asymptotic theory on further estimators based on the block maxima method, if possible allowing for a comparison between the imposed second order condition and those from the POT approach."
  - "In case the BM method yields to faster attainable rates of convergence than the POT approach (Section 2.1): are the obtained rates optimal?"
  - "Derive a test for which approach is preferably for a given data set ($H_0:\rho_{BM}\le\rho_{POT}$, or similar)."
  - "Block length choice and bias reduction for BM." (see C2)
  - "More results on the sliding block maxima method (non-heavy tailed case, multivariate case)." This is partly resolved: Bücher & Zanger
    (arXiv:2110.15576) give sliding PWM/GEV theory with `Ω^{sb} ≤_L Ω^{db}`; Bücher & Staud (arXiv:2308.13761, arXiv:2409.05529) cover U-statistics and the bootstrap.
    I did not find a sliding-blocks GEV-MLE theory for general ξ.
  - "A comparison of BM and POT second order conditions in the multivariate case."
  - "A comparison of return level/quantile estimation based on BM and POT, possibly incorporating an estimator for the extremal index."
  - "Extension to stochastic processes (max-stable processes and generalized Pareto processes)..."

  Also, §2.1:
  > "We conjecture that the same result [rate $n^{\rho/(1-2\rho)}$] holds true for many other estimators relying on the BM method"
- **Why practitioners care.** Annual maxima versus POT is the central methodological choice in hydrology (Deltares and USGS practice).
- **Library has.** Second-order regular variation (`ρ ≤ 0`), both MDA characterizations, block-maxima empirical c.d.f. convergence, Hill normality with bias `λ/(1−ρ)`, GEV and GPD MLE.
- **Missing.** The Drees–de Haan–Li (2003) relation between `ρ_BM` and `ρ_POT` (Table 2 in Bücher–Zhou: equal on `[−1,0)`, `ρ_BM = −1` when `ρ_POT < −1`), and any BM estimator CLT.
- **Feasibility.**
  - *Medium* for formalizing the known `ρ_BM`/`ρ_POT` relation. It is a statement about `−log F` versus `1−F`, both handled by the
    library's second-order machinery, and it tells practitioners when BM has the faster optimal rate.
  - *Hard* for the optimality, test and comparison items.
- **Outcome.** A formal decision aid (which method has the better optimal rate for a given second-order structure) and a basis for later items.

### C8. Adaptive choice of the level for estimating the second-order parameter ρ (OPEN-EXPLICIT, older source)
- **Source.** Beirlant, Caeiro & Gomes, "An overview and open research topics in statistics of univariate extremes", REVSTAT 10(1) (2012) 1–31,
  https://www.ine.pt/revstat/pdf/rs120101.pdf, §3.1.3:
  > "Such a crucial property can potentially be achieved if we compute $\hat\rho$ at its optimal level (see Caeiro et al., 2009), but the adaptive choice of such a level is still an open research topic."

  §4.4:
  > "Is it sensible to use bootstrap computational intensive procedures for threshold selection or there will be simpler techniques possibly related with bias pattern?"

  §4.5 asks: "And what about testing second-order and third-order conditions?"
  Belzile & Davison (2026, §8.2) still write:
  > "estimates of the second-order parameter $\rho$ are typically far too noisy to be useful"
- **Why practitioners care.** Reduced-bias Hill estimators (`evt0`, `tea`) need ρ̂. The key requirement is `(ρ̂ − ρ) log n = o_p(1)`.
- **Library has.** Second-order RV, Hill normality with bias, and Weissman at ρ ≤ 0, including the ρ = 0 cancellation.
- **Missing.** The Fraga Alves–Gomes–de Haan ρ-estimators, their consistency, and third-order conditions.
- **Feasibility.** *Hard* for the open part (an adaptive rule). *Medium* for verifying consistency of the standard ρ̂ at `k₁ = n^{1−ε}`, which is a known result.
- **Outcome.** A validity theorem for the bias-corrected Hill pipeline. The open part is probably beyond formal methods for now.

### C9. Seasonal or circular block maxima: variance advantage under non-stationarity (OPEN-EXPLICIT conjecture)
- **Source.** Bücher & Staud, "Bootstrapping estimators based on the block maxima method", arXiv:2409.05529v2, conclusion:
  > "Respective methods could be studied mathematically under a suitable triangular array structure, and we conjecture that advantages over the disjoint block maxima method will eventually show up in respective estimation variances."

  This concerns circular block maxima with within-block varying GEV parameters. The same section also says naive block bootstraps fail for sliding blocks, and that circular-block resampling works.
- **Why practitioners care.** Uncertainty for 100-year return levels from seasonal data (Bücher–Zanger's temperature case study).
- **Library has.** BM empirical c.d.f. convergence and GEV moments and PWMs. **Missing:** almost everything (triangular arrays, bootstrap).
- **Feasibility.** *Hard.* Listed for completeness.

### C10. Threshold selection by sequential goodness-of-fit tests: error-rate control (OPEN-EXPLICIT, essentially)
- **Source.** Belzile & Davison (2026), §8.1.1, on ForwardStop and StrongStop applied to nested GPD hypotheses `H_J ⊂ … ⊂ H_1`:
  > "these rely on independence of the null $p$-values ... The procedures described above do not provide independent null $p$-values, so the proofs of their properties fail."

  §5 (Bader et al. 2018) says there is a "lack of theoretical guarantees for the control of the false discovery rate".
- **Why practitioners care.** Automated threshold choice for many series (`eva::gpdSeqTests`).
- **Library has.** GPD likelihood and PBdH. **Missing:** goodness-of-fit statistics, multiple testing, dependence of p-values.
- **Feasibility.** *Hard, and off-mission* for this library.

### C11. Hsing's null-variance conjecture for linear models (RESOLVED by Buriticá–Wintenberger; verify, and it supports C1)
- **Source.** Buriticá & Wintenberger, arXiv:2212.13521, abstract:
  > "Regarding linear models, we prove that the asymptotic variance of classical index cluster-based estimators is null as first conjectured in [Hsing 1993]."

  Their conclusion still lists, as "a road for future research":
  > "a complete study of the tuning parameters $k,k'$ requires a careful analysis of the bias conditions for blocks"
- **Why practitioners care.** It explains why bootstrap intervals for θ collapse on ARMA-type data, and it matters for C1.
- **Library has.** Finite and infinite moving-average spectral tail processes, with `θ = max ψ^α / Σ ψ^α`.
- **Missing.** The ℓᵖ-block functionals and the estimator CLT.
- **Feasibility.** *Medium* for the deterministic core: for linear processes the spectral cluster `Q` is non-random up to shift, which makes the variance functional vanish. *Hard* for the full CLT.
- **Outcome.** A verified "super-efficiency" fact plus known-answer tests.

### C12. Hammersley–Clifford for extremal graphical models on non-decomposable graphs (OPEN-EXPLICIT in 2020; likely RESOLVED)
- **Source.** Engelke & Hitz, "Graphical models for extremes", JRSSB 2020, arXiv:1812.01734, Remark 2:
  > "it is an open problem whether they can be chosen to be homogeneous"

  (the clique factors of a multivariate Pareto density on a non-decomposable graph).
- **Status.** Engelke, Ivanovs & Strokorb, "Graphical models for infinite measures with applications to extremes", AAP 35(5) (2025),
  arXiv:2211.15769, prove a Hammersley–Clifford-type theorem. I did not verify that it settles homogeneity for non-decomposable graphs.
- **Practical relevance.** River-network flood models (`graphicalExtremes`).
- **Reach.** Low. The library has MRV, exponent measures, MGPD and spectral measures, but no densities of exponent measures and no graph theory.

### C13. Minor or unverified items
- **Hill asymptotic normality for preferential-attachment degree data.** Stated as open by Drees et al. (2020). Status today unverified. Out of reach (no network models).
- **Change-point detection in tail behaviour, censored-data EVT, and "SUE for weakly dependent data".** Beirlant–Caeiro–Gomes (2012, §4.5) name them as "challenging"; they are too vague to be single problems.
- **Markovich–Rodionov (2020).** They also state: "The impact of the heaviness of tail on the accuracy of the discrepancy method remains an open problem." This is narrow.

---

## 2. Ranking: top 5

Criterion: (practical value of the outcome) × (how explicitly open the problem is) × (feasibility with what the library already has).

| Rank | Candidate | Why | Feasibility | Outcome type |
|---|---|---|---|---|
| 1 | **C2** block/run-length choice for θ | Explicitly open; most of the machinery is already proved, including log-echo estimator-level inconsistency of short runs. The power-lag estimator version turns it into "no polynomial rule is universal" | easy–medium | warning theorem + recommendation (long blocks) |
| 2 | **C3** sliding-blocks consistency without β-mixing | Explicitly open; the library's α-mixing Chebyshev framework is exactly the right tool; `exdex::spm` users benefit | medium | validity theorem |
| 3 | **C1** PoT versus BM variance | Explicitly open, directly practical; there is a promising negative lead via Buriticá–Wintenberger (C11) and tail-process algebra on MA models | medium (conditional on published variance formulas) / hard (full) | recommendation or counterexample |
| 4 | **C4** GEV MLE on the full parameter space | Only just resolved (2025, one paper); covers what software does; removes the library's compact-set caveat | medium–hard | validity theorem (verification) |
| 5 | **C5** Stein seasonal maxima, dependent case | Climate-relevant; the iid theorem is formalizable and an m-dependent extension would partly settle a stated conjecture | medium (iid) / medium–hard (m-dependent) | warning theorem |

Runner-up: **C6** (Clauset/KS threshold). It has the highest practical visibility, but its open core (a Brownian argmin) is hard.
A medium-difficulty warning ("`k*/n ↛ 0` for exact Pareto") is achievable.

---

## 3. Cheap "known but unformalized" wins that support practice (not open problems)

These came up during the search. They are standard results, not research, but each fixes a real practitioner question and fits existing machinery.

- **Return level bias from ignoring clustering.** Using `P(M_m ≤ x) ≈ F(x)^{mθ}`, ignoring θ < 1 in the Fréchet domain multiplies block return
  levels by `θ^{−γ}` asymptotically. Library: `H^θ` limits and Weissman. *Easy.*
  Relevant to Fawcett & Walshaw (Environmetrics 2012), who find that standard POT "is liable to incur serious bias". I saw this only in a
  secondary source and did not verify the exact quote.
- **Declustered cluster maxima have the same tail index as the margins.** Under anticlustering,
  `P(M_r > u_n x)/P(M_r > u_n) → x^{−α}`, from `tendsto_blockRatio`. *Easy.* This justifies fitting the GPD to cluster maxima with the marginal ξ.
- **Rounded or tied data (Belzile–Davison §8.1.4).** Rounding to a fixed grid preserves regular variation, so Hill stays consistent. Rounding
  light-tailed data, for example exponential to geometric, destroys the domain of attraction: no GEV limit (Anderson 1970). *Easy.* This gives both a reassurance and a warning.
- **Hill confidence intervals under clustering are too narrow.** The asymptotic variance under dependence (Hsing 1991; Drees 2000) needs Hill
  normality for dependent data. The library has consistency only. *Medium–hard.*

---

## 4. Sources consulted (URLs)
- Bai, Kulik, Wang 2024: https://arxiv.org/abs/2409.17966 (HTML v2)
- Bai, Wang 2023: https://arxiv.org/abs/2110.07499. Quote: "we are not aware of any other examples ... θ and ϑ are both between 0 and 1 and yet not the same."
- Cissokho, Kulik: https://arxiv.org/abs/2005.11378
- Chen, Kulik (PoT expansions): https://arxiv.org/abs/2309.03163
- Buriticá, Wintenberger: https://arxiv.org/abs/2212.13521
- Bücher, Zhou (horse race): https://arxiv.org/abs/1807.00282 ; https://doi.org/10.1214/20-STS795
- Bücher, Zanger: https://arxiv.org/abs/2110.15576
- Bücher, Staud (bootstrap for BM): https://arxiv.org/abs/2409.05529 ; (U-statistics) https://arxiv.org/abs/2308.13761
- Carl, Padoan, Rizzelli 2025: https://arxiv.org/abs/2506.17448
- Stein 2017: https://doi.org/10.1093/biomet/asw070 (abstract only)
- Markovich, Rodionov: https://arxiv.org/abs/2009.02318
- Drees, Janßen, Resnick, Wang 2020: https://arxiv.org/abs/1811.06433
- Danielsson, Ergun, de Haan, de Vries: https://www.bankofcanada.ca/2019/08/staff-working-paper-2019-28/
- Belzile, Davison 2026: https://arxiv.org/abs/2606.28540
- Murphy, Tawn, Varty (Technometrics): https://arxiv.org/abs/2310.17999. No explicit open problem; the EQD method has no consistency theory (their conclusion: it "avoids a reliance on asymptotic theory").
- Beirlant, Caeiro, Gomes 2012: https://www.ine.pt/revstat/pdf/rs120101.pdf
- Engelke, Ivanovs (sparse structures review): https://arxiv.org/abs/2004.12182. No explicit open-problem list found.
- Huser, Wadsworth (spatial review): https://arxiv.org/abs/2007.00774 (the id 2007.00360 in the brief is wrong). No precise open problems found.
- Engelke, Hitz: https://arxiv.org/abs/1812.01734 ; Engelke, Ivanovs, Strokorb: https://arxiv.org/abs/2211.15769
- exdex vignette (block-size diagnostic `choose_b`): https://cran.r-project.org/web/packages/exdex/vignettes/exdex-vignette.html

**Not accessed:** Kulik & Soulier (2020) book, so any book-only open questions are missing here; the Scarrott–MacDonald review and the
Caeiro–Gomes papers (covered indirectly by Belzile–Davison 2026 and Beirlant–Caeiro–Gomes 2012); the Fawcett–Walshaw primary text.
