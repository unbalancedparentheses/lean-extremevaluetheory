# Roadmap

What it takes to be the best extreme value theory library, in six tracks: the **textbook layer**,
**research** (with priority to problems practitioners care about), **verification** (evidence that the
statements are the right ones, including review by human experts), **code quality and usability**,
**maintenance**, and **outreach**, plus one distinctive extra: a link to real EVT software, and a
**growth** track (H) that turns the library into something people use, cite and contribute to. See [`THEOREMS.md`](THEOREMS.md) for what is proved
and [`RESEARCH.md`](RESEARCH.md) for the research results.

`[x]` done, `[~]` partial, `[>]` in progress, `[ ]` missing.

## Ranked plan (2026-11-04)

Everything still open in this file, in the order to do it. The ranking puts first what:

- unblocks other work, or protects work already done;
- has a long lead time (expert review, accounts);
- costs little and buys a lot of trust.

Each tier can run in parallel internally. The sections below give the details.

**Tier 0: this week, mostly the maintainer (minutes each)**
1. Done (2026-11-04): the agents are running again
2. *you:* send [`docs/REVIEW.md`](docs/REVIEW.md) to two or three experts. Review takes weeks, so it
   should start before anything else (C)
3. Merge [#4](https://github.com/unbalancedparentheses/lean-extremevaluetheory/pull/4), one definition
   per concept. It already builds, and the statistics pull requests rebase on it
4. Done (2026-11-04): the GitHub–Zenodo integration is enabled, so `v1.0.0` will get a DOI (H.1)

**Next, in order (2026-11-05)**
1. *you:* read the paper, send the expert emails, submit to arXiv, post on the Lean Zulip; cut `v0.10.0` first so they point
   to a release with the GEV and Wilks results
2. *you:* get de Haan–Ferreira, Embrechts et al., Coles and Kulik–Soulier, to check citations (the agents had no access to the
   books; some theorem numbers and Coles's figures are from memory) and finish the novelty check
3. **Likelihood for approximate models, the main gap for practice:** block maxima from a law in a domain of attraction
   (Dombry–Ferreira 2019), then threshold excesses with a random number of exceedances
4. The Gumbel case `ξ₀ = 0` of GEV normality, consistency of the plug-in standard error, Wilks for `ξ₀ ≤ 0` and the GEV
5. Moment estimator normality for `γ ≤ 0`
6. First pull requests to Mathlib from `ForMathlib/`, then the link to R and Python (G)

**First release: `v0.9.0`, before the work in flight** (decided 2026-11-04). A citable release with
honest limits now does more than waiting for every proof. It does not wait for #4–#9; those ship in 0.x
and 1.0 releases.
- [x] CI fails on `sorry` and extra axioms (`Test/AxiomAudit.lean`, `scripts/check_source.py`)
- [x] Limitations section and "Use it in your project" in the README; downstream CI job
- [x] Independent AI review of the statements and claims by Codex; fix what it finds. This is AI review,
  and does not replace expert review
- [x] Non-vacuity tests for `powEchoProcess_antiClustering_iff`, `logEchoProcess_betaMixing_incompatible`
  and `logEcho_tendstoInMeasure_runsEstimator` (found by the Codex review; added after the release)
- [x] `CHANGELOG.md`, the tag and [GitHub release `v0.9.0`](https://github.com/unbalancedparentheses/lean-extremevaluetheory/releases/tag/v0.9.0)
  (2026-11-04), and the Zenodo DOI [10.5281/zenodo.23966373](https://doi.org/10.5281/zenodo.23966373), in `CITATION.cff` and the README
- [>] Library paper [`paper/evt-lean.tex`](paper/evt-lean.tex): drafted and reviewed twice by Codex; *you*
  submit to arXiv (check early whether you need an endorsement)
- [ ] *you:* send the expert emails and post on the Lean Zulip, with the release and paper links

**Tier 1: finish the work in flight** (sunk cost; ordered by how close each is)
5. [#7](https://github.com/unbalancedparentheses/lean-extremevaluetheory/pull/7) Tail-dependence
   estimation: theorems written, one file to fix
6. [#5](https://github.com/unbalancedparentheses/lean-extremevaluetheory/pull/5) Pickands and moment
   estimator normality: one proof, then the general-sample theorem
7. [#6](https://github.com/unbalancedparentheses/lean-extremevaluetheory/pull/6) GEV three-parameter MLE
   normality, then unconditional GEV return-level normality: the result practitioners rely on most
8. [#8](https://github.com/unbalancedparentheses/lean-extremevaluetheory/pull/8) Profile-likelihood
   intervals
9. [#9](https://github.com/unbalancedparentheses/lean-extremevaluetheory/pull/9) Mathlib v4.36: only
   once v4.36.0 is stable

**Tier 2: trust that runs by itself** (independent of tier 1, so in parallel with it)
10. Done (2026-11-04): axiom audit of every declaration in CI (H.7)
11. Done (2026-11-04): Comparator challenge on four headline theorems, in CI (H.7)
12. Architecture checks and the remaining gates against overclaiming (H.6, H.7)
13. Done (2026-11-04): specification tests for the newest results, and the seventh faithfulness audit (C)

**Tier 3: release 1.0**
14. Close the design pass:
    - split the `Statistics/` files;
    - stop using the `@[deprecated]` aliases;
    - fix the Mathlib deprecation warnings;
    - do the cleanup list.

    (Version 1.0, item 2)
15. Documentation matches the code: `THEOREMS.md`, README, website, blueprint entries (item 3)
16. Honest counts by status in the README (H.2); keep the Limitations section current
17. `CONTRIBUTING.md`, `CLAUDE.md`, code of conduct, templates and the credit rules (H.4)
18. `v1.0.0`, once the experts have replied and #4, #6 and #7 are in
19. A new version of the library paper for 1.0, if the review changes it
20. *you:* announce 1.0 on the Lean Zulip (F)
21. *you:* contact formal-mathfin and invite one or two collaborators (H.8)
22. Dependabot pull requests #1–#3, after checking that the website builds

**Tier 4: after 1.0, users and contributors**
23. Labels; the issue tracker as the only backlog; 10–15 good first issues; the open problems as
    `EVT-OP-…` issues (H.4, H.5)
24. A way in:
    - tutorial;
    - worked examples for the standard laws;
    - applied examples;
    - "how to find a result" guide;
    - onboarding, beginners' manual and troubleshooting pages.

    (D, H.4)
25. The theorem catalogue, the Hugging Face dataset (*you* create the account), `formalization.yaml` and
    the review deadline in CI (H.3, H.7)
26. *you:* decide on registering with Palomar (H.7)
27. One tagged release per Mathlib bump (E)

**Tier 5: research** (B)
28. Finish the novelty check of the Bai–Kulik–Wang answer, then the arXiv note on the echo process
29. Practical open problem 1, block and run length for the extremal-index estimators; then problems 2–6
30. Theoretical open problems, starting with the critical case `κ = 1` of the power-lag echo process

**Tier 6: textbook gaps** (A; most-used statistics first)
31. Statistics:
    - Hill interval with bias;
    - Ferro–Segers Theorem 1;
    - likelihood at `ξ = 0`;
    - GEV likelihood on the whole parameter space;
    - L-moments follow-ups;
    - bias-reduced estimators;
    - a random number of exceedances.
32. Processes and dependence:
    - Davis–Hsing cluster processes and cluster functionals;
    - the weighted tail empirical process and quantile process;
    - Brown–Resnick, Schlather and extremal-t;
    - hidden regular variation;
    - stochastic volatility.
33. Theory:
    - the parametric stable family and its tails;
    - Π-variation;
    - two-sided second-order inequalities;
    - rates of convergence of maxima;
    - records;
    - domains of attraction for processes;
    - sharp Kesten–Goldie tails (needs the renewal theorem).

**Tier 7: long term**
34. Upstream `ForMathlib/` to Mathlib, then regular variation and the EVT core; a talk (F)
35. Executable estimators cross-checked against R and Python (G)
36. Optional: a Docker image, only if a contributor needs it (H.4)

---

## Version 1.0

What "finished" means for a first release: the running work merged, a consistent design, documentation
that matches the code, a way in for new users, and review by people other than the AI that wrote the
statements. Everything after that (further textbook chapters, open problems, upstreaming, executable
estimators) is listed in sections A–G and is not needed for 1.0. Updated 2026-11-04.

**Owner:** *agent* = done by Claude Code agents; *you* = needs the maintainer (sending, submitting,
posting, deciding).

1. [>] **Finish the work in flight** (*agent*; paused, one draft pull request per task, see the table below)
   - [>] One definition per concept: `upperQuantile`/`survivalQuantile`/`survival` (`UpperQuantile.lean`)
         and one GPD survival function done and building; the remaining duplicates of the audit are
         listed in the pull request
   - [>] Pickands and moment estimator normality: moment estimator `γ > 0` done; the Pickands theorem for
         uniform samples is written but its last proof does not build yet
   - [>] GEV three-parameter MLE normality (step 1 of 3, domination near the moving endpoint, mostly
         done), then unconditional GEV return-level normality
   - [>] Profile-likelihood intervals (Wilks' theorem, GPD first): early, the log-likelihood expansion
   - [>] Nonparametric tail dependence: the consistency theorems for the empirical stable tail dependence
         function, `χ̂` and the Pickands function estimator are written; the population file does not
         build yet
2. [ ] **Close the design pass** (*agent*)
   - [ ] Split the oversized `Statistics/` files (waits for item 1)
   - [ ] Stop using `@[deprecated]` aliases inside the library and tests (the aliases stay for
         downstream users; [`docs/DESIGN.md`](docs/DESIGN.md) keeps them six months)
   - [ ] Fix the Mathlib deprecation warnings in `Statistics/` and in the newly promoted files
         (`GEVDomain.lean`, `ExtremalIndexEstimatorsIid.lean`: `dif_pos`, `if_pos`, `Set.mem_setOf_eq`)
   - [ ] `CHANGELOG.md` and a tagged release `v1.0.0`
3. [ ] **Documentation matches the code** (*agent*)
   - [ ] [`THEOREMS.md`](THEOREMS.md), the README and the website list every merged result
   - [ ] Every new file has a blueprint entry
   - [ ] Specification tests for the newest results (return levels, intervals, SRE/GARCH,
         extremal-index estimators, the 1.0 statistics results)
   - [ ] Seventh faithfulness audit (everything since the sixth)
4. [ ] **A way in for new users** (*agent*)
   - [ ] Tutorial: your first extreme value theory proof in Lean
   - [ ] Worked examples for the standard laws
   - [ ] "How to find a result" guide
5. [ ] **Trust and visibility** (*you*, with drafts from an agent)
   - [ ] Human expert review with [`docs/REVIEW.md`](docs/REVIEW.md) (see C)
   - [ ] Finish the novelty check, then the arXiv note on the echo process (see B)
   - [ ] Announce on the Lean Zulip (see F)

6. [ ] **Ready for users and contributors** (*agent*, with accounts from *you*; details in H)
   - [ ] Release `v0.9.0`, then `v1.0.0`, with a Zenodo DOI, badges and a "use it in your project" section,
         checked by a downstream CI job (H.1)
   - [~] Honest counts and a Limitations section in the README (H.2): Limitations done
   - [ ] `CONTRIBUTING.md`, `CLAUDE.md`, labels, issues and the first good first issues (H.4)
   - [ ] Open problems filed as numbered issues (H.5)
   - [ ] Architecture checks in CI (H.6)
   - [~] Axiom audit in the build (done), the Comparator challenge, the review deadline and the gates against
         overclaiming (H.7)

### Work in flight

**Status (2026-11-05):** nothing running. All the tasks are merged: #4–#8, the review guide, the comparison with Hirata and its
improvements, the Comparator challenge, the catalogue, the seventh and eighth audits, the contributor docs and the
examples.

### Waiting on the maintainer

- [ ] Decide on the three Dependabot pull requests (#1–#3: nokogiri, faraday, concurrent-ruby for the
      website); an agent can check that the site still builds and merge them
- [ ] Expert review: send [`docs/REVIEW.md`](docs/REVIEW.md) to two or three extreme value theorists
      (an agent can draft the emails)
- [ ] Novelty check of the Bai–Kulik–Wang answer against Kulik–Soulier's examples (needs the physical
      book or an expert), then submit the arXiv note (an agent can draft it)
- [ ] Post the Lean Zulip announcement (an agent can draft it)
- [ ] Confirm the deprecation policy proposed in [`docs/DESIGN.md`](docs/DESIGN.md): aliases kept at
      least six months and one Mathlib bump
- [ ] Growth (H): create a Hugging Face account or organization for the dataset; approve and send the contact to formal-mathfin;
      submit the library paper; decide on registering with Palomar; send the collaborator invitations

### Cleanup to do

- [ ] Remove the five task worktrees (about 43 GB) once their work is merged
- [ ] Fix the remaining Mathlib deprecation warnings (about 18: `Statistics/`, `GEVDomain.lean`,
      `ExtremalIndexEstimatorsIid.lean`) after the statistics agents finish
- [ ] Rename the remaining `Statistics/` lemmas whose names still contain `gpdSurvival'`
- [ ] In the tests, replace `iidLaw_cdf` (`Test/NonVacuity/Processes.lean`) and `gumbelLaw_real_Iic`
      (`Test/NonVacuity/Multivariate.lean`) by the bridge's `hasLaw_measure_iff` and `measureReal_Iic`
- [ ] `Statistics/Hill.lean` still converts by hand between `cdf (P.map Y)` and the survival function;
      use `CDFBridge` instead
- [ ] Delete each `wip/…` branch on GitHub when its pull request is merged, and the seven superseded
      branches now (`wip/<agent-id>`, `wip/<agent-id>-snapshot`, `wip/<task>-snapshot`), whose content
      is in the task branches

Done in the current round (merged to `main`): names and namespaces; oversized files split outside
`Statistics/`; the law bridge (`CDFBridge.lean`); test helpers promoted and `docs/DESIGN.md`; the
weekly Mathlib bump workflow and deprecation fixes; the second open-problems survey.

### After 1.0

In order: the remaining textbook gaps (parametric stable family, Davis–Hsing cluster processes,
Brown–Resnick processes, bias-reduced estimators; see A); open problems, practical ones first (block
and run length for extremal-index estimators, then the rest of B); upstreaming `ForMathlib/` to Mathlib
(see F); executable estimators checked against R and Python (see G).

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
- [>] GEV: joint normality of the 3-parameter MLE (missing: Hessian domination near a moving endpoint,
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
- [>] Profile-likelihood intervals (Coles §2.6.6)
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
- [>] Nonparametric estimation: empirical tail dependence function / stable tail dependence
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
Second survey (2026-10-25, [`docs/OPEN_PROBLEMS_SURVEY2.md`](docs/OPEN_PROBLEMS_SURVEY2.md)), top candidates:
- [ ] Falk (2015): is the limit of a D-norm track idempotent? (a small 2-d construction may answer no)
- [ ] Leonetti–Khorrami Chokami (2022): is the max-domain of attraction a Borel set, and of which class?
- [ ] Strokorb–Schlather: existence of minimal dependency sets for given extremal coefficients
- [ ] Does d-separation characterize extremal conditional independence in recursive max-linear models?
- [ ] Sharp upper bound of Spearman's ρ given Kendall's τ for extreme-value copulas

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
      independent of the AI that wrote the statements. Send to two or three extreme value theorists
      (e.g. Kulik, Segers, Drees, Kytölä's group), fix what they find, and list the reviewers and the
      reviewed statements in [`FAITHFULNESS.md`](FAITHFULNESS.md)

---

## D. Code quality and usability

### Consolidation
- [>] Unify the three tail-quantile definitions
- [x] One namespace for the `Minimality` results (`Classical*` files use `ExtremeValueTheory.Minimality`,
      `Dependence*` files do not)
- [x] Rename "escape mass" (clashes with Abadi–Freitas–Freitas): now "late-return mass"
- [x] Rename `gpdSurvival` / `gpdSurvival'` so the `ξ < 0` case cannot be picked by mistake
      (`gpdSurvivalNonneg` / `gpdSurvivalAll`)
- [x] Fix misleading `_of_lt_one` names (now `_of_summable_rpow`; old names are deprecated aliases)
- [>] Remove duplicate helpers
- [x] Promote helper lemmas from the test files into the library (e.g. the exponential law is not
      subexponential; uniqueness of the regular-variation index)
      (done 2026-10-27; conventions in [`docs/DESIGN.md`](docs/DESIGN.md))

- [>] Design pass: one definition per concept is still running. Done: names and namespaces;
      oversized files split outside `Statistics/`; one representation of laws (`CDFBridge.lean`);
      test helpers promoted; conventions in [`docs/DESIGN.md`](docs/DESIGN.md)
- [ ] **Afterwards:** split the oversized `Statistics/` files (deferred while statistics agents edit
      them); migrate remaining uses off the `@[deprecated]` aliases and then delete the aliases; rebase
      the in-flight agent branches onto the new names

### Documentation
- [ ] `THEOREMS.md` and the website's "What is proved" list: add the newest results
- [ ] Every new file has a blueprint entry

### Usability
- [ ] Tutorial: "your first extreme value theory proof in Lean", one example end to end (e.g. proving
      that a given law is in the Fréchet domain and applying the Hill estimator's consistency to it)
- [ ] Worked examples for the standard distributions (Pareto, exponential, uniform, Gumbel, GPD, GEV,
      Student t, Cauchy), applying the headline theorems; the non-vacuity tests are a starting point
- [ ] Applied examples in `Examples/Applications/`, each a concrete problem ending in one statement the
      build checks, and each importing only the umbrella `ExtremeValueTheory` as a downstream project does:
      a 100-year flood return level, a reinsurance layer, a tail index estimated with Hill. Link them from
      [`docs/PRACTITIONERS.md`](docs/PRACTITIONERS.md)
- [ ] A stable public API: after the design pass, deprecate before removing and keep a `CHANGELOG.md`
- [ ] A short "how to find a result" guide (blueprint, API docs search, `THEOREMS.md`, naming conventions
      in `docs/DESIGN.md`)

---

## E. Maintenance

- [x] On the latest stable Mathlib (v4.35.0, checked 2026-10-27)
- [x] Trial bump to v4.36.0-rc1 builds (branch `wip/mathlib-v4.36-trial`; 23 files, all from `Set`
      becoming a structure); Mathlib deprecation warnings outside `Statistics/` fixed on v4.35.0
- [x] Regular bumps: a scheduled CI job that tries the latest Mathlib and opens a pull request
- [ ] Tagged releases, starting with `v1.0.0` (then one per Mathlib bump), so other projects can depend on a fixed version
- [ ] Keep the nightly independent kernel check and the specification tests green on every bump

---

## F. Outreach

- [ ] Announce the library on the Lean Zulip
- [ ] Upstream `ForMathlib/` (vague convergence, Poisson random measures, mixing, Skorokhod space,
      delta method, Wald intervals, …) as a series of small PRs; plan in
      [`UPSTREAMING.md`](ExtremeValueTheory/ForMathlib/UPSTREAMING.md)
- [ ] Then regular variation and the EVT core
- [ ] A talk (Lean Together, a Lean or probability seminar) and the arXiv note (see B)

---

## G. A link to real EVT software

The distinctive extra, after A–F: small executable reference versions of the main estimators (Hill,
Pickands, moment, PWM/L-moments, GPD/GEV maximum likelihood, return levels, extremal-index estimators),
tested on the same data against R (`evd`, `ismev`, `extRemes`, `POT`, `exdex`) and Python
(`scipy.stats`, `pyextremes`). The aim is to catch convention bugs in widely used packages, like the
sign of scipy's GEV shape, rather than only document them in
[`docs/PRACTITIONERS.md`](docs/PRACTITIONERS.md).

- [ ] Executable (`Float`) versions of the estimators, each linked to the definition it implements
- [ ] Cross-check scripts against R and Python on shared test data, run in CI
- [ ] A report of any disagreements with the packages

---

## H. Growth

How the library gets users, citations and contributors. Modelled on
[formal-mathfin](https://github.com/formal-applied-math/formal-mathfin), a Lean library of mathematical
finance. In six months it reached 49 stars, 17 forks, 7 contributors (plus a bot) and 9 releases, with
an arXiv paper. What it did that we do not yet do:

- a release with a DOI in its first month;
- its results published as a Hugging Face dataset;
- honest counts and a Limitations section in its README;
- issues with labels and good first issues, each specified so a stranger can start from it;
- open problems filed as numbered issues;
- architecture rules enforced by tests;
- reviews that CI forces to happen, and gates against claims stronger than the proof;
- applied examples that end in a statement the build checks;
- other people's work ported with credit.

What we already do better: a complete independent kernel check that runs in CI (their kernel replay has
not completed, and Comparator is not in their CI), a blueprint, mutation and junk-value tests,
faithfulness audits. Everything else on their list is below.

Their commit counts are the lesson about contributors (2026-11-04): the maintainer has 1,357, one
contributor has 560, and nobody else has more than 12. One strong collaborator did far more than all the
small contributions together, so direct outreach (H.8) matters at least as much as good first issues.

**What we do not copy:**

- their autoformalization pipeline (`formal-foundry`): its prover silently did not run for two months
  while CI stayed green. Documenting our agent workflow (H.4) gives most of the benefit;
- the weight of their process: a 31 KB `CLAUDE.md`, a 210 KB ledger file and eight-lens review panels. We
  take the review deadline and the gates in H.7, and keep them small.

**Owner:** *agent* unless marked *you*.

### H.1 Releases, citation and use as a dependency
- [>] Release early: `CHANGELOG.md` and the tag `v0.9.0` with a GitHub release, and the library paper
      (H.8) right after, as formal-mathfin did (a release three weeks after starting, the paper a week
      later). Each tag pins Lean and Mathlib; then one tag per Mathlib bump (see E)
- [x] The GitHub–Zenodo integration is enabled, so every GitHub release gets a permanent DOI (no test
      releases), and [`.zenodo.json`](.zenodo.json) holds the metadata
- [x] The DOI is in [`CITATION.cff`](CITATION.cff) and the README
- [~] README badges: build, kernel check, blueprint and DOI done; then arXiv and the dataset when they exist
- [x] README section "Use it in your project": the `require` lines for `lakefile.toml`,
      `lake exe cache get`, `import ExtremeValueTheory`
- [x] `Downstream/`: a client project that only imports the library and states one headline theorem,
      and a weekly workflow that builds it in a fresh project requiring this repository (catches
      packaging breakage that our own build cannot see)

### H.2 Honest numbers in the README
- [ ] A status for every headline result: `full`, `library_wrapper` (restates Mathlib) or
      `reduced_core` (weaker than the result it is named after), taken from the catalogue in H.3
- [ ] `scripts/coverage_report.py`: counts by status and by area, printed into the README by CI
- [x] A **Limitations** section in the README naming every result weaker than its textbook form
      (GEV MLE on a compact parameter set, the `ξ ≠ 0` restrictions, iid-only estimators, the multivariate
      generalized Pareto hypothesis `G(x ∧ 0) > 0`, …), drawn from the scope notes in
      [`FAITHFULNESS.md`](FAITHFULNESS.md)

### H.3 The theorem catalogue as a dataset
- [ ] `catalogue/*.json`, one file per area. Each entry has:
      - an id and a name;
      - the source (book and theorem number);
      - the Lean name and file, and the statement;
      - the status from H.2, and a scope note saying what is left out.

      Generate it from [`THEOREMS.md`](THEOREMS.md) and the blueprint's `\lean{}` names
- [ ] A CI check that every catalogue entry's Lean name resolves and its statement matches `#check`
- [ ] *you:* create a Hugging Face account or organization; then a workflow that publishes the catalogue
      as a dataset on every release (the AI theorem-proving community is a large audience)
- [ ] `formalization.yaml`: machine-readable provenance (sources, AI-written parts, human-reviewed
      parts after C, axioms), generated by a script

### H.4 Contributors
- [ ] `CONTRIBUTING.md`: setup with the Mathlib cache, where things go, the rules (no `sorry`, standard
      axioms, faithful docstrings, reuse before writing, register new files), and the pull request
      checklist (`lake build`, `lake build Test`, blueprint names)
- [x] `CODE_OF_CONDUCT.md`, a pull request template and issue templates (bug in a statement, missing
      result, proof request)
- [ ] `CLAUDE.md`, plus an `AGENTS.md` that points to it: the agent workflow used here. It covers:
      - worktrees and the instant `.lake` clone;
      - the `lake` path, and retrying on "too many open files";
      - checkpoint commits pushed to a `wip/<task>` branch with a draft pull request;
      - the verification list before merging.
- [ ] Labels: `area:*` (classical, POT, statistics, dependence, multivariate, processes, heavy tails,
      ForMathlib), `type:*` (proof, refactor, docs, tooling, research), `difficulty:*` (small, medium,
      hard), `status:*` (ready, blocked-upstream, research), `open-problem`, `good first issue`.
      Document them in `docs/ISSUE_LABELS.md` and create them with `gh label create`
- [ ] Make the issue tracker the only backlog: move the open items of A–G into issues, and keep only the
      strategy in this file, linking the issues
- [ ] 10–15 `good first issue` items, for example:
      - a worked example for one standard law (see D, Usability);
      - known-answer tests for a recent result;
      - the unbiasedness of the sample probability-weighted moments `b_r` (A.2);
      - the bridge `tailCount = exceedCount` (from PR #4);
      - a docstring that cites the wrong theorem number.

      Each one has the sections Context, Task, Acceptance criteria and Pointers, and names the exact
      lemmas and files, so a stranger can start from the issue alone. Make this the proof-request template
- [ ] `docs/ONBOARDING.md`: from clone to a merged pull request, with one first contribution done as an
      example
- [ ] A Contributors section in the README crediting each person by what they did; CI checks that a
      first-time author has added themselves
- [ ] Credit in the history: merge contributions with a merge commit, never a squash, so each person's
      commits reach `main` as they wrote them. Contributors put their own name on the `Copyright` and
      `Authors:` lines of their files, and a `.mailmap` covers differing git names. Write this into
      `CONTRIBUTING.md`
- [ ] `docs/BEGINNERS.md`: Lean and the library for mathematicians who have never used Lean, with
      exercises whose solutions are checked by the build
- [ ] `docs/TROUBLESHOOTING.md`: the setup failures we have hit (Mathlib cache, `lake` not on `PATH`,
      "too many open files", stale `.lake`, toolchain mismatch)
- [ ] Optional, only if a contributor reports needing it: a Docker image with the toolchain and a prebuilt
      Mathlib, published by CI to the GitHub container registry, for contributors who cannot install elan.
      It must not need a registry login. formal-mathfin needs its image partly because BrownianMotion
      compiles from source; we depend only on Mathlib, so `lake exe cache get` should be enough

### H.5 Open problems as issues
- [ ] One issue per problem in [`docs/PRACTICAL_OPEN_PROBLEMS.md`](docs/PRACTICAL_OPEN_PROBLEMS.md)
      and [`docs/OPEN_PROBLEMS_SURVEY2.md`](docs/OPEN_PROBLEMS_SURVEY2.md), numbered `EVT-OP-001`, …,
      labelled `open-problem`. Each issue gives the source and quote, why it matters, and what the
      library already has
- [ ] `EVT-OP-001`: block and run length for the extremal-index estimators (the first practical problem
      in B)

### H.6 Architecture checks in CI
- [ ] `scripts/check_architecture.py`, run in CI:
      - every file is imported by `ExtremeValueTheory.lean`;
      - every module imports a library module or is imported by one (no orphans);
      - `ForMathlib/` imports only Mathlib and `ForMathlib/`.
- [ ] A duplicate-definition check that flags two definitions with the same body (automates the audit
      of PR #4)
- [ ] After the design pass: no use of a `@[deprecated]` alias inside the library or the tests
- [ ] An admission rule, as a short section at the top of this file: what the library is not trying to be
      (the largest theorem count), when a new result is worth adding (it is used by another module, or
      connects two parts of the library), and what stays out (mathematics Mathlib lacks and that we should
      not build ourselves, labelled `status:blocked-upstream`)

### H.7 Trust machinery that runs by itself
- [x] **Axiom audit in the build.** [`Test/AxiomAudit.lean`](Test/AxiomAudit.lean) checks every declaration
      in the library, not a list of headline theorems, so a `sorry` or an extra axiom anywhere fails CI
- [ ] **Comparator challenge.**
      - `Challenge.lean` states three to five headline theorems with `sorry`, using only Mathlib's
        definitions: Fisher–Tippett–Gnedenko, Pickands–Balkema–de Haan, consistency of the Hill
        estimator, the answer to Bai–Kulik–Wang.
      - `Solution.lean` proves them from the library.
      - `lake comparator`, in Lean core since v4.35.0, checks in a sandbox that the two files state the
        same theorems, that the proofs use only the standard axioms, and that the kernel accepts them.
        Add the nanoda kernel too.
      - Run it in CI and on every release.

      This lets a skeptical reader trust the headline statements after reading one short file that
      imports nothing but Mathlib, instead of our definitions
- [ ] **Palomar registry.** [Palomar](https://palomar-registry.org), incubated by the Lean FRO and ICARM,
      records a fixed commit and a few declarations, re-checks the proof and publishes the exact statement
      and the review's comments. It is a filter, not an endorsement or a novelty claim. Submit the Comparator
      challenge with `formalization.yaml` (*agent* prepares; *you* decide on registering, which publishes
      the review). This is outside review while we wait for experts (see C), not a replacement for them
- [ ] **A deadline for reviews.** CI fails when the headline theorems (the catalogue in H.3) have grown more
      than a set number past the last audit recorded in [`FAITHFULNESS.md`](FAITHFULNESS.md); formal-mathfin
      allows 12 entries. A script cannot judge an audit, but it can check that one happened. Each audit ends
      in a ranked list of fixes, filed as issues
- [ ] **Gates against overclaiming**, in `scripts/`, run in CI:
      - an entry with status `full` cannot rest on a theorem proved by `rfl` or by unfolding a definition;
      - [x] search tactics (`exact?`, `apply?`) and trust-extending commands (`native_decide`, new
        `axiom`s) cannot appear in committed source ([`scripts/check_source.py`](scripts/check_source.py));
      - each catalogue entry stores a hash of the inputs it was checked under, and CI fails when they change
        without a new check, so a stale claim cannot survive.
- [ ] Machine-readable provenance in `formalization.yaml` (see H.3)

### H.8 Papers and partners
- [ ] A library paper on arXiv, "A formally verified library of extreme value theory in Lean 4",
      before the echo-process note in B (*agent* drafts, *you* submit). A library paper is what people
      cite
- [ ] Contact formal-mathfin (Raphael Coelho). Their `ExtremeValue.lean`, `GeneralizedPareto.lean` and
      `PoissonMaxima.lean` (about 900 lines) overlap a small part of ours, and their risk measures
      (value-at-risk, expected shortfall) are where extreme value theory is used. Propose that they
      depend on this library for extremes, or a bridge file between the two (*agent* drafts, *you*
      send)
- [ ] Compare our statements of Fisher–Tippett–Gnedenko, Pickands–Balkema–de Haan and Karamata with
      Hirata's independent Isabelle developments ([Extreme Value Theory](https://isa-afp.org/entries/Extreme_Value_Theory.html),
      [Regular Variation](https://isa-afp.org/entries/Regular_Variation.html), Archive of Formal Proofs,
      September 2026), which the first related-work search missed. Two independent statements of one theorem
      are a real check on faithfulness. Then contact Hirata (*agent* drafts, *you* send)
- [ ] Search for other Lean projects with results on extremes, regular variation or heavy tails, and
      port or link them with credit to their authors. Porting can also bring in the author: formal-mathfin
      ported Robert Martin's American put and SVI work, and lists them as a contributor
- [ ] Invite one or two strong collaborators directly: people already working on probability in Lean or on
      extreme value theory, each offered a specific area to own (see the commit counts at the top of H)
      (*agent* drafts, *you* send)
