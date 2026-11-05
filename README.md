# Extreme Value Theory in Lean

[![Build](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/build.yml/badge.svg)](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/build.yml)
[![Kernel check](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/kernel-check.yml/badge.svg)](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/kernel-check.yml)
[![Blueprint](https://github.com/unbalancedparentheses/lean-extremevaluetheory/actions/workflows/blueprint.yml/badge.svg)](https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23966372.svg)](https://doi.org/10.5281/zenodo.23966372)

A library of extreme value theory in [Lean 4](https://lean-lang.org), built on
[Mathlib](https://github.com/leanprover-community/mathlib4). It covers the limits of maxima, domains of
attraction, regular variation, peaks over threshold, stable laws and heavy tails, the statistics of
extremes (estimators, likelihood, return levels, confidence intervals), extremes of dependent sequences,
multivariate extremes, point processes and the Skorokhod space.

The library has about 113,000 lines and 4,770 theorems and lemmas. It contains no `sorry`, and CI checks
that all 10,677 of its declarations depend only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Written audits compare 191 main statements and definitions with the literature: they record
114 as faithful, 60 as faithful within a stated scope, and 17 as differing from the cited form while correct
as stated ([`FAITHFULNESS.md`](FAITHFULNESS.md)). The [theorem catalogue](catalogue/) lists 232 headline results, each
with its source, its statement as Lean reports it, and what it leaves out. Judged strictly against the result
each is named after, 147 are `full`, 2 are `wrapper` (they restate Mathlib), and 83 are `reduced`: a special case,
an extra hypothesis, or part of the conclusion assumed. The gap is widest in statistics and likelihood, where 36
of 50 are `reduced`. **No human expert has reviewed the library yet.** The
statements, tests and audits were written with AI assistance, so those audits are not independent; see
[Limitations](#limitations).

Here, for example, is the Fisher–Tippett–Gnedenko theorem, from
[`SelfSimilarCDF.lean`](ExtremeValueTheory/SelfSimilarCDF.lean):

```lean
theorem CumulativeDistributionFunction.IsExtremeValueDistr.classification
    {G : CumulativeDistributionFunction} (hG : G.IsExtremeValueDistr) :
    (∃ (A : AffineIncrEquiv), A • G = standardGumbelCDF) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ), A • G = standardFrechetCDF hξ) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ), A • G = standardWeibullCDF hξ)
```

`G.IsExtremeValueDistr` says that $`G`$ is non-degenerate and is the limit of $`F(a_n x + b_n)^n`$ at its
continuity points, for some distribution function $`F`$ and affine normalizations. `A • G` is $`G`$ after
an increasing affine change of variables. So every limit law of normalized maxima is, up to type, Gumbel,
Fréchet or Weibull.

## Main results

- **Limits of maxima.** Besides the classification above, a distribution function is max-stable if and only
  if it is an extreme value distribution
  ([`isMaxStable_iff_isExtremeValueDistr`](ExtremeValueTheory/GEV/MaxStable.lean)).

- **Domains of attraction.** $`F`$ is in the domain of attraction of the Fréchet law $`\Phi_\alpha`$ if and
  only if $`1-F`$ is regularly varying with index $`-\alpha`$
  ([`isInMDAFrechet_iff`](ExtremeValueTheory/DomainOfAttraction/Frechet.lean)). It is in the domain of the
  Weibull law $`\Psi_\alpha`$ if and only if it has a finite right endpoint $`x_F`$ and
  $`t \mapsto 1-F(x_F-t^{-1})`$ is regularly varying with index $`-\alpha`$
  ([`isInMDAWeibull_iff`](ExtremeValueTheory/DomainOfAttraction/Weibull.lean)). De Haan's auxiliary-function
  characterization gives the Gumbel domain
  ([`isInMDAGumbel_iff`](ExtremeValueTheory/DomainOfAttraction/GumbelNecessity.lean)), and $`F \in \mathrm{MDA}(H_\gamma)`$ if and only if the tail quantile function is extended regularly varying with
  index $`\gamma`$
  ([`isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile`](ExtremeValueTheory/DomainOfAttraction/Quantile.lean)).
  The normal law is in the Gumbel domain, with explicit norming constants
  ([`tendsto_standardNormalCDF_pow`](ExtremeValueTheory/DomainOfAttraction/Examples.lean)).

- **Peaks over threshold (Pickands–Balkema–de Haan).** For every $`\xi \in \mathbb{R}`$, $`F \in \mathrm{MDA}(H_\xi)`$ if and only if there is a scale $`\beta(u) > 0`$ with

  ```math
  \frac{\bar F(u+\beta(u)x)}{\bar F(u)} \to \bar G_{\xi,1}(x)
  ```

  uniformly in $`x \ge 0`$ as $`u \uparrow x_F`$
  ([`isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival`](ExtremeValueTheory/PeaksOverThreshold/Converse.lean)).

- **Regular variation.** Karamata's theorem: if $`F`$ is measurable and regularly varying with index
  $`-\alpha`$, $`\alpha > 1`$, then $`\int_x^\infty F \big/ (xF(x)) \to 1/(\alpha-1)`$
  ([`IsRegularlyVarying.tendsto_integral_Ioi_div_of_measurable`](ExtremeValueTheory/RegularVariation/KaramataConverse.lean)).
  Breiman's lemma: if $`X, Y`$ are independent, $`P(X>x)`$ is regularly varying with index $`-\alpha`$,
  $`Y \ge 0`$ and $`E[Y^{\alpha+\varepsilon}] < \infty`$, then $`P(XY>x)/P(X>x) \to E[Y^\alpha]`$
  ([`tendsto_measure_mul_div_measure`](ExtremeValueTheory/RegularVariation/Breiman.lean)).

- **Stable laws.** The generalized central limit theorem with textbook constants. For example, for
  $`1 < \alpha < 2`$, with a regularly varying tail of index $`-\alpha`$ and tail balance $`p`$, the laws of
  $`(X_1+\dots+X_n-nEX)/a_n`$ converge to the stable law with characteristic function
  $`\exp\big(-\Gamma(1-\alpha)\cos(\pi\alpha/2)|t|^\alpha(1-i(2p-1)\operatorname{sign}(t)\tan(\pi\alpha/2))\big)`$
  ([`tendsto_map_convPow_sub_of_isRegularlyVarying_of_one_lt'`](ExtremeValueTheory/StableLaws/Constants.lean)).

- **Heavy tails and ruin.** If $`\mu`$ is subexponential and the count $`N`$ has an exponential moment, then
  $`P(S_N>x)/\bar F(x) \to E[N]`$
  ([`IsSubexponential.tendsto_tail_compound_div`](ExtremeValueTheory/HeavyTails/RandomSums.lean)). With
  regularly varying claims of index $`-\alpha`$, $`\alpha > 1`$, and loading $`\rho > 0`$, the
  Pollaczek–Khinchine ruin function satisfies $`\psi(u)/(u\bar F(u)) \to 1/(\rho m(\alpha-1))`$
  ([`tendsto_pkRuin_div_mul_tail`](ExtremeValueTheory/HeavyTails/Ruin.lean)).

- **Tail estimators.** For iid data with a second-order regularly varying tail quantile function,
  $`k \to \infty`$, $`k/n \to 0`$ and $`\sqrt{k}A(n/k) \to \lambda`$, the Hill estimator satisfies

  ```math
  \sqrt{k}\,(H_{k,n}-\gamma) \Rightarrow \mathcal{N}\Big(\frac{\lambda}{1-\rho},\ \gamma^2\Big)
  ```

  ([`tendstoInDistribution_hill`](ExtremeValueTheory/Statistics/HillNormality.lean)). The Pickands estimator is
  asymptotically normal for every shape
  ([`tendstoInDistribution_pickands`](ExtremeValueTheory/Statistics/PickandsNormality.lean)), and the moment
  estimator for $`\gamma > 0`$. Weissman's extreme quantile estimator is also covered.

- **GEV likelihood.** For an iid GEV sample with $`\xi_0 > -1/2`$, $`\xi_0 \ne 0`$, a maximum likelihood estimator on
  a compact parameter set with the true parameter in its interior is jointly asymptotically normal, with the
  inverse Fisher information as its covariance
  ([`tendstoInDistribution_gevMLE`](ExtremeValueTheory/Statistics/GEVMLENormality.lean)), and so is the return level
  ([`tendstoInDistribution_gevMLEReturnLevel`](ExtremeValueTheory/Statistics/GEVReturnLevelNormality.lean)).

- **Wilks' theorem and profile likelihood.** For an iid GPD sample with $`\xi_0 > 0`$, the deviance converges to
  $`\chi^2_2`$ and the profile deviance to $`\chi^2_1`$
  ([`tendstoInDistribution_gpdProfileDeviance`](ExtremeValueTheory/Statistics/GPDWilks/Profile.lean)), so the
  profile-likelihood sets for the shape, the scale and a return level have the coverage they claim
  ([`tendsto_measure_mem_gpdReturnLevelProfileInterval`](ExtremeValueTheory/Statistics/GPDWilks/Coverage.lean)).

- **Likelihood and return levels.** For an iid $`\mathrm{GPD}(\xi_0,\sigma_0)`$ sample, $`\xi_0 > -1/2`$,
  $`\xi_0 \ne 0`$, there is a measurable maximum likelihood estimator on a compact parameter set with the true
  parameter in its interior, jointly asymptotically normal with the inverse Fisher information as its
  covariance
  ([`exists_gpdMLE_tendstoInDistribution`](ExtremeValueTheory/Statistics/GPDMLENormality.lean)). With a known
  exceedance probability, the plug-in interval for a return level has the asymptotic coverage it claims
  ([`tendsto_measure_mem_gpdReturnLevelInterval`](ExtremeValueTheory/Statistics/ConfidenceIntervals.lean)).

- **Dependent sequences.** Leadbetter's theorem: under $`D(u_n)`$ and $`D'(u_n)`$ with $`nP(X_0>u_n) \to \tau`$,
  $`P(M_n \le u_n) \to e^{-\tau}`$
  ([`tendsto_measureReal_partialMax_le_exp`](ExtremeValueTheory/Dependence/Leadbetter.lean)). The extremal
  index equals the candidate index $`\vartheta`$ read off the spectral tail process when anticlustering and the
  block condition $`A(u_n)`$ hold on a common block sequence
  ([`HasSpectralTailProcess.hasExtremalIndex_abs`](ExtremeValueTheory/Dependence/Anticlustering.lean)).

- **Multivariate extremes.** A vector is regularly varying if and only if its norm is, and the law of its
  direction given a large norm converges
  ([`isRegVarVector_iff`](ExtremeValueTheory/RegularVariation/Multivariate/Polar.lean)). With continuous
  margins, a law is in a multivariate domain of attraction if and only if each margin is and the standardized
  joint tail converges ([`isMDAWith_iff`](ExtremeValueTheory/Multivariate/DomainOfAttractionConverse.lean)). The
  empirical stable tail dependence function is consistent, pointwise and uniformly, in any finite dimension
  ([`tendstoInMeasure_empiricalStableTailDependence`](ExtremeValueTheory/Statistics/StableTailDependence.lean)).

- **Processes.** $`D([0,1],E)`$ with the $`J_1`$ topology is Polish for complete separable $`E`$
  ([`SkorokhodSpace.instPolishSpace`](ExtremeValueTheory/ForMathlib/Topology/Skorokhod/Complete.lean)). The
  uniform tail empirical process converges to Brownian motion in that space
  ([`tendstoInDistribution_tailEmpiricalPath`](ExtremeValueTheory/Statistics/TailEmpiricalProcess.lean)).

## Contents

| Area | Topics |
|---|---|
| Limits of maxima | types, Fisher–Tippett–Gnedenko, max-stability, the GEV family |
| Domains of attraction | Fréchet, Weibull and Gumbel characterizations, von Mises conditions, the quantile form |
| Regular variation | slow, regular, extended and second-order variation; Karamata; Potter bounds; the representation theorem; Breiman's lemma |
| Peaks over threshold | Pickands–Balkema–de Haan, the generalized Pareto law, mean excess |
| Stable laws | the generalized central limit theorem, domains of attraction, uniqueness of the index |
| Heavy tails | subexponential laws, random sums, Pollaczek–Khinchine ruin asymptotics |
| Estimators | order statistics; Hill, Pickands, moment and Weissman, with asymptotic normality; probability-weighted moments and L-moments; blocks, runs and intervals estimators of the extremal index |
| Likelihood and return levels | Wald consistency, GPD and GEV likelihood, Fisher information, joint normality of the GPD and GEV estimators, Wilks' theorem, the delta method, return levels, Wald and profile-likelihood intervals |
| Dependence | Leadbetter's theorem, the extremal index, the tail process, mixing, AR(1), ARMAX, linear processes, Markov chains, `X = AX + B`, GARCH(1,1) tail exponent bounds, the echo processes |
| Multivariate extremes | multivariate regular variation, converse Cramér–Wold, max-stable vectors and their spectral representation, domains of attraction, the multivariate generalized Pareto law, tail dependence and its nonparametric estimation |
| Processes | Poisson random measures, exceedance point processes, the Skorokhod space, the tail empirical process |
| Sharpness of hypotheses | counterexamples showing that hypotheses of Karamata, Breiman, von Mises, the generalized CLT, Hill, Leadbetter and `θ = ϑ` are needed |

## New results

Formalizing the extremal index forced every hypothesis into the open. The results below were found
that way; their novelty has been checked against the literature
([`docs/NOVELTY.md`](docs/NOVELTY.md), [`docs/NOVELTY2.md`](docs/NOVELTY2.md)) but not yet by experts.

- **An answer to a question of Bai, Kulik and Wang (2024).** They asked whether some process
  satisfies the anticlustering condition only for block lengths up to `n^{ρ₀}` with `ρ₀ < 1`. The
  *power-lag echo process* (each large shock reappears once, after a delay that grows with its size)
  does so for every `ρ₀ ∈ (0,1)` (`powEchoProcess_antiClustering_iff`).
- **Mixing does not give `θ = ϑ`.** The same processes are β-mixing, yet their extremal index
  `θ = 1/2` differs from the value `ϑ = 1` read off the tail process
  (`logEchoProcess_betaMixing_incompatible`, `logEchoProcess_theta_lt_vartheta`).
- **The echo process.** A simple stationary sequence with `θ < ϑ`, apparently only the second known
  mechanism after Bai and Wang's (`logEchoProcess_theta_lt_vartheta`), with a phase transition in the
  block length (`logEchoProcess_phase_transition`).
- **A warning for practitioners, proved.** On the echo process, the runs estimator with short runs
  converges to `ϑ`, not to the extremal index `θ` (`logEcho_tendstoInMeasure_runsEstimator`).
- **Which hypotheses are needed.** Counterexamples show that the hypotheses of Karamata's theorem,
  Breiman's lemma, the von Mises condition, the generalized CLT and Hill consistency cannot be dropped;
  some others can be weakened (`ExtremeValueTheory/Minimality/`).
- **Known results, proved under weaker hypotheses:** `θ ≤ ϑ` (Kulik–Soulier Lemma 7.5.4) and an exact
  formula for the gap `ϑ − θ`.

## Limitations

Many results are narrower than their textbook form, and each case is recorded here so that nobody has
to discover it. Rows and scope notes are in [`FAITHFULNESS.md`](FAITHFULNESS.md), and missing results
in [`ROADMAP.md`](ROADMAP.md).

**Nobody independent has reviewed this yet.** The statements, tests and audits were written with AI
assistance, and no human expert has checked them. The kernel guarantees the proofs, not that a
statement matches its textbook. The new results' novelty has not been confirmed by experts either.

**Maximum likelihood and return levels**
- GEV: consistency only on a compact parameter set `K ⊂ {ξ > −1, σ > 0}`, and only for an exact iid GEV
  sample. Fitting finite-block maxima from a law in a domain of attraction, or dependent block maxima, is
  not covered. Joint normality (`tendstoInDistribution_gevMLE`) needs `ξ₀ > −1/2` and `ξ₀ ≠ 0`, and the same exact
  sample. The GEV Wald interval assumes a consistent standard error: no plug-in is proved to be one.
  `tendstoInDistribution_gevReturnLevel` and its Gumbel version are only the delta method applied to an assumed normal
  estimator; `tendstoInDistribution_gevMLEReturnLevel` assumes no normality.
- GPD: also on a compact set, with the true parameter in its interior. Joint normality needs
  `ξ₀ > −1/2` and `ξ₀ ≠ 0`.
- `ξ = 0`: the likelihood is only partly covered. With the shape known to be `0`, the scale estimator is
  normal (`tendstoInDistribution_sampleMean_gpd_zero`). `ξ₀ = 0` is outside every three-parameter GEV result and every
  joint GPD result, even though the Gumbel model is widely fitted.
- Peaks-over-threshold return levels treat the excesses as an exact iid GPD sample with a known exceedance
  probability `ζ`. The number of exceedances is not random, and neither the error of the GPD
  approximation above a finite threshold nor the estimation of `ζ` is accounted for.
- Profile-likelihood intervals and Wilks' theorem are proved for the GPD with `ξ₀ > 0` only, narrower than the regular
  range `ξ₀ > −1/2`, on a compact set, and as confidence sets: that they are intervals is not proved. There is no GEV
  version.
- **The main gap for practice:** these likelihood results describe exact models. What practitioners fit are block
  maxima and threshold excesses that are only approximately GEV or GPD. Likelihood over the whole parameter space
  is also not proved.

**Tail estimators**
- Pickands normality assumes locally uniform second-order regular variation, formally stronger than the pointwise
  textbook condition. Moment estimator normality is proved for `γ > 0` only, in ratio form. Hill intervals are only without bias
  (`λ = 0`) and exclude exact Pareto data, and there are no bias-reduced estimators.
- The basic far-tail Weissman theorems assume the rate and the bias condition; second-order versions
  derive them, for `ρ < 0`, and with extra regularity at `ρ = 0`.
- The blocks and runs estimators (`tendstoInMeasure_blocksEstimator`, `tendstoInMeasure_runsEstimator`)
  assume that the population block or run ratio converges to `θ`. They do not prove that this limit is the
  extremal index, and on the echo process it is not (`logEcho_tendstoInMeasure_runsEstimator`).
- The intervals estimator (`tendstoInMeasure_intervalsEstimator₁`) assumes the two empirical-moment limits.
  Deriving them from a sequence's actual inter-exceedance times (Ferro–Segers Theorem 1) is not proved.
- The non-vacuity tests of the α-mixing Hill theorems and of the intervals estimator use iid data, and those
  of the GEV and Gumbel return levels a synthetic estimator `θ₀ + Z/√n`, which shows only that the hypotheses
  can hold together. Hill does have dependent applications in the library (`tendstoInMeasure_hill_movingMax`,
  `MovingAverage.tendstoInMeasure_hill`).
- These are asymptotic statements. The library says nothing about finite samples or how to choose a
  threshold, a block length or `k`.

**Heavy tails and stable laws**
- The ruin probability `pkRuin` is *defined* by the Pollaczek–Khinchine formula. It is not derived from
  the Cramér–Lundberg process.
- `X = AX + B` and GARCH(1,1): the tail is bounded by `O(x^{−s})` for `s < κ` and shown not to be for
  `s > κ`. Regular variation, the sharp Kesten–Goldie asymptotics `c x^{−κ}` and anything at `s = κ` are not
  proved, and GARCH concerns the squared volatility only, not the returns.
- The parametric stable family `S(α, β, σ, μ)` and the tails of stable laws are not developed.

**Dependence**
- `θ = ϑ` needs anticlustering and the block condition `A(uₙ)` on a common block sequence, and this is
  essential: the echo processes are β-mixing and have `θ < ϑ`.
- The moving-maximum, moving-average and echo theorems assume noise that is nonnegative for every `ω`, not
  almost surely, which is formally stronger than the textbook. The tails of linear processes do not
  (`tendsto_measureReal_tsum_mul_div_of_summable_rpow` allows signed noise and coefficients).
- Infinite moving averages need `Σ|ψ|^δ < ∞` for some `δ < min(α, 1)`, which for `α > 1` is slightly
  stronger than the optimal `Σ|ψ| < ∞`.
- ARMAX needs exact Pareto innovations.

**Multivariate extremes and processes**
- The multivariate GPD limit `IsMDAWith.tendsto_conditionalExcessCDF` needs `G(x ∧ 0) > 0`, which fails
  for unit-Fréchet-standardized limits; use `IsMDAWith.tendsto_conditionalExcess_tailQuantile` for those.
- The multivariate domain-of-attraction equivalence assumes continuous margins.
- The Pickands dependence estimator assumes known unit Fréchet margins. Nonparametric tail-dependence
  estimation is consistency only, with no rates or limit law, uniformly on `(0,T]^d` rather than `[0,T]^d`.
- Point-process convergence is stated through joint laws of counts on finite families of disjoint sets,
  with no topology on the space of measures.
- The functional limit of the tail empirical process is for uniform observations in unweighted `D[0,1]`;
  only weighted near-zero bounds are proved beyond it. Cluster point processes and Brown–Resnick, Schlather
  and extremal-t processes are not formalized.

**Classical theory**
- Explicit norming constants exist only for the standard normal and standard Cauchy laws and for Gamma laws. The unified
  von Mises condition takes the sign of `γ` as a hypothesis.
- Karamata's direct half has versions for measurable `F` and for `F` antitone on `[a, ∞)`, but
  its converse `IsRegularlyVarying.of_tendsto_mul_div_integral_Ioi` assumes `F` antitone on all of `ℝ`.

## Building

With [elan](https://github.com/leanprover/elan) installed:

```sh
git clone https://github.com/unbalancedparentheses/lean-extremevaluetheory.git
cd lean-extremevaluetheory
lake exe cache get   # prebuilt Mathlib
lake build           # the library
lake build Test      # the specification tests and the axiom audit
```

[`lean-toolchain`](lean-toolchain) pins Lean and [`lake-manifest.json`](lake-manifest.json) pins Mathlib, both at
v4.35.0. A weekly job tries newer versions of Mathlib. With Nix, `nix develop` gives a shell with `elan` and the
other tools used by the scripts and CI.

## Using the library in a project

Create a Lean project with the same [`lean-toolchain`](lean-toolchain), and add to its `lakefile.toml`:

```toml
[[require]]
name = "lean-extremevaluetheory"
git = "https://github.com/unbalancedparentheses/lean-extremevaluetheory"
rev = "v0.10.0"
```

Then fetch it and build:

```sh
lake update
lake exe cache get   # prebuilt Mathlib; the library itself compiles from source the first time
lake build
```

and write `import ExtremeValueTheory`. Each tag fixes Lean and Mathlib together.
[`Downstream/Readme.lean`](Downstream/Readme.lean) is such a client, and a weekly
[workflow](.github/workflows/downstream.yml) builds it in a fresh project that requires this repository.

## Verification

A successful `lake build` checks every proof in the library. A proof does not show that a statement says
what the literature says, so the library also tests its statements. `lake build Test` builds the tests and
the axiom audit, and CI runs them on every push.

- **Axioms.** [`Test/AxiomAudit.lean`](Test/AxiomAudit.lean) fails the build if any of the library's 9,487
  declarations depends on an axiom other than the three standard ones, so a `sorry` anywhere in a proof fails CI,
  even if hidden in a macro. [`scripts/check_source.py`](scripts/check_source.py) also rejects `sorry`, new axioms and
  search tactics in the source, and any library file not reachable from the umbrella import.

- **Independent kernel.** A nightly [workflow](.github/workflows/kernel-check.yml) rechecks everything with
  `con-leche`, an independent kernel with a machine-checked proof that it never accepts `False`. It
  accepted all 719,954 declarations of the library and its dependencies on the run of 2026-11-05.

- **Comparator.** [`Challenge.lean`](Challenge.lean) states Fisher–Tippett–Gnedenko, Pickands–Balkema–de Haan, Hill
  consistency and the answer to Bai–Kulik–Wang using only Mathlib, with every definition written out, and says where
  each stops short of the literature. So a sceptic can read that one file instead of trusting this library's
  definitions. [`lake comparator`](comparator.json) checks that [`Solution.lean`](Solution.lean) proves those exact
  statements from the standard axioms. A [workflow](.github/workflows/comparator.yml) runs it, in the sandbox and with
  several kernels, and also checks that a tampered statement is rejected.

- **Non-vacuity tests.** [139 tests](Test/README.md) apply headline theorems to concrete objects, which shows
  that their hypotheses can hold together. They include the echo-process theorems named under New results.

- **Known-answer tests.** [253 tests](Test/README.md) check definitions against textbook values, such as
  Gumbel moments, Smith's Fisher information and extremal indices. These catch sign and parametrization slips.

- **Junk values.** A [scan of 3,718 theorems](Test/JUNK_VALUES.md), by a script outside CI, looked for statements
  true only because `x/0 = 0` or `log 0 = 0`. It found one, now fixed.

- **Mutation checks.** A [script outside CI](Test/MUTATION.md) tried 323 perturbed statements with their
  proofs kept, to catch theorems proved for a trivial reason. None revealed a weakness.

- **Faithfulness audits.** [Eight written audits](FAITHFULNESS.md) compare statements with the literature and record
  each deviation. The last two read new results at headline level, not every supporting lemma. CI
  fails when the library has outgrown the last audit by more than a set margin
  ([`Test/AUDIT_BASELINE`](Test/AUDIT_BASELINE)).

- **Independent statements.** [`docs/HIRATA_COMPARISON.md`](docs/HIRATA_COMPARISON.md) compares our statements with
  Hirata's independent Isabelle ones. By an argument we wrote, not a mechanized one, both main theorems are equivalent.
  The comparison also led to stronger regular variation results here, and to the normal law's domain of attraction.

- **AI review.** Codex, a second AI system, reviewed the headline statements and public claims, and later the GEV, Wilks,
  Pickands and tail-dependence statements. It found no blocking problem in the statements it read, several overstated
  claims, and one definition that was wrong in a junk case, which the audits had missed; all were corrected. This is not
  expert review.

- **Catalogue.** CI fails if a statement in [`catalogue/`](catalogue/), or a definition it reaches, changes without its entry
  being re-checked, and if a `full` entry rests on `rfl` or on unfolding a definition. The statuses are an AI's judgement.

- **Downstream.** A weekly [workflow](.github/workflows/downstream.yml) builds a fresh project that requires this
  repository and imports only `ExtremeValueTheory`.

## Documentation

| If you are… | Read |
|---|---|
| A practitioner using `evd`, `ismev`, `extRemes`, `POT`, `ReIns`, `pyextremes` or `scipy.stats` | [`docs/PRACTITIONERS.md`](docs/PRACTITIONERS.md): which theorem justifies each function, under which assumptions, and the conventions that trip people up (scipy's GEV shape is `c = −ξ`) |
| An extreme value theorist checking the statements | [`docs/REVIEW.md`](docs/REVIEW.md), written for readers who do not use Lean, and [`FAITHFULNESS.md`](FAITHFULNESS.md) |
| A researcher | [`RESEARCH.md`](RESEARCH.md), [`docs/PRACTICAL_OPEN_PROBLEMS.md`](docs/PRACTICAL_OPEN_PROBLEMS.md) and [`docs/OPEN_PROBLEMS_SURVEY2.md`](docs/OPEN_PROBLEMS_SURVEY2.md) |
| New to the library | [`docs/TUTORIAL.md`](docs/TUTORIAL.md), [`docs/FINDING_RESULTS.md`](docs/FINDING_RESULTS.md) and the [applied examples](Examples/Applications) (a 100-year flood, a reinsurance layer, a Hill tail index) |
| A Lean or Mathlib user | The [blueprint](https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/), the [API documentation](https://unbalancedparentheses.github.io/lean-extremevaluetheory/docs/), [`THEOREMS.md`](THEOREMS.md), [`docs/DESIGN.md`](docs/DESIGN.md) and the [`ForMathlib` plan](ExtremeValueTheory/ForMathlib/UPSTREAMING.md) |

[`ROADMAP.md`](ROADMAP.md) says what comes next and [`CHANGELOG.md`](CHANGELOG.md) what has changed. The
[website](https://unbalancedparentheses.github.io/lean-extremevaluetheory/) has an overview.

## Layout

| Directory | Contents |
|---|---|
| top level, `GEV/` | distribution functions, types, Fisher–Tippett–Gnedenko, max-stability, the GEV family |
| `RegularVariation/` | slow, regular, extended and second-order variation; Karamata; Breiman; multivariate |
| `DomainOfAttraction/`, `PeaksOverThreshold/` | the three domains, von Mises conditions, Pickands–Balkema–de Haan |
| `StableLaws/`, `HeavyTails/` | stable laws, the generalized CLT; subexponential laws, random sums, ruin |
| `Statistics/` | order statistics, estimators, likelihood, return levels, confidence intervals, extremal-index estimators |
| `Dependence/` | extremal index, tail process, mixing, Markov chains, linear processes, `X = AX + B`, GARCH, the echo processes |
| `Multivariate/`, `MaxStable/` | multivariate regular variation and domains of attraction, the multivariate GPD, max-stable vectors and processes |
| `PointProcess/` | exceedance point processes |
| `Minimality/` | counterexamples showing which hypotheses are needed |
| `ForMathlib/` | general results written for Mathlib (vague convergence, Poisson random measures, mixing, Skorokhod space, delta method, …); see [`UPSTREAMING.md`](ExtremeValueTheory/ForMathlib/UPSTREAMING.md) |
| `Test/` | specification tests: non-vacuity, known answers, junk values, mutation checks |

## Contributing

The most useful contribution is a correction: if a formal statement does not say what its textbook
counterpart says, please open an issue. No knowledge of Lean is needed for that.
[`CONTRIBUTING.md`](CONTRIBUTING.md) explains how to add a theorem, and
[`docs/ONBOARDING.md`](docs/ONBOARDING.md) walks through a first contribution.

## Citation

```bibtex
@software{carrone2026evt,
  author  = {Carrone, Federico},
  title   = {Extreme Value Theory in Lean},
  year    = {2026},
  doi     = {10.5281/zenodo.23966372},
  url     = {https://github.com/unbalancedparentheses/lean-extremevaluetheory}
}
```

That DOI always resolves to the latest release; [10.5281/zenodo.23966373](https://doi.org/10.5281/zenodo.23966373)
is `v0.9.0`. Both are in the Zenodo record, and [`CITATION.cff`](CITATION.cff) has the same details.

## Acknowledgements

The Fisher–Tippett–Gnedenko development and its blueprint are based on
[ExtremeValueProject](https://github.com/kkytola/ExtremeValueProject) by Kalle Kytölä and the participants of the
Aalto University course MS-EV0029 *Introduction to Formalized Mathematics in Lean*. Several of its statements
were false as written and have been corrected; see [`TRIAGE.md`](TRIAGE.md). Derived files keep their original
copyright headers; see [`NOTICE`](NOTICE).

The library depends on [Mathlib](https://github.com/leanprover-community/mathlib4). Independently, Michikazu
Hirata has formalized
[Fisher–Tippett–Gnedenko and Pickands–Balkema–de Haan](https://isa-afp.org/entries/Extreme_Value_Theory.html)
and [regular variation](https://isa-afp.org/entries/Regular_Variation.html) in Isabelle, in the Archive of Formal
Proofs. This library's structure and its plan for growth also owe much to
[formal-mathfin](https://github.com/formal-applied-math/formal-mathfin).

## License

Apache 2.0. See [`LICENSE`](LICENSE).
