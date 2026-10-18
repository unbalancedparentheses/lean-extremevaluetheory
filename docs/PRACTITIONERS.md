# EVT software and what the Lean library actually proves

A practitioner's guide that maps the estimators in common R and Python extreme value packages to
the theorems formally verified in
[`lean-extremevaluetheory`](https://github.com/unbalancedparentheses/lean-extremevaluetheory).

**How to read this guide.** A formal theorem is a *mathematical guarantee about an idealized
estimator under stated hypotheses*. It is not a certificate for a particular package's code: the
library does not verify numerical optimizers, default tuning, or confidence-interval code. When
this guide says "covered", it means the *formula the package computes* (as documented) agrees
with the formula defined in Lean, and the Lean theorem gives the stated asymptotic property under
the stated hypotheses. Every theorem name below was checked with `#check` against the library at
commit `9a3bfe3`; the faithfulness of each statement to its textbook source is audited in
`FAITHFULNESS.md` (repository root).

Everything in the library is **asymptotic** (`n → ∞`, `k → ∞`, `u → x_F`). Nothing is said about
finite-sample bias, coverage of confidence intervals, or how to choose `k` or the threshold `u`.

---

## 1. Summary table

| Method | R / Python functions (examples) | Lean theorem(s) | Conditions (plain language) | Not covered |
|---|---|---|---|---|
| Hill estimator, consistency | `ReIns::Hill`, `mev::shape.hill`, `QRM::hill`/`hillPlot`, `evir::hill` (plot), `tea` (choice of `k`) | `tendstoInMeasure_hill`; `tendstoInMeasure_hill_of_isInMDAGEV` | iid; `P(X > x)` regularly varying with index `−α`, `α > 0`; `k → ∞`, `k/n → 0` | rates; choice of `k`; `ξ ≤ 0` (Hill is not consistent there) |
| Hill estimator, dependent data | same functions applied to time series | `tendstoInMeasure_hill_of_isMDependent`, `tendstoInMeasure_hill_of_alphaMixing_rate`, `…_of_sumAntiClustering`, `tendstoInMeasure_hill_of_variance` | m-dependent, or stationary α-mixing with a rate and a cluster condition | normality under dependence; the cluster condition is assumed, not derived from a model |
| Hill estimator, asymptotic normality | CIs in `evir::hill`/`QRM::hillPlot` plots; `ReIns::Hill.kopt` (AMSE choice of `k`) | `tendstoInDistribution_hill`; `tendstoInDistribution_hill_pareto` | iid; second-order regular variation of `U` with `(γ>0, ρ≤0, A)`; `√k A(n/k) → λ` | variance estimation, bias-correction (e.g. `ReIns::Hill.2oQV`), choice of `k` |
| Pickands estimator | `mev::shape.pickands`; `POT::fitgpd(est="pickands")` | `tendstoInMeasure_pickands` | iid; `F ∈ MDA(H_ξ)`, any `ξ ∈ ℝ`; `k → ∞`, `k/n → 0` | normality; the POT-package variant that fits a GPD scale too |
| Moment (Dekkers–Einmahl–de Haan) estimator | `ReIns::Moment`, `mev::shape.moment` | `tendstoInMeasure_momentEstimator_of_isInMDAGEV'` | iid; `F ∈ MDA(H_ξ)`, any `ξ`; right endpoint `x_F > 0`; `k → ∞`, `k/n → 0` | normality, generalized Hill (`ReIns::genHill`) |
| Weissman extreme quantile | `ReIns::Weissman.q` (= `Quant`); not `evir::quant`/`QRM::RiskMeasures` (GPD-based) | `tendstoInMeasure_weissman_div` (intermediate), `tendstoInMeasure_weissman_div_of_secondOrder`, `tendstoInDistribution_weissman`, `tendstoInDistribution_weissman_of_rho_eq_zero` | iid; RV tail; intermediate: `k/(np) ∈ [a,b]`; far tail: second order with `ρ < 0` (or `ρ = 0` + regularity), `log(k/(np))/√k → 0` | `ξ ≤ 0`; GPD-based quantiles; choice of `k` |
| Tail-probability estimator (Weissman-type) | `ReIns::Weissman.p` (= `Prob`) | `tendstoInMeasure_tailProbEstimator_div_of_secondOrder`, `tendstoInDistribution_tailProbEstimator(_of_rho_eq_zero)` | same as Weissman | GPD-based exceedance probabilities |
| GPD MLE (peaks over threshold), consistency | `evd::fpot(model="gpd")`, `ismev::gpd.fit`, `extRemes::fevd(type="GP")`, `POT::fitgpd(est="mle")`, `evir::gpd(method="ml")`, `mev::fit.gpd` (default `"Grimshaw"`), `eva::gpdFit(method="mle")`, `QRM::fit.GPD(type="ml")`, `ReIns::GPDmle`, `scipy.stats.genpareto.fit`, `pyextremes` (`"POT"` + `"MLE"`), `thresholdmodeling.gpdfit(..., "mle")` | `ae_tendsto_gpdMLE'` | data **exactly** GPD(`ξ₀`, `σ₀`), iid; parameter search restricted to a compact set with `ξ > −1`, `σ > 0` containing the truth; any (approximate) maximizer | threshold approximation error (data are only approximately GPD above `u`); `ξ ≤ −1`; unbounded parameter space |
| GPD MLE, joint asymptotic normality | standard errors in the same functions (observed/expected information) | `exists_gpdMLE_tendstoInDistribution` (covariance `gpdFisherInfoInv`) | exactly GPD, iid; `ξ₀ > −1/2`, `ξ₀ ≠ 0`; truth in the interior of the compact search set | `ξ₀ = 0` (exponential boundary case); `−1 < ξ₀ ≤ −1/2`; the theorem is about *a* measurable maximizer, not your optimizer's output; profile-likelihood CIs |
| GPD scale MLE with known shape | fixing the shape, e.g. `evd::fpot(..., shape=ξ)`, `mev::fit.gpd(fpar=…)`, `scipy` `genpareto.fit(..., fc=…)` | `ae_tendsto_gpdScaleMLE`, `tendstoInDistribution_gpdScaleMLE'` | exactly GPD; known `ξ`; consistency `ξ > −1, ξ ≠ 0`; normality `ξ > −1/2, ξ ≠ 0`, variance `σ₀²(1+2ξ)` | unknown shape (see joint row) |
| Exponential (`ξ = 0`) fit | `extRemes::fevd(type="Exponential")`, `evd::fpot(..., shape=0)`, `scipy.stats.expon.fit`, `pyextremes` (AIC may pick `expon`) | `tendstoInDistribution_sampleMean_gpd_zero` | exactly exponential(σ), iid; MLE = sample mean | testing `ξ = 0` vs `ξ ≠ 0` |
| GEV MLE (block maxima), consistency | `evd::fgev`, `ismev::gev.fit`, `extRemes::fevd(type="GEV", method="MLE")`, `evir::gev`, `mev::fit.gev`, `eva::gevrFit(method="mle")`, `QRM::fit.GEV`, `scipy.stats.genextreme.fit` (**`c = −ξ`**), `pyextremes` (`"BM"` + `"MLE"`) | `ae_tendsto_gevMLE` | block maxima **exactly** GEV(`ξ₀, μ₀, σ₀`), iid; compact search set with `ξ > −1`, `σ > 0` | asymptotic normality of the 3-parameter MLE; GEV approximation error for finite block size; Gumbel fit |
| GEV MLE, information / normality | standard errors in `fgev`, `gev.fit`, `fevd` | `gevFisherInfoMuSigma`, `tendstoInDistribution_gevScoreVec` | exactly GEV; **known** `ξ`, `−1/2 < ξ`, `ξ ≠ 0` | shape row of the information; normality of the estimator itself (only the score CLT is proved) |
| Return levels (GEV) | `extRemes::return.level`, `ismev::gev.diag`/`gev.prof`, `evd::qgev(1-1/m)`, `eva::gevrRl`, `mev::gev.retlev`, `pyextremes` `get_return_value`, `scipy` `genextreme.isf(1/m, c=-ξ, …)` | `returnLevel`, `gevFun_returnLevel` | `m > 1`; standard GEV; location–scale return level is `μ + σ z_m` | sampling distribution of the estimated return level; delta-method CIs; POT return levels |
| Block maxima empirical CDF | (diagnostic: P–P/Q–Q plots in `gev.diag`, `plot.fevd`) | `tendstoInMeasure_blockMaxEmpCDF` | iid; **known** norming `aₙ, bₙ` with `Fⁿ(aₙx+bₙ) → H(x)`; numbers of blocks and block size → ∞ | estimated norming constants (which is what a GEV fit does) |
| Mean excess / mean residual life | `evd::mrlplot`, `ismev::mrl.plot`, `extRemes::mrlplot`, `POT::mrlplot`, `evir::meplot`, `QRM::MEplot`, `ReIns::MeanExcess`, `pyextremes` `plot_mean_residual_life`, `thresholdmodeling.MRL` | `IsRegularlyVarying.tendsto_meanExcess_div` (population); PBdH `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival` | population: tail RV with `α > 1`, then `e(u)/u → 1/(α−1)` | linearity of the MRL plot for `ξ ≤ 0`; any statement about the *empirical* mean excess function |
| POT justification (Pickands–Balkema–de Haan) | every POT fit | `exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV'`, `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival` | `F ∈ MDA(H_ξ)`, any `ξ ∈ ℝ` | rate of the approximation; threshold choice (`tea`, `eva::gpdSeqTests`, threshold stability plots) |
| Extremal index (θ) | `extRemes::extremalindex` (intervals, runs), `evd::exi` (runs `r≥1`, intervals `r=0`), `POT::fitexi` (intervals), `evir::exindex` (blocks), `mev::ext.index` (wls, mle, intervals), `exdex::spm`, `kgaps`, `dgaps`, `iwls` | `HasSpectralTailProcess.tendsto_blockRatio`, `.hasExtremalIndex_abs`, `.le_candidateExtremalIndex'`, `.hasExtremalIndex_of_isMDependent`, `tendsto_measureReal_partialMax_le_pow` | stationary, regularly varying, forward anticlustering, block condition `𝒜` (from α-mixing) | **no estimator is verified**: no consistency or normality of runs, blocks, intervals, K-gaps or sliding-blocks estimators |
| Declustering | `extRemes::decluster`, `evd::clusters`, `POT::clust`, `evir::decluster`, `pyextremes` (`r` in `get_extremes`), `thresholdmodeling.decluster` | none | — | everything |
| Bivariate extremes / Pickands dependence | nonparametric Pickands-function estimators, e.g. `evd::abvnonpar` (UNVERIFIED: not checked in this review) | `tendsto_pickandsDependenceEstimator` | **known** unit-Fréchet margins; sample from a simple max-stable law | estimated margins; parametric bivariate models |
| L-moments / PWM fits | `extRemes::fevd(method="Lmoments")`, `POT::fitgpd(est="pwmu"/"pwmb")`, `evir::gpd(method="pwm")`, `eva` `method="pwm"`, `mev::fit.gpd(method="pwm")`, `pyextremes` `"Lmoments"`/`"MOM"` | population GEV PWMs only (`integral_mul_gevFun_pow_gevCDF`) | — | consistency or normality of the L-moment / PWM estimators |
| Other GPD/GEV estimators (penalized, MPS, robust, Zhang–Stephens, GMLE) | `POT::fitgpd(est="mple"/"mdpd"/"med"/"lme"/"mgf"/"moments")`, `eva` `method="mps"`, `mev::fit.gpd(method="zs"/"zhang"/"obre")`, `extRemes::fevd(method="GMLE")` | none | — | everything |
| Threshold / `k` selection | `tea` (`dAMSE`, `HW`, `danielsson`, `gomes`, `hall`, `DK`, `GH`, `eye`, `PS`, `RT`, `mindist`, `TH`), `eva::gpdSeqTests`, `mev::thselect.*`, `tcplot`/`threshrange.plot`/`gpd.fitrange`/`plot_parameter_stability` | none (PBdH only says *some* threshold sequence works asymptotically) | — | every selection rule |
| Bayesian fits | `extRemes::fevd(method="Bayesian")`, `pyextremes` `"Emcee"`, `mev::fit.gpd(MCMC=TRUE)` | none | — | everything |

---

## 2. Conventions cheat-sheet

### 2.1 The library's parametrization

| Object | Lean definition | Formula |
|---|---|---|
| Standard GEV CDF | `gevFun ξ x` (`Statistics/ExtremeQuantile.lean`); `gevCDF ξ` (`GEV/Family.lean`) | `H_ξ(x) = exp(−(1+ξx)^(−1/ξ))` on `1+ξx > 0`; `exp(−e^(−x))` for `ξ = 0`; `0` left of the support (`ξ > 0`), `1` right of it (`ξ < 0`) |
| Location–scale GEV | `gevLocScaleCDF ξ μ hσ` | `H_ξ((x − μ)/σ)`, `σ > 0` |
| GPD survival | `gpdSurvival' ξ β x` (`PeaksOverThreshold/Balkema.lean`) | `max(1 + ξx/β, 0)^(−1/ξ)`; `exp(−x/β)` for `ξ = 0` |
| GPD law | `gpdMeasure ξ σ` (`Statistics/GPDLikelihood.lean`) | law of `σ(e^(ξE) − 1)/ξ`, `E ~ Exp(1)`; survival `gpdSurvival' ξ σ` on `x ≥ 0` |
| GPD Fisher information | `gpdFisherInfo ξ σ`, inverse `gpdFisherInfoInv ξ σ` | `I⁻¹ = (1+ξ)·[[1+ξ, −σ], [−σ, 2σ²]]` in the order `(ξ, σ)` |
| GEV return level | `returnLevel ξ m` | `z_m = ((−log(1−1/m))^(−ξ) − 1)/ξ`, `−log(−log(1−1/m))` for `ξ = 0`; for `(μ, σ)`: `μ + σ z_m` |
| Hill | `hill x k` | `k⁻¹ Σ_{i<k} (log X₍ᵢ₊₁₎ − log X₍ₖ₊₁₎)`, `X₍₁₎ ≥ X₍₂₎ ≥ …` (estimates `γ = 1/α`) |
| Pickands | `pickands x k` | uses `X₍ₖ₊₁₎, X₍₂ₖ₊₁₎, X₍₄ₖ₊₁₎` (de Haan–Ferreira indexing; EKM is one off) |
| Weissman | `weissman x k p` | `X₍ₖ₊₁₎ · (k/(np))^γ̂_Hill` |
| Tail probability | `tailProbEstimator x k y` | `(k/n)·(y/X₍ₖ₊₁₎)^(−1/γ̂_Hill)` |
| Tail quantile | `tailQuantile P X p` | `inf{x : P(X > x) ≤ p}` |

So in the library **`ξ > 0` is the heavy (Fréchet) tail, `ξ < 0` a finite endpoint (Weibull
domain), `ξ = 0` Gumbel/exponential**. Note `IsInMDAGEV ξ` maps `ξ > 0` to `MDA(Φ_{1/ξ})` and
`ξ < 0` to `MDA(Ψ_{−1/ξ})`.

### 2.2 Package conventions

| Package (version checked) | GEV CDF as documented | GEV shape | GPD shape | Parameter order in output | Same sign as library? |
|---|---|---|---|---|---|
| R `evd` 2.3-7.1 | `exp[−{1+s(z−a)/b}^(−1/s)]`; Fréchet for `s > 0` | `shape` = `ξ` | `shape` = `ξ`; GPD `loc` = threshold | `fgev`: `loc, scale, shape`; `fpot`: `scale, shape` | yes |
| R `ismev` 1.43 | Coles (2001) eq. 3.2; "positive shape = heavy tail" | `ξ` | `ξ` | `gev.fit$mle = (loc, scale, shape)`; `gpd.fit$mle = (scale, shape)` | yes |
| R `extRemes` 2.2-1 | `exp[−(1+shape(x−location)/scale)^(−1/shape)]` | `shape` = `ξ` | `shape` = `ξ` | `location, scale, shape` | yes (doc typo in the Gumbel formula: sign missing inside `exp`) |
| R `POT` 1.1-12 | — | — | `shape` = `ξ`; threshold = `loc` | `fitted.values = (scale, shape)` | yes |
| R `evir` 1.7-4 | from source: `exp(−(1+xi(q−mu)/sigma)^(−1/xi))` (`pgev` has no `ξ = 0` branch) | `xi` | `xi` | `gev$par.ests = (xi, sigma, mu)`; `gpd$par.ests = (xi, beta)` | yes |
| R `mev` 2.2 | `exp{−[1+ξ(x−μ)/σ]^(−1/ξ)}` | `shape` | `shape` | `fit.gpd`: `(scale, shape)` on excesses | yes |
| R `eva` 0.2.7 | same form (GEVr, `r = 1` = GEV) | `shape` | `shape` | `loc, scale, shape` | yes |
| R `QRM` 0.4-35 | from source: `exp(−(1+xi x)^(−1/xi))` | `xi` | `xi` (no location) | `fit.GEV$par.ests = (xi, mu, sigma)`; `fit.GPD = (xi, beta)` | yes |
| R `ReIns` 1.0.16 | — | — | `gamma` (EVI) | estimates indexed by `k` | yes (`γ = ξ`) |
| Python `scipy.stats.genextreme` | `exp(−(1−cx)^(1/c))` | **`c = −ξ`** | — | `(c, loc, scale)` | **no: flip the sign** |
| Python `scipy.stats.genpareto` | — | — | `c = ξ`; threshold in `loc` | `(c, loc, scale)` | yes |
| Python `pyextremes` 2.5.0 | scipy's | **`c = −ξ`** | `c = ξ` (`floc` = threshold by default) | scipy's | GEV sign flipped |
| Python `thresholdmodeling` 0.0.1 | — | — | calls R `POT::fitgpd` through `rpy2`, so `ξ` | `(shape, scale, …)` | yes (requires R) |

Watch the **parameter order**: `evir::gev` returns `(xi, sigma, mu)`, `QRM::fit.GEV` returns
`(xi, mu, sigma)`, `ismev::gev.fit` returns `(loc, scale, shape)`. The library's MLE theorems use
`(ξ, σ)` for the GPD and `(ξ, μ, σ)` for the GEV.

Other conventions to watch:

- **Gumbel**: library `ξ = 0` is `exp(−e^(−x))`. `scipy.stats.gumbel_r` is the same law
  (`genextreme` with `c = 0`); `gumbel_l` is the law of the *minimum*. Two documentation pages print
  the Gumbel/exponential limit with a missing minus sign (`extRemes` `?fevd`/`?return.level`, and
  `ReIns` `?pgpd` for `γ = 0`); the code is standard.
- **Weibull**: the library's `standardWeibullCDF α x = exp(−(−x)^α)` for `x < 0` is the reversed
  Weibull of maxima (`scipy.stats.weibull_max`), not the ordinary Weibull (`weibull_min`). By our own
  algebra (not in the scipy docs), `genextreme(c) = weibull_max(1/c, loc=1/c, scale=1/c)` for
  `c > 0`, i.e. GEV `ξ = −1/α`, matching the library's `gevCDF` for `ξ < 0`.
- **Hill indexing**: Lean `hill x k` averages over the top `k` and uses `X₍ₖ₊₁₎` as threshold, as in
  de Haan–Ferreira and `ReIns::Hill` (`H = k⁻¹ Σ_{j≤k} log X_{n−j+1,n} − log X_{n−k,n}`). Other
  implementations (`evir::hill`, `QRM::hill`, `mev::shape.hill`) may index by the number of order
  statistics used; check for an off-by-one before comparing numbers.
- **Return levels**: the library's `m` is the number of *blocks*. For POT return levels
  (`extRemes::return.level` on a GP fit, `pyextremes` POT) the return period is in observation
  units scaled by the exceedance rate; the library has no theorem about POT return levels.
- **Optimizers**: `scipy`'s `.fit` uses `optimize.fmin` (Nelder–Mead) by default; `ismev` uses
  `optim` Nelder–Mead; `evd::fgev` and `extRemes::fevd` use BFGS; `mev::fit.gpd` defaults to
  Grimshaw's profile algorithm; `pyextremes` picks the distribution by AIC (it may silently fit
  `gumbel_r` or `expon`, i.e. `ξ = 0`, a case outside the joint-normality theorem). None of this is
  verified: the theorems are about the exact maximizer over a compact set.
- **GEV support**: off the support, `gevLogLik`/`gpdLogLik` use the junk value `log 0 = 0`; the MLE
  theorems use the extended-real versions `gevLogLikE`/`gpdLogLikE` (value `−∞` off the support),
  which match what packages do (return `Inf` negative log-likelihood).

---

## 3. Per-method sections

Notation: `F̄(x) = P(X > x)`; `U(t) = F^←(1 − 1/t)`; `X₍₁₎ ≥ … ≥ X₍ₙ₎` the order statistics;
"iid" means `iIndepFun X P` plus `IdentDistrib (X i) (X 0)` in Lean.

### 3.1 Hill estimator

**Software.** `ReIns::Hill(data, k=TRUE)` returns the Hill estimates `γ̂` for all `k`;
`mev::shape.hill`; `QRM::hill(data, k)` and `QRM::hillPlot`; `evir::hill(data, option="xi")` plots
`ξ̂ = γ̂` (or `option="alpha"` for `α̂ = 1/γ̂`). `ReIns::Hill.kopt` and the `tea` package choose `k`.
Neither `scipy` nor `pyextremes` has a Hill function.

**Guarantees.**

- `tendstoInMeasure_hill` — *iid; `x ↦ P(X₀ > x)` regularly varying with index `−α`, `α > 0`;
  `k → ∞`, `k/n → 0`* ⇒ `hill → 1/α` in probability. No positivity assumption on `X`.
- `tendstoInMeasure_hill_of_isInMDAGEV` — same conclusion phrased as `F ∈ MDA(H_ξ)` with `ξ > 0`.
- `tendstoInMeasure_hill_of_isMDependent` — the same for **m-dependent** identically distributed
  data (no stationarity needed).
- `tendstoInMeasure_hill_of_alphaMixing_rate` — stationary; α-mixing with
  `(n/k)² α(rₙ + 1) → 0`; and a cluster condition: for every threshold sequence with
  `n P(X₀ > uₙ)/k → c > 0`, `Σ_{h=1}^{rₙ} P(X₀ > uₙ, X_h > uₙ) / P(X₀ > uₙ) = o(k)`. The cluster
  condition is a hypothesis; `tendstoInMeasure_hill_of_alphaMixing_of_sumAntiClustering` derives it
  from the Kulik–Soulier condition `S(rₙ, uₙ)`.
- `tendstoInDistribution_hill` — iid; `U` second-order regularly varying with
  `(γ > 0, ρ ≤ 0, A)` (`IsSecondOrderRegularlyVarying`); `k → ∞`, `k/n → 0`,
  `√k A(n/k) → λ` ⇒ `√k(γ̂ − γ) ⇒ N(λ/(1−ρ), γ²)`.
- `tendstoInDistribution_hill_pareto` — exact Pareto tail: normality with no bias.

**Not covered.** Choice of `k` (adaptive or plot-based); bias-reduced Hill
(`ReIns::Hill.2oQV`, `ReIns::EPD`); generalized Hill (`ReIns::genHill`); asymptotic normality for
dependent data; consistency when `ξ ≤ 0` (Hill estimates are meaningless there and the library
says nothing about them).

### 3.2 Pickands estimator

**Software.** `mev::shape.pickands`; `POT::fitgpd(data, threshold, est = "pickands")` (a GPD
fit by the Pickands method; its exact indexing and the accompanying scale estimate were not
compared with the Lean definition).

**Guarantee.** `tendstoInMeasure_pickands` — iid; the CDF `F` of `X₀` is in `MDA(H_ξ)` for some
`ξ ∈ ℝ` (all three domains); `k → ∞`, `k/n → 0` ⇒ `pickands → ξ` in probability.

**Not covered.** Asymptotic normality; the generalized (Segers/Drees) Pickands family; the GPD
scale estimate that accompanies it in `POT`.

### 3.3 Moment estimator (Dekkers–Einmahl–de Haan)

**Software.** `ReIns::Moment(data)` (as a function of `k`), `mev::shape.moment`; the moment
estimate feeds `ReIns::QuantMOM`/`ProbMOM`.

**Guarantee.** `tendstoInMeasure_momentEstimator_of_isInMDAGEV'` — iid; `F ∈ MDA(H_γ)`, any
`γ ∈ ℝ`; `x_F > 0` (some `y > 0` with `F(y) < 1`); `k → ∞`, `k/n → 0` ⇒ moment estimator → `γ`
in probability.

**Not covered.** Normality; moment-based extreme quantile estimators (`ReIns::QuantMOM`); the
mixed-moment and generalized estimators.

### 3.4 Weissman quantile and tail-probability estimators

**Software.** `ReIns::Weissman.q(data, gamma, p)` (alias `Quant`; quantile `x_p` with
`P(X > x_p) = p`, `gamma` = Hill estimates) and `ReIns::Weissman.p(data, gamma, q)` (alias `Prob`;
exceedance probability). `QuantGH`/`QuantMOM` plug in other `γ̂` and are not covered. Note: `evir::quant`,
`evir::riskmeasures`, `QRM::RiskMeasures` and `POT`/`extRemes` quantiles are **GPD-based**
(`u + σ̂/ξ̂ ((n p/N_u)^(−ξ̂) − 1)`), a different estimator not covered by these theorems.

**Guarantees** (iid throughout; Lean uses the Hill estimate for `γ̂`).

- `tendstoInMeasure_weissman_div` — RV tail with index `−α`; `k → ∞`, `k/n → 0`; extrapolation
  factor `dₙ = k/(n pₙ)` eventually in `[a, b]`, `a > 0` (intermediate quantiles) ⇒
  `x̂_p / x_p → 1` in probability. Unconditional (no second order).
- `tendstoInMeasure_weissman_div_of_secondOrder` — far tail: second order with `ρ < 0`,
  `√k A(n/k) → λ`, `dₙ ≥ 1`, `log dₙ / √k → 0` ⇒ ratio consistency.
- `tendstoInDistribution_weissman` — same plus `dₙ → ∞` ⇒
  `(√k / log dₙ)(x̂_p/x_p − 1) ⇒ N(λ/(1−ρ), γ²)`.
- `tendstoInDistribution_weissman_of_rho_eq_zero` — `ρ = 0`, with an extra uniformity hypothesis on
  `A` over `[n/k, 1/pₙ]`; limit is centred `N(0, γ²)` (bias cancels).
- `tendstoInMeasure_tailProbEstimator_div_of_secondOrder`,
  `tendstoInDistribution_tailProbEstimator` (limit `N(λ/((1−ρ)γ²), γ⁻²)`) and
  `…_of_rho_eq_zero` — the analogous results for `p̂(y) / P(X > y)`.
- Further reduction forms (`…_of_bias`, `…_of_isBoundedInProbability`, `…_pareto`) take the
  Hill rate and bias as hypotheses.

**Not covered.** Light or bounded tails (`ξ ≤ 0`); bias-corrected Weissman (`ReIns` with `EPD`);
GPD-based quantiles; choice of `k`. The audit notes the `ρ = 0` statement was not checked line by
line against de Haan–Ferreira.

### 3.5 Peaks over threshold: GPD maximum likelihood

**Software.** `evd::fpot(x, threshold, model="gpd")`, `ismev::gpd.fit(xdat, threshold)`,
`extRemes::fevd(x, threshold=u, type="GP")`, `POT::fitgpd(data, threshold, est="mle")`,
`evir::gpd(data, threshold, method="ml")`, `mev::fit.gpd(xdat, threshold)` (default
`method="Grimshaw"`, an exact-MLE algorithm), `eva::gpdFit(data, threshold, method="mle")`,
`QRM::fit.GPD(data, threshold, type="ml")`, `ReIns::GPDmle(data)` (alias `POT`; excesses over
`X_{n−k,n}` for each `k`), `scipy.stats.genpareto.fit(excesses, floc=0)`,
`pyextremes`: `EVA.get_extremes("POT", threshold=u, r="24h")` then `fit_model("MLE")`,
`thresholdmodeling.gpdfit(sample, threshold, "mle")` (calls R `POT::fitgpd`).
`ismev::pp.fit`, `evd::fpot(model="pp")`, `extRemes::fevd(type="PP")` and `mev::fit.pp` fit the
equivalent point-process likelihood, which the library does not treat.

**Theoretical justification of POT.**
`exists_tendstoUniformlyOn_excessSurvival_of_isInMDAGEV'` and the equivalence
`isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival`: *`F ∈ MDA(H_ξ)` (any `ξ ∈ ℝ`) iff there
is a scale `β(u) > 0` with `sup_{x ≥ 0} |F̄(u + β(u)x)/F̄(u) − Ḡ_{ξ,1}(x)| → 0` as `u ↑ x_F`*.
This is why excesses over a high threshold are modelled as GPD. It gives no rate.

**Guarantees for the MLE** (these assume the data *are* GPD — the well-specified model):

- `ae_tendsto_gpdMLE'` — *iid with law `gpdMeasure ξ₀ σ₀`; a compact parameter set `K` with
  `ξ > −1`, `σ > 0` on `K` and `(ξ₀, σ₀) ∈ K`* ⇒ almost surely, **every** sequence of approximate
  maximizers of the extended-real log-likelihood over `K` (log-likelihood within `n εₙ`, `εₙ → 0`,
  of the value at the truth) converges to `(ξ₀, σ₀)`. This is strong consistency for all shapes
  `ξ₀ > −1`.
- `exists_gpdMLE_tendstoInDistribution` — same model, `(ξ₀, σ₀)` in the **interior** of `K`,
  `ξ₀ > −1/2`, `ξ₀ ≠ 0` ⇒ there is a measurable maximizer `θ̂ₙ` of the likelihood over `K` with
  `√n(θ̂ₙ − θ₀) ⇒ N(0, I(ξ₀,σ₀)⁻¹)`,
  `I⁻¹ = (1+ξ₀)[[1+ξ₀, −σ₀], [−σ₀, 2σ₀²]]` (`gpdFisherInfoInv`). This is the textbook
  covariance used by `ismev::gpd.fit` / `fevd` standard errors (they use the *observed*
  information, which is asymptotically equivalent; that equivalence is not proved).
- `ae_tendsto_gpdScaleMLE` (`ξ > −1`, `ξ ≠ 0`) and `tendstoInDistribution_gpdScaleMLE'`
  (`ξ > −1/2`, `ξ ≠ 0`, variance `σ₀²(1+2ξ)`) — known shape, scale MLE.
- `tendstoInDistribution_sampleMean_gpd_zero` — exponential case (`ξ = 0`): the MLE is the
  sample mean, `√n(σ̂ − σ) ⇒ N(0, σ²)`.

**Not covered.**

- **Threshold bias**: in practice excesses are only *approximately* GPD. The library has no
  theorem for the GPD MLE applied to excesses of a general `F ∈ MDA(H_ξ)` over a random or
  deterministic threshold (the "`k`-largest" POT asymptotics of Drees–Ferreira–de Haan).
- `ξ₀ = 0` for joint normality (the exponential boundary); `−1 < ξ₀ ≤ −1/2` (non-regular case,
  different rates); `ξ₀ ≤ −1` (no MLE).
- The normality theorem asserts the existence of *some* measurable maximizer on a compact set; a
  numerical optimizer's output (local maximum, unconstrained search, different start values) is
  not shown to coincide with it. In regular cases this is what practitioners assume anyway.
- Penalized MLE (`POT` `"mple"`), moment, PWM, L-moment, minimum-density-power-divergence,
  median and Bayesian fits.
- Profile-likelihood confidence intervals (`gpd.prof`, `ci.fevd(method="proflik")`).
- Threshold choice (`tea`, `eva::gpdSeqTests`, `mrlplot`, `tcplot`, `threshrange.plot`).

### 3.6 Block maxima: GEV maximum likelihood

**Software.** `evd::fgev(x)`, `ismev::gev.fit(xdat)`, `extRemes::fevd(x, type="GEV")`,
`evir::gev(data, block)`, `mev::fit.gev(xdat)`, `eva::gevrFit(data)` (r-largest, `r = 1` is GEV),
`QRM::fit.GEV(maxima)`, `scipy.stats.genextreme.fit(maxima)` (**`c = −ξ`**),
`pyextremes`: `EVA.get_extremes("BM", block_size="365.2425D")` then `fit_model("MLE")` (the
default distribution is chosen by AIC between `genextreme` and `gumbel_r`).

**Theoretical justification.** Fisher–Tippett–Gnedenko
(`CumulativeDistributionFunction.IsExtremeValueDistr.classification`) and its unified form
`IsExtremeValueDistr.exists_smul_eq_gevCDF`: every non-degenerate limit of normalized maxima is
of type `H_ξ`. `tendstoInMeasure_blockMaxEmpCDF`: with iid data and *known* norming constants
`aₙ, bₙ` such that `Fⁿ(aₙx + bₙ) → H(x)`, the empirical CDF of normalized block maxima converges in
probability to `H(x)` as the number of blocks and the block length grow. For dependent data,
`tendsto_measureReal_partialMax_le_pow`: under stationarity and extremal index `θ > 0`,
`P(Mₙ ≤ aₙx + bₙ) → H(x)^θ`, which is again GEV of the same type — so fitting a GEV to block
maxima of a stationary series is still justified (with different parameters).

**Guarantees for the MLE** (the block maxima are assumed exactly GEV):

- `ae_tendsto_gevMLE` — iid with law `gevLocScaleCDF ξ₀ μ₀ σ₀`; compact `K` with `ξ > −1`,
  `σ > 0`; every sequence of approximate maximizers over `K` of the extended-real log-likelihood
  converges a.s. to `(ξ₀, μ₀, σ₀)`.
- `gevFisherInfoMuSigma ξ σ` — the `(μ, σ)` block of the Fisher information (Prescott–Walden) for
  known `ξ`, `−1/2 < ξ`, `ξ ≠ 0`; `tendstoInDistribution_gevScoreVec` — the CLT for the
  `(μ, σ)` score with that covariance.

**Not covered.** Asymptotic normality of the 3-parameter GEV MLE (the shape row of the Fisher
information is missing; only the score CLT is proved, not the estimator's normality); the Gumbel
fit (`ξ = 0`, `ismev::gum.fit`, `fevd(type="Gumbel")`); bias from finite block length (the
Bücher–Segers theory for block maxima of non-GEV data); r-largest order statistic models
(`eva::gevrFit` with `r > 1`, `ismev::rlarg.fit`); non-stationary (covariate) GEV models.

### 3.7 Return levels

**Software.** `extRemes::return.level(fit, return.period)` and `ci(fit, type="return.level")`
(delta method, bootstrap, profile likelihood); `ismev::gev.diag` (return-level plot) and
`ismev::gev.prof` (profile likelihood; `ismev` has no separate return-level function);
`eva::gevrRl`; `mev::gev.retlev`; `evd::qgev(1 - 1/m, loc, scale, shape)`; `pyextremes`
`EVA.get_return_value(return_period)` (bootstrap CIs for MLE);
`scipy.stats.genextreme.ppf(1 - 1/m, c=-ξ, loc=μ, scale=σ)`.

**Guarantee.** `gevFun_returnLevel` — for `m > 1`, `H_ξ(returnLevel ξ m) = 1 − 1/m`; the
location–scale return level is `μ + σ z_m` (docstring). This verifies the closed-form formula,
including the `ξ = 0` branch. Combined with `ae_tendsto_gevMLE` and continuity, plug-in return
levels are consistent for exactly-GEV block maxima (this corollary is *not* stated in Lean).

**Not covered.** Confidence intervals (delta method, profile likelihood); POT return levels;
non-stationary return levels.

### 3.8 Mean excess (mean residual life) plots

**Software.** `evd::mrlplot`, `ismev::mrl.plot`, `extRemes::mrlplot`, `POT::mrlplot`,
`evir::meplot`, `QRM::MEplot`, `ReIns::MeanExcess`, `pyextremes.plot_mean_residual_life`,
`thresholdmodeling.MRL`.

**Guarantee.** `IsRegularlyVarying.tendsto_meanExcess_div` — for an antitone survival
function regularly varying with index `−α`, `α > 1`, `e(u)/u → 1/(α − 1)`; i.e. the mean excess is
asymptotically linear with slope `ξ/(1 − ξ)`, `ξ = 1/α < 1`, which is the GPD prediction.

**Not covered.** The empirical mean excess function (no consistency theorem); linearity for
`ξ ≤ 0`; any guidance on reading the plot.

### 3.9 Extremal index and declustering

**Software.** `extRemes::extremalindex(x, threshold, method = c("intervals", "runs"))`,
`extRemes::decluster`; `evd::exi(data, u, r)` (runs estimator, inverse mean cluster size, for
`r ≥ 1`; Ferro–Segers intervals for `r = 0`) and `exiplot`; `POT::fitexi` (Ferro–Segers intervals);
`evir::exindex` (blocks); `mev::ext.index(method = c("wls", "mle", "intervals"))` (Süveges gaps
estimators, Ferro–Segers); `exdex::spm` (Northrop 2015 and Berghaus–Bücher 2018 semiparametric
block-maxima estimators, sliding and disjoint blocks), `exdex::kgaps` (Süveges–Davison K-gaps
MLE), `exdex::dgaps` (Holešovský–Fusek D-gaps), `exdex::iwls` (Süveges 2007).

**What the library proves.** It treats the extremal index as a *population quantity* and
connects it to the tail process; it does **not** analyse any estimator.

- `HasExtremalIndex X P θ` is the Leadbetter definition: `θ ∈ [0,1]` and
  `P(Mₙ ≤ uₙ) → e^(−θτ)` whenever `n P(X₀ > uₙ) → τ`.
- `HasSpectralTailProcess.tendsto_blockRatio` — stationary, spectral tail process `Θ` of index
  `α`, `uₙ → ∞`, `rₙ → ∞`, forward anticlustering at `(uₙ, rₙ)` ⇒ the **cluster ratio**
  `P(max_{t<rₙ} |X_t| > uₙ) / (rₙ P(|X₀| > uₙ)) → ϑ`, the candidate extremal index. This ratio is
  the population target of the **blocks estimator** (and the reciprocal of mean cluster size).
- `HasSpectralTailProcess.hasExtremalIndex_abs` — additionally `rₙ/n → 0` and condition `𝒜(uₙ)`
  (derivable from α-mixing via `conditionA_of_alphaMixing`) ⇒ `|X|` has extremal index `θ = ϑ`.
- `HasSpectralTailProcess.le_candidateExtremalIndex'` — `θ ≤ ϑ` always (no mixing).
- `HasSpectralTailProcess.tendsto_clusterRatio_iff`, `.lt_candidateExtremalIndex_iff` — the exact
  gap `θ = ϑ − η` ("escape mass"), and `logEchoProcess_theta_lt_vartheta`: a stationary process
  whose tail process tends to 0 but `θ = 1/2 < ϑ = 1`. Practical meaning: **a runs- or
  blocks-type estimator can target `ϑ` while the true `θ` is smaller** when anticlustering fails;
  `logEchoProcess_phase_transition` shows the cluster ratio depends on whether the block length
  grows faster than `log n`.
- `hasExtremalIndex_of_isMDependent`, `MovingAverage.hasExtremalIndex`
  (`θ = max ψ_j^α / Σψ_j^α`), `AR1.hasExtremalIndex_of_pos` (`θ = 1 − φ^α`),
  `ARMAX.hasExtremalIndex_candidate` — closed-form `θ` for models you can use to *test* an
  estimator's implementation.
- `tendsto_measureReal_partialMax_le_pow` — `P(Mₙ ≤ aₙx + bₙ) → H(x)^θ` for `θ > 0`.

**Not covered.** Consistency or asymptotic normality of the runs, blocks, intervals (Ferro–Segers),
K-gaps, D-gaps, sliding-blocks or IWLS estimators; declustering algorithms; run-length or
block-length selection.

### 3.10 Other verified results that support common practice

- **Domains of attraction.** Fréchet: `isInMDAFrechet_iff` (tail RV); Weibull: `isInMDAWeibull_iff`;
  Gumbel: `isInMDAGumbel_iff`; von Mises sufficient conditions. Useful for deciding whether a
  parametric family is in the domain you are fitting.
- **Order statistics.** `tendsto_measureReal_orderStat_le`: the Poisson limit for the `k`-th
  largest (`n F̄(uₙ) → τ`), the theory behind r-largest models.
- **Records.** `tendstoInMeasure_recordCount_div_log`: the number of records grows like `log n`
  for iid continuous data — a simple check for trend/non-stationarity.
- **Tail empirical process.** `tendstoInDistribution_tailEmpiricalPath`: the uniform tail empirical
  process converges to Brownian motion in `D[0,1]` (the engine of many tail-estimator CLTs; the
  weighted version for RV `F` is not done).
- **Bivariate.** `tendsto_pickandsDependenceEstimator`: a.s. consistency of the Pickands dependence
  function estimator, **with known unit-Fréchet margins**; extremal coefficient and `λ_U = 2 − θ_E`.
- **Heavy-tail aggregation.** Subexponential results (`P(S_n > x) ~ n P(X > x)`), Breiman's lemma,
  random sums and Embrechts–Veraverbeke ruin asymptotics — not estimators, but the probabilistic
  basis of many risk-aggregation formulas.

---

## 4. Assumptions you should check in practice

1. **Domain of attraction / regular variation.** Every tail-index result assumes
   `F ∈ MDA(H_ξ)`; Hill and Weissman need `ξ > 0` (regularly varying tail). Check a Hill plot is
   stable over a range of `k`; compare Hill with Pickands and moment estimators (the latter two are
   valid for every `ξ`, the moment estimator only if `x_F > 0`).
2. **Intermediate sequence.** The theorems need `k → ∞` and `k/n → 0`. In a finite sample this
   means: use more than a handful of order statistics, but a small fraction of the data.
3. **Second-order behaviour.** Hill normality and far-tail Weissman need a second-order condition
   and `√k A(n/k) → λ`. If `λ ≠ 0` the limit is **biased** by `λ/(1−ρ)`. Standard Hill CIs assume
   `λ = 0`; a too-large `k` violates this. Far-tail Weissman also needs `log(k/(np))/√k → 0`:
   don't extrapolate exponentially far beyond the data.
4. **Independence.** iid is assumed everywhere except the dependent-Hill and extremal-index
   results. For time series, either decluster or use the m-dependent/mixing Hill results, and
   remember the GEV/GPD MLE theorems assume independence.
5. **Well-specification of GPD/GEV MLE.** The MLE theorems assume the data *are* GPD/GEV. For POT
   the excesses are only approximately GPD (justified by PBdH as `u → x_F`) and for block maxima
   only approximately GEV; this approximation bias is outside the verified results. Use threshold
   stability plots and goodness-of-fit diagnostics.
6. **Shape range.** GPD/GEV consistency needs `ξ > −1`; GPD joint normality needs `ξ > −1/2` and is
   proved only for `ξ ≠ 0`. Standard errors reported for `ξ̂` near `−1/2` or with `ξ̂ ≈ 0` are
   outside the verified scope (the `ξ = 0` case is believed regular in the literature, just not
   formalized).
7. **Compact parameter space.** The MLE theorems search over a compact set containing the truth
   (in its interior for normality). Unconstrained optimizers that wander to `σ → 0` or extreme `ξ`
   are outside the theorem.
8. **Stationarity, anticlustering and mixing for `θ`.** `θ = ϑ` needs forward anticlustering and
   condition `𝒜`; without anticlustering `θ < ϑ` is possible. Cluster-size and blocks estimators
   are sensitive to the block length relative to `log n`.
9. **Sign convention.** Before comparing numbers across packages, convert `scipy`/`pyextremes` GEV
   shapes (`ξ = −c`).

---

## 5. Uncertainty and scope notes

- Package function names, arguments and conventions were checked against the current CRAN
  reference manuals and package sources (versions in Section 2.2), the scipy 1.18 docs and source,
  and the PyPI sources of `pyextremes` 2.5.0 and `thresholdmodeling` 0.0.1. Items marked
  UNVERIFIED were not checked. `QRM`'s point-process fitters (`extremalPP`, `fit.POT`, `fit.sePP`,
  `fit.seMPP`) are defunct stubs in 0.4-35.
- The library defines estimators by formulas; packages may differ in indexing (e.g. `k` vs `k+1`),
  tie handling, or numerical details. Such differences are asymptotically irrelevant for the
  theorems above but matter for exact numerical agreement.
- The library's faithfulness audit flags: the Weissman `ρ = 0` results were not checked against
  the textbook line by line; the GEV moment table numbers in EKM were not verified; the theorems
  for `θ ≤ ϑ` cite Kulik–Soulier via a secondary source.

## 6. Documentation links

- R `evd`: https://cran.r-project.org/web/packages/evd/evd.pdf (GEV help: https://rdrr.io/cran/evd/man/gev.html)
- R `ismev`: https://cran.r-project.org/web/packages/ismev/ismev.pdf
- R `extRemes`: https://cran.r-project.org/web/packages/extRemes/extRemes.pdf (`fevd`: https://rdrr.io/cran/extRemes/man/fevd.html)
- R `POT`: https://cran.r-project.org/web/packages/POT/POT.pdf, https://pot.r-forge.r-project.org/
- R `ReIns`: https://cran.r-project.org/web/packages/ReIns/ReIns.pdf, https://github.com/TReynkens/ReIns
- R `evir`: https://cran.r-project.org/web/packages/evir/evir.pdf
- R `tea`: https://cran.r-project.org/web/packages/tea/tea.pdf
- R `eva`: https://cran.r-project.org/web/packages/eva/eva.pdf, https://github.com/brianbader/eva_package
- R `mev`: https://cran.r-project.org/web/packages/mev/mev.pdf, https://lbelzile.github.io/mev/
- R `exdex`: https://cran.r-project.org/web/packages/exdex/exdex.pdf, https://paulnorthrop.github.io/exdex/
- R `QRM`: https://cran.r-project.org/web/packages/QRM/QRM.pdf
- Python `scipy.stats.genextreme`: https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.genextreme.html
- Python `scipy.stats.genpareto`: https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.genpareto.html
- Python `rv_continuous.fit`: https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.rv_continuous.fit.html
- Python `pyextremes`: https://georgebv.github.io/pyextremes/, https://github.com/georgebv/pyextremes
- Python `thresholdmodeling`: https://github.com/iagolemos1/thresholdmodeling, https://pypi.org/project/thresholdmodeling/
- Lean library: `README.md`, `FAITHFULNESS.md` (statement audit), blueprint
  https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/ and API docs
  https://unbalancedparentheses.github.io/lean-extremevaluetheory/docs/
