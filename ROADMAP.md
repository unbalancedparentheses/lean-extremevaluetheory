# Roadmap: the textbook layer of extreme value theory

Goal: formalize the core results of the standard references — Embrechts, Klüppelberg and Mikosch,
*Modelling Extremal Events* (EKM); de Haan and Ferreira, *Extreme Value Theory* (dHF); Bingham,
Goldie and Teugels, *Regular Variation* (BGT); Leadbetter, Lindgren and Rootzén (LLR); Resnick,
*Extreme Values, Regular Variation and Point Processes* (1987) and *Heavy-Tail Phenomena* (2007);
Kulik and Soulier, *Heavy-Tailed Time Series* (KS); Beirlant, Goegebeur, Segers and Teugels,
*Statistics of Extremes* (BGST).

`[x]` done, `[~]` partial, `[ ]` missing. See [`THEOREMS.md`](THEOREMS.md) for what is proved.

## 1. Classical theory of maxima and regular variation
- [x] Fisher–Tippett–Gnedenko, max-stability, GEV family and moments
- [x] Domains of attraction (Fréchet, Weibull, Gumbel), von Mises conditions, quantile form
- [x] Regular variation: UCT, representation, Potter, Karamata (both halves), Breiman
- [x] Extended regular variation; second-order regular variation (`ρ ≤ 0`, one-sided bounds)
- [ ] de Haan's Π-variation theory in full (BGT ch. 3, dHF App. B): representation, uniform bounds
- [ ] Two-sided uniform second-order inequalities (dHF Thm 2.3.9 / Drees) for all `ρ ≤ 0`
- [ ] Rates of convergence of maxima (EKM §3.3 / Resnick ch. 2: penultimate approximation)

## 2. Peaks over threshold
- [x] Pickands–Balkema–de Haan (equivalence, every shape)
- [x] GPD / GEV densities, Wald consistency, Fisher information, joint normality (GPD `ξ ≠ 0`)
- [ ] Likelihood at `ξ = 0` (GPD and GEV; continuous extension of score and Hessian)
- [ ] GEV: shape-parameter Fisher information (digamma), joint normality of the 3-parameter MLE
- [ ] Probability-weighted-moment / L-moment estimators (Hosking–Wallis) and their normality
- [ ] Mean excess function: empirical version and consistency (EKM §6.2)

## 3. Statistics of extremes
- [x] Hill: consistency, normality, dependent data; Pickands; moment estimator; Weissman
- [ ] Bias-reduced estimators (second-order: Gomes et al., Feuerverger–Hall), and their normality
- [ ] Asymptotic normality of the Pickands and moment estimators (dHF Thms 3.3.5, 3.5.4)
- [ ] Confidence intervals and the delta method for tail functionals
- [ ] Extremal-index estimators: blocks, runs, intervals (Ferro–Segers), consistency (KS ch. 10)
- [ ] Return levels and return periods for block maxima and POT, with normality

## 4. Heavy tails and stable laws
- [x] Subexponential laws, random sums, ruin, lognormal, `𝒮*`, convolution roots
- [x] Generalized CLT, converse, domain-of-attraction iff, stable index, normal domain
- [ ] The parametric stable family `S(α, β, σ, μ)`: characteristic function, closure properties
- [ ] Tails of stable laws (`P(X > x) ~ C x^{−α}`), series representation (LePage)

## 5. Dependence
- [x] Leadbetter, extremal index, tail process, time change, `θ = ϑ`, mixing, m-dependence
- [x] Linear processes, AR(1), ARMAX, Markov chains, tail chain
- [ ] Point process of clusters (Davis–Hsing 1995): cluster point process convergence
- [ ] Cluster functionals and their limit theory (KS ch. 6, 9)
- [ ] Stochastic recurrence equations: Kesten–Goldie implicit renewal theorem; GARCH(1,1) tails
- [ ] Stochastic volatility models; regularly varying time series beyond linear (KS ch. 14–15)

## 6. Multivariate extremes
- [x] Multivariate regular variation, polar decomposition, converse Cramér–Wold (non-integer `α`)
- [x] Max-stable vectors: spectral representation (existence, uniqueness), Pickands function
- [ ] Multivariate domains of attraction (dHF ch. 6.2: `F ∈ MDA(G)` ⇔ margins + exponent measure)
- [ ] Multivariate POT and the multivariate GPD (Rootzén–Tajvidi)
- [ ] Nonparametric estimation: empirical tail dependence function / stable tail dependence
      function, CFG and Pickands estimators with estimated margins, and their consistency
- [ ] Hidden regular variation and asymptotic independence (Resnick 2002, Ledford–Tawn)

## 7. Point processes and functional limits
- [x] Vague convergence, Poisson random measures, exceedance point processes
- [x] Skorokhod space (Polish), weak convergence in `D`, tail empirical process ⇒ Brownian motion
- [ ] Weighted tail empirical process; tail empirical quantile process (dHF ch. 5)
- [ ] Point-process approach to sums: stable limits via point processes (Resnick 2007 ch. 7)
- [ ] Records and record times as point processes (Resnick ch. 4)

## 8. Max-stable processes
- [x] Spectral construction (de Haan 1984) on finite-dimensional laws
- [ ] Named models: Brown–Resnick, Schlather, extremal-t (finite-dimensional laws, stationarity)
- [ ] Domains of attraction for processes (dHF ch. 9)
