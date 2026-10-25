# Open problems in EVT reachable by the Lean library: second survey

Literature search of 2026-10-25. It extends `docs/PRACTICAL_OPEN_PROBLEMS.md` and `RESEARCH.md` and does
not repeat their items (Bai–Kulik–Wang, θ vs ϑ, Cissokho–Kulik, Markovich–Rodionov, Carl–Padoan–Rizzelli,
Stein, Drees–Janßen–Resnick–Wang, Bücher–Zhou, Beirlant–Caeiro–Gomes, Bücher–Staud, sequential GoF tests,
Hsing, Engelke–Hitz, Breiman/Denisov–Zwart, θ<ϑ for Markov chains).

I read `README.md`, `THEOREMS.md`, `ROADMAP.md`, `RESEARCH.md` and `docs/PRACTICAL_OPEN_PROBLEMS.md`, and grepped
the Lean sources for the declarations cited below.

**Labels.**
- **OPEN-EXPLICIT**: a source states the problem as open, conjectured or unknown. The quote is given.
- **RESOLVED**: a later paper claims a solution. Such items are verification targets.
- **UNVERIFIED**: open when stated; I could not establish the current status.

**Quotes.** Every quote is from full text I extracted myself (arXiv HTML via `arxiv.org/html` or ar5iv, or the
arXiv PDF). Mathematical symbols are flattened to LaTeX alt-text, so check typography and numbering against the
published versions before citing. "No resolution found" means a citation/web search found nothing, not that
nothing exists.

**Own reasoning** is marked *(my argument, unchecked)*. Treat it as a plan, not a result.

---

## 1. Candidates

### D1. Is the maximum domain of attraction a Borel set of probability measures? What is its Borel class? (OPEN-EXPLICIT)

- **Statement.** Let `𝒫` be the Borel probability measures on `ℝ^k` with the weak topology, and let
  `D ⊂ 𝒫` be the laws in the maximum domain of attraction of *some* (multivariate) extreme value law.
  Is `D` a Borel set? What is its exact place in the Borel hierarchy?
- **Source.** Leonetti & Khorrami Chokami, "The maximum domain of attraction of multivariate extreme value
  distributions is small", Electron. Commun. Probab. 27 (2022), no. 60; arXiv:2203.15761v2, §4 "Closing Remarks",
  https://arxiv.org/abs/2203.15761:
  > "We leave as open question for the interested reader to establish the topological complexity of $\mathsf{D}$ and, in particular, whether it is a Borel set."

  Their main theorem: `D` is dense and of the first Baire category. They also show `D` is neither closed nor open.
- **Still open?** No citing paper addressing it found (searches on the title, "Borel", "Baire category",
  "domain of attraction", 2023–2026).
- **Plan for `k = 1` (my argument, unchecked).** The answer looks like **yes, Borel, of low finite rank**.
  1. `F ∈ D` iff the tail quantile `U = (1/(1−F))^←` is extended regularly varying for some `γ`. Equivalently, the ratio
     `r_t(x) = (U(tx) − U(t)) / (U(2t) − U(t))` has, for each `x > 0`, a finite limit as `t → ∞`, with a
     nonconstant limit function. The limit is then forced to be `(x^γ−1)/(2^γ−1)` (log form at `γ = 0`).
     Library: `isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile`, plus the type and limit
     classification behind `IsExtremeValueDistr.classification`.
  2. `μ ↦ U_μ(q)` is Borel for each fixed `q`: `U(q) ≤ c` iff `F(c) ≥ 1 − 1/q`, and `μ ↦ μ(−∞, c]` is upper
     semicontinuous.
  3. `U` is monotone and left-continuous, so the `limsup`/`liminf` over real `t → ∞` equal those over rational `t`.
     Rational `x` suffice by monotonicity.
  4. So `D` is defined by a countable `∀ε ∃N ∀t,s ≥ N` formula over Borel functions: Borel, roughly `Π⁰₃`/`Π⁰₄`.
- **Sharper target.** Exact Borel class, e.g. `Π⁰₃`-completeness, as for "the sequence converges" sets. Completeness
  would also be a **warning theorem** in the Bahadur–Savage tradition: no countable family of continuous or
  semicontinuous tests can decide MDA membership.
- **Multivariate `k ≥ 2`.** `F ∈ D` iff the margins are in `D` and the standardized law is in the domain of a simple
  max-stable law. That is again a countable-quantifier limit condition, so plausibly Borel, but the
  standardization needs care.
- **Why it matters.**
  - *Theory:* it answers a stated question.
  - *Practice:* it gives a precise sense in which "is my data in an MDA?" is untestable. This complements the
    library's `Minimality/` results.
- **Library has.**
  - Domain-of-attraction characterizations: `isInMDAFrechet_iff`, `isInMDAWeibull_iff`, `isInMDAGumbel_iff`,
    `IsInMDAGEV`, the quantile/ERV equivalence (`DomainOfAttraction/Quantile.lean`), and the uniform convergence theorem.
  - The multivariate domain of attraction (`Multivariate/DomainOfAttraction*.lean`).
  - Mathlib: `ProbabilityMeasure` with its weak topology, the Giry σ-algebra, and the Borel hierarchy is expressible.
- **Missing.**
  - The measurability bridge `μ ↦ U_μ(q)`.
  - The `Tendsto` filter over `ℝ` reduced to `ℚ` for monotone left-continuous functions.
  - The theorem "convergence of a ratio of increments to a nonconstant limit ⇒ ERV".
- **Feasibility.** *Easy–medium* for Borelness at `k = 1`; *medium* for `k ≥ 2`; *hard* for exact Borel-class completeness.
- **Outcome.** A validity theorem answering a published question (Borelness), and possibly a completeness or untestability warning.

### D2. Minimal dependency sets with prescribed extremal coefficients (OPEN-EXPLICIT; the `d = 2` case looks elementary)

- **Statement.** For a max-stable vector or field, the dependency set `𝒦_M` is the compact convex set whose support
  function is the stable tail dependence function. Among all `𝒦_M` with a given extremal coefficient function `θ`,
  the Tawn–Molchanov model `𝒦*_M` is the **largest** (the union of all of them).
  - Is there a **minimal** one?
  - Does a smallest one (the intersection) exist?
- **Source.** Strokorb & Schlather, "Characterizing extremal coefficient functions and extremal correlation
  functions", arXiv:1205.1315 §4. The text is repeated in "An exceptional max-stable process fully parameterized by its
  extremal coefficients", Bernoulli 21 (2015), arXiv:1504.03459. https://arxiv.org/abs/1205.1315:
  > "It is an open problem and it would be interesting to know whether there exist also minimal dependency sets and if they would help to better understand the classification of all dependency structures. A very naive idea would be to take for each $L$ in each of the sets [...] one point and then to take the convex hull with 0 included. However this fails to be a dependency set in dimensions $|M|\geq 3$ , since it is not even a zonoid, which would be necessary"
- **Still open?** No resolution found. Janßen–Neblung–Stoev (arXiv:2212.01044) and the stochastic-ordering paper
  arXiv:2209.02039 (Strokorb a coauthor) do not address it.
- **Bivariate answer (my argument, unchecked).** For `M = {1,2}`, `𝒦₁ ⊂ 𝒦₂` iff `A₁ ≤ A₂` pointwise (Pickands
  functions). Fixing `θ = 2A(1/2) = 2c`:
  - **Minimal elements exist and form a one-parameter family.** For every admissible slope `s`,
    `A_s(t) = max(t, 1−t, c + s(t−1/2))` is convex, satisfies the bounds, and is minimal. If a convex `A ≤ A_s` has
    `A(1/2) = c`, it must equal the line `c + s(t − 1/2)` wherever `A_s` does, by convexity, and
    `A ≥ max(t, 1−t) = A_s` elsewhere.
  - **No smallest element.** Take `c = 0.6`, `A_1 = max(t, 1−t, 0.6)` and `A_3 = max(t, 1−t, 0.5 + 0.2t)`. They are
    incomparable, and the support function of `𝒦₁ ∩ 𝒦₃` is the convex envelope of `min(A_1, A_3)`. That envelope is
    `≤ (0.59 + 0.6)/2 < 0.6` at `t = 1/2`. So the intersection has a strictly smaller extremal coefficient: the
    "minimum" fails already in `d = 2`.
  - **General `|M|`:** existence of inclusion-minimal sets should follow from Zorn plus compactness. Decreasing chains
    of dependency sets correspond to stable tail dependence functions converging pointwise downwards, and spectral
    measures on the simplex with fixed marginal moments form a weakly compact set. The interesting open part is the
    *structure* for `|M| ≥ 3`: e.g. are minimal sets always polytopes, or max-linear (finitely many atoms)?
- **Why it matters.**
  - Sharp *upper* bounds on joint exceedance probabilities given extremal coefficients come from the maximal set.
    Sharp *lower* bounds would come from minimal ones.
  - Practitioners use such bounds for risk under partial dependence information: Yuen–Stoev distributionally robust
    VaR, which uses the Strokorb–Schlather maximal-set bounds.
- **Library has.**
  - `pickandsDependence`, `HasSpectralMeasure.convexOn_pickands`, `max_le_pickands`, `pickandsDependence_le_one`.
  - `exists_isSimpleMaxStable_pickands` (a max-stable law from any spectral measure), `extremalCoefficient`,
    `IsSimpleMaxStable.extremalCoefficient_eq_two_mul_pickands`.
  - `IsSimpleMaxStable.existsUnique_hasSpectralMeasure`.
- **Missing.**
  - The converse "every convex `A` between the bounds is a Pickands function" (or just the explicit discrete spectral
    measures of `A_s`, which are max-linear).
  - The dependency-set and support-function dictionary.
  - Compactness of spectral measures for the general Zorn argument.
- **Feasibility.** *Easy* (bivariate non-existence of a minimum plus explicit minimal family); *medium* (existence of
  minimal sets in any finite dimension); *hard* (structure for `d ≥ 3`).
- **Outcome.**
  - A counterexample: no least dependency set.
  - A validity theorem: minimal sets exist.
  - A practical corollary: sharp lower bounds on `P(max_i X_i ≤ x)` given `θ`, which are attained only by a family,
    not by one model.

### D3. Geometry of the tail-correlation-function polytope `TCF_n`: Questions (F), (G), (H) (OPEN-EXPLICIT)

- **Statement.** `TCF_n` is the set of matrices `(χ_ij)` of tail correlation coefficients that some stochastic process
  realizes. For finite `n` it is a convex polytope (Fiebig–Strokorb–Schlather). Three questions:
  - **(F)** For which `n` is the polytope cut out by the facets at the vertices `v₀ = 0` and `v₁ = 1` contained in
    the positive semidefinite cone?
  - **(G)** Are there non-hypermetric facets at `v₁` for `n ≥ 7`?
  - **(H)** Is the polytope cut out by all hypermetric facets contained in `PSD_n`?
- **Source.** Fiebig, Strokorb & Schlather, "The realization problem for tail correlation functions", Extremes 20
  (2017), arXiv:1405.6876 §8 "Some open questions on the geometry of TCF_n", https://arxiv.org/abs/1405.6876:
  > "(F) For which values of $n$ does $\text{TCF}_{n}(v_{0},v_{1})\subset\text{PSD}_{n}$ hold?"

  > "(G) Are there non-hypermetric facets at $v_{1}$ for $n\geq 7\,$ ? Are there hypermetric facets at $v_{1}$ with $\sum_{i=1}^{n}b_{i}=0$ for $n\geq 7\,$ ?"

  > "(H) Do the inequalities of all hypermetric facets of $\text{TCF}_{n}$ define a polytope, say $\text{TCF}_{n}^{\text{hyp}}$ , already contained in $\text{PSD}_{n}$ ? This holds true for $n\leq 5$ by Proposition 48 , and remains open for $n\geq 6$ ."

  They add: "we expect “if and only if $n\leq 5$ ” to be the answer to Question F". Their Prop. 48 settles (F) for
  `n ≤ 6`, so (F) is open for `n ≥ 7`.
- **Still open?** Probably partly answerable from known results.
  - Janßen, Neblung & Stoev, arXiv:2212.01044 (Extremes 2023), identify tail-dependence matrices with
    `ℓ₁`-embeddable metrics and the cut polytope (Deza–Laurent). They prove that realizability is NP-complete,
    confirming a Shyamalkumar–Tao conjecture.
  - Through this dictionary, (G) and (H) become questions about facets of the cut polytope `CUT_n` at a vertex. For
    `n = 7` all facets of `CUT_7` are known (Deza–Laurent), and non-hypermetric facets exist (clique-web,
    parachute).
  - **So (G) for `n = 7` is likely answerable from the literature.** I have not checked that the affine map takes
    `v₁` to a cut vertex and preserves "hypermetric". I found no paper that states the answer for the TCF questions
    themselves.
- **Why it matters.** It decides which `χ`-matrices a spatial-extremes analyst can fit. This is the TCF analogue of
  "is my correlation matrix PSD?". Practical value is moderate: realizability itself is settled (NP-complete); only
  the facet geometry is open.
- **Library has.** Extremal coefficients and the bivariate `λ_U = 2 − θ_E` (`two_sub_extremalCoefficient_mem_Icc`,
  `hasUpperTailDependence_pickands`), simple max-stable vectors in any finite dimension, and spectral measures. Nothing
  on polytopes.
- **Missing.** The TCF/Bernoulli-compatibility characterization, and polytope machinery: facets, and certificates
  checked by `decide` or `norm_num` over `ℚ`.
- **Feasibility.** *Medium* for a single certificate. Example: exhibit an explicit point of `TCF^hyp_7(v₀,v₁)` outside
  `PSD_7`, or an explicit non-hypermetric facet at `v₁` for `n = 7`. Each is a finite rational computation, which suits
  a proof assistant. *Hard* for general `n`.
- **Outcome.** Explicit counterexamples or certificates.

### D4. Identification of totally skewed 1-stable laws from weighted sums (the `α = 1` gap) (OPEN-EXPLICIT)

- **Statement.** Let `ψ₁,…,ψ_q > 0` satisfy `Σ_j ψ_j^{α+iθ} ≠ 0` for all real `θ`, and let `Z_j` be iid.
  If `Σ ψ_j Z_j` has a totally skewed to the right `α`-stable law, must `Z` be `α`-stable?
  - Known for `α ∈ (0,1) ∪ (1,2)`; a converse construction exists if the Mellin condition fails.
  - **Unknown for `α = 1`.**
- **Source.** Jacobsen, Mikosch, Rosiński & Samorodnitsky, "Inverse problems for regular variation of linear filters, a
  cancellation property for σ-finite measures and identification of stable laws", Ann. Appl. Probab. 19 (2009);
  arXiv:0712.0576, §6 (before Prop. 6.2), https://arxiv.org/abs/0712.0576:
  > "In this context, the following question arises: is it possible to drop the a priori condition of infinite divisibility on Z? The proposition below gives a partial answer. [...] We find the answer in the cases α ∈ (0, 1) ∪ (1, 2). What happens in the case α = 1 is still unclear."

  The same paper also says, of the cancellation property for Lévy measures: "a general characterization of such ρ's remains unknown".
  The follow-up Damek–Mikosch–Rosiński–Samorodnitsky, "General inverse problems for regular variation", J. Appl.
  Probab. 51A (2014), arXiv:1401.5777 §5, says: "Generally, we do not know how to solve inverse problems involving
  non-diagonal matrices."
- **Still open?** No follow-up addressing `α = 1` found.
- **Plan (my reading).** The `α ≠ 1` proofs solve `Σ_j G(ψ_j x) = c x^α` for `G = ±log` of the Laplace transform, by
  cancellation (their Thm 2.1).
  - At `α = 1` the right side becomes `c x log x + d x`. A particular solution `a x log x + b x` exists. The
    difficulty is that the remainder `H` solving `Σ_j H(ψ_j x) = 0` is a *signed* object, so the measure-cancellation
    theorem does not apply directly.
  - Either a sign or growth argument closes it, or a counterexample built from zeros of `s ↦ Σ ψ_j^{1+s}` off the
    imaginary axis might exist.
- **Why it matters.**
  - The general question is the "converse Breiman/linear filter" problem: does tail behaviour of an aggregate force it
    on the components? Risk aggregation and the linear-process analyses in the library rely on the forward direction.
  - `α = 1` is the Cauchy/log-correction case that the library treated separately for the GCLT.
- **Library has.**
  - Stable laws with explicit `α = 1` characteristic exponent: `tendsto_map_convPow_sub_of_isRegularlyVarying_one'`.
  - `domainOfAttraction_isStableIndex_iff`, `IsStable.existsUnique_isStableIndex`.
  - Finite moving-average tails (`HeavyTails/LinearProcess*.lean`), Breiman, and convolution roots for `𝒮`
    (`IsSubexponential.of_convPow`): the equal-weights case.
- **Missing.** Laplace transforms of one-sided stable laws, the JMRS cancellation theorem (Choquet–Deny/Wiener type),
  and Mellin transforms.
- **Feasibility.** *Hard* (genuinely open analysis). A formal **reduction** is *medium*: show that the `α = 1` question
  is equivalent to uniqueness for the functional equation above.
- **Outcome.** A validity theorem or a counterexample.

### D5. Arithmetic Kesten–Goldie: when is the log-periodic factor `q` constant? (OPEN-EXPLICIT, phrased as "would be interesting")

- **Statement.** For `X =ᵈ AX + B` with `log A` arithmetic of span `h`, `E A^κ = 1`, the tail is
  `P(X > x) ~ q(x) x^{−κ}` (up to a slowly varying factor). Here `q(xe^h) = q(x)`, so the tail need **not** be
  regularly varying. Which conditions on `(A,B)` make `q` constant, or continuous?
- **Source.** Kevei, "Implicit renewal theory in the arithmetic case", J. Appl. Probab. 54 (2017); arXiv:1609.07339
  §2.1, https://arxiv.org/abs/1609.07339:
  > "However, for general $(A,B)$ it seems very difficult to determine $q$ . It would be interesting to know what conditions on $(A,B)$ imply that $q$ is constant, or $q$ is continuous, but these questions do not seem to be tractable with our methods."
- **Still open?** No follow-up found. The related Iksanov book problem (*Renewal theory for perturbed random walks*,
  2016, Problem 1.4.2) was solved by Kevei (arXiv:1512.07262: "Theorem 1 is stated as a conjecture/open problem in [23, Problem 1.4.2] by Iksanov").
- **Explicit example (my computation, unchecked).** `A ∈ {0, 2}` with probability `1/2` each, `B ≡ 1`, so `κ = 1`.
  - Then `X = 2^N − 1` with `N` geometric, and `P(X > x) = 2^{−⌊log₂(x+1)⌋}`.
  - So `x·P(X > x)` oscillates in `[1/2, 1)` and never converges: an exact non-RV stationary SRE tail.
  - The Fourier coefficients of `q` are Mellin-type moments `E[(AX+B)^{κ+2πik/h} − (AX)^{κ+2πik/h}]`. So "q
    constant" is equivalent to these vanishing for all `k ≠ 0`. A sufficient condition, or a sharp family of
    examples, is the target.
- **Why it matters.**
  - GARCH/ARCH tail-index estimation assumes Kesten's `c x^{−κ}`. In lattice models (discrete-valued multipliers,
    e.g. branching-type recursions or integer-valued volatility proxies) the Hill estimator and Weissman extrapolation
    are then not consistent in the usual sense.
  - This is a clean **warning**.
- **Library has.**
  - SRE stationary solution and perpetuity (`Dependence/SRE.lean`, `SREPathwise.lean`).
  - Kesten exponent existence and uniqueness (`SRE.exists_integral_abs_rpow_eq_one`, `SRE.kesten_exponent_unique`).
  - Moment and tail-index bounds (`SRE.lintegral_enorm_rpow_stationaryLaw_lt_top`, the `O(x^{-s})` tail bounds in
    `SREMoments.lean`).
  - GARCH (`SREGarch.lean`).
  - Hill consistency `tendstoInMeasure_hill`, which requires RV.
- **Missing.** The implicit renewal theorem (explicitly noted as not formalized in `SREMoments.lean`), and the Mellin
  description of `q`.
- **Feasibility.**
  - *Easy:* the explicit example as a theorem. "There is a stationary SRE with `E A^κ = 1`, `E B^κ < ∞`, whose tail
    is not regularly varying", plus the corollary that it is not in any Fréchet MDA, via `isInMDAFrechet_iff`.
  - *Hard:* the characterization of constant `q`.
- **Outcome.** A warning theorem, and a known-answer test for the SRE module.

### D6. Breiman's 1965 conjecture on randomly weighted self-normalized sums (RESOLVED, Aug–Sep 2026, single unrefereed preprint: a verification target)

- **Statement.** Let `T_n = Σ X_i Y_i / Σ Y_i` with `Y_i ≥ 0` iid and `X_i` iid independent of them. If `T_n` converges in
  distribution to a nondegenerate limit for *some* integrable nonconstant `X`, then `P(Y > y)` is regularly varying
  with index `−β`, `β ∈ [0,1)`.
- **Open status before 2026.** Kevei & Mason, "On the Breiman conjecture", arXiv:1508.01533 (Proc. AMS), §1:
  > "his conjecture can restated to be: for any $X\in\mathcal{X}$ , ( 2 ) is equivalent to ( 3 ). It has proved to be surprisingly challenging to resolve. Mason and Zinn [ 8 ] partially verified Breiman’s conjecture."
- **Claimed resolution.** J. Lenzi, "Breiman's conjecture and normalized jumps of subordinators",
  arXiv:2608.24616v3 (10 Sep 2026), https://arxiv.org/abs/2608.24616. Abstract:
  > "We prove Breiman’s conjecture under the first-moment assumption."

  Theorem 5.1 is the iff. The method uses Poisson–Dirichlet limits, "signed Fourier–Mellin identities", and a
  "ratio–Tauberian argument". A Cauchy-mark example shows integrability cannot be dropped.
- **Why it matters.**
  - It is a 60-year-old conjecture with a new, very recent, single-author proof that is not yet refereed: exactly the
    situation where machine checking adds value.
  - Statistically, `T_n` is a randomly weighted mean (Bayesian bootstrap, importance sampling with heavy-tailed
    weights). The conjecture says nondegenerate limits *force* `RV_{−β}`, `β < 1`, weights.
- **Library has.**
  - Stable domains of attraction and their converse: `domainOfAttraction_isStableIndex_iff`,
    `GCLTConverse.exists_isRegularlyVarying_tailBalance_of_tendsto`.
  - Karamata/Tauberian tools (`RegularVariation/Karamata*.lean`), Poisson random measures (`ForMathlib/`), and
    point processes of exceedances.
- **Missing.** Poisson–Dirichlet `PD(β,0)` laws, the "ratio–Tauberian" theorem, and Fourier–Mellin identities.
- **Feasibility.** *Hard.* The forward (sufficiency) direction, Breiman 1965, is *medium*, and is a natural first
  milestone: `Y ∈ RV_{−β}, β<1 ⇒ T_n ⇒ Σ Q_i X_i`.
- **Outcome.** Verification of a new claimed proof, or discovery of a gap.

### D7. Mixed-type stationary Brown–Resnick processes (OPEN-EXPLICIT 2009–10; current status UNVERIFIED)

- **Statement.** Is there a stationary Brown–Resnick process with nontrivial dissipative **and** conservative parts?
  Equivalently: for a Gaussian process `W` with stationary increments and continuous paths, is
  `P(∫ e^{W_t − σ_t²/2} dt < ∞) ∈ {0,1}`?
- **Source.** Wang & Stoev, "On the structure and representations of max-stable processes", Adv. Appl. Probab. 42
  (2010); arXiv:0903.3594 §7, https://arxiv.org/abs/0903.3594:
  > "The question raised in Kabluchko [ 15 ] on whether there exist stationary Brown–Resnick processes $X$ of mixed type i.e. with non–trivial dissipative and conservative components still remains open. In view of our new necessary and sufficient condition ( 7.3 ), this question is equivalent to the following: Question 7.2 . Is it true for Gaussian processes $W=\{W_{t}\}_{t\in{\mathbb{R}}}$ with stationary increments and continuous paths that $\mu{\{}\int_{-\infty}^{\infty}e^{W_{t}-\sigma^{2}_{t}/2}dt$ [< ∞} ∈ {0,1}]"
- **Still open?** Unclear.
  - Dombry & Kabluchko (arXiv:1601.00792, SPA 2017) characterize the dissipative part by `Y(t) → 0`. Their own §5.4
    open question is about a pathwise characterization of *mixing*, and they answer it negatively there.
  - I found no paper stating the zero-one law.
- **Why it matters.** It decides whether every stationary Brown–Resnick process has a mixed moving maxima (M3)
  representation, which simulation and composite-likelihood software rely on. Practical relevance is low.
- **Library has.** Max-stable processes via Poisson random measures (`IsPoissonRandomMeasure.isSimpleMaxStable_map_process`)
  and the Smith model. No Gaussian path integrals, no ergodic decomposition.
- **Feasibility.** *Out of reach* for now.
- **Outcome.** A structural theorem.

### D8. Embrechts–Goldie conjectures on convolution roots for `𝓛(γ)` and `𝒮(γ)` (RESOLVED, negative: verification targets that complement an existing theorem)

- **Statement.** Embrechts–Goldie (1980, 1982):
  - **Conjecture I:** `𝓛(γ)`, `γ ≥ 0`, is closed under convolution roots.
  - **Conjecture II:** `𝒮(γ)`, `γ > 0`, is closed under convolution roots.

  The `γ = 0` subexponential case is *true* (EGV 1979), and the library proves it (`IsSubexponential.of_convPow`).
- **Resolution.**
  - Shimura & Watanabe (2005) disproved I for every `γ ≥ 0`. Watanabe, arXiv:1511.01246 (Ann. Probab. 47 (2019),
    "The Wiener condition and the conjectures of Embrechts and Goldie"), disproved II:
    > "However, Shimura and Watanabe [ 16 ] disproved Conjecture I for every $\gamma\geq 0$ . On the other hand, Conjecture II was unsolved for over thirty years. In this paper, we disprove Conjecture II for every $\gamma>0$ ."
  - Xu, Foss & Wang (arXiv:1501.07458, Extremes 2015) give counterexamples in `𝓛 ∩ 𝒪𝒮`.
  - Still open variants: "Problem 1.2" of Xu–Wang–Cheng–Yang (arXiv:1609.00912): "Under what conditions, the distribution $V$ or its convolution with self belongs to the class $\mathcal{L}(\gamma)\cap\mathcal{OS}$ , if $V^{*\tau}\in\mathcal{L}(\gamma)\cap\mathcal{OS}$ ?" This is a sufficient-conditions programme, not a sharp question.
- **Why it matters.** The library proves the positive `𝒮` case. Proving that the *long-tailed* class `𝓛` is not closed
  under convolution roots (Shimura–Watanabe) would show that subexponentiality, not long-tailedness, is the right
  hypothesis: a **minimality** result in the style of `Minimality/`.
- **Feasibility.** *Medium* for the `γ = 0`, `𝓛` counterexample (explicit lattice-type construction). *Hard* for
  `𝒮(γ)`, `γ > 0` (Wiener's approximation theorem).
- **Outcome.** A counterexample (minimal-hypothesis warning).

### D9. Minor or narrow items found during the search

- **MathOverflow 473489 (2024): a regularly varying minorant of a nonintegrable decreasing function.** The question:
  is there `h ∈ RV_{−1}`, `h ≤ f`, `∫h = ∞` for every nonincreasing `f` with `∫ f = ∞`?
  https://mathoverflow.net/questions/473489. It has no posted answer, but a comment (by "fedja") gives the
  counterexample: "`f` can crawl at the level `1/T_j` for the time `T_j` for some very fast increasing sequence".
  - **RESOLVED (negative).** By Potter bounds (`potter_bounds_of_measurable`), `h(T) ≥ T^{−1−ε}` eventually, while a
    staircase `f` with `T_{j+1} = T_j²` has `f(T_j) ≈ T_j^{−2}`.
  - A one-file Lean exercise. Low value.
- **Good–Turing / missing mass under regularly varying frequencies.** Ayed, Battiston, Camerlenghi, Favaro,
  arXiv:1806.09712: "An open problem is to extend Proposition 2.2 to the uniform case, when considering the supremum
  of the risk over all $P\in\mathcal{P}_{RV_{\alpha}}$", and they conjecture Good–Turing is rate-optimal minimax.
  Their own Prop. (line "for every sequence $(T_{n})$ ... we can find an element $P\in\mathcal{P}_{PL_{\alpha}}$ such
  that $\limsup$ ... $=+\infty$") suggests uniform rates fail. This is EVT-adjacent (Karlin occupancy), not core.
- **Lo, arXiv:1201.5962 §5.1:** "We conjecture that the couple $(A_{n},T_{n})$ should suffice to characterize the
  whole extremal domain". The conjecture is vaguely stated; skip.
- **Seneta's conjecture on regular variation of generating functions:** RESOLVED by Kevei, arXiv:2007.04668 ("In this
  short note we prove an extension of Seneta’s conjecture").
- **Cramér–Wold for regular variation, nonnegative vectors:** RESOLVED (Boman–Lindskog, arXiv:0802.4373: "this result
  answers affirmatively the conjecture in [ BDM ]"). Already recorded in `RESEARCH.md`.
- **Extremal coefficient functions:** fully characterized (Strokorb–Schlather 2015, "complete alternation"). The
  related question "whether also in the general situation $\Xi_{\text{max}}(T)=\Xi_{\text{lim}}(T)$" (arXiv:1205.1315,
  Remark 24) was answered affirmatively by Fiebig–Strokorb–Schlather 2017 (their Question (D)).
- **Tail measures** (Bladt, Hashorva & Shevchenko, arXiv:2103.04396 §6.3): four open questions on regular variation
  of càdlàg processes, e.g. "it is of some interest to relate (and estimate) the extremal index of periodic processes".
  Too vague to be single problems.

### D10. Does the limit of a track of D-norms have to be idempotent? (OPEN-EXPLICIT; a small explicit counterexample appears to settle it)

- **Statement.** D-norms `‖x‖_D = E max_j |x_j| Z_j` are the exponent functions of simple max-stable laws.
  - Falk multiplies D-norms by multiplying independent generators componentwise. A *track* is the sequence of running
    products of a sequence of D-norms.
  - The track converges, and its limit is idempotent if the same D-norm is repeated.
  - Question: if infinitely many factors differ from `‖·‖_∞`, is the limit idempotent?
- **Source.** Falk, "On idempotent D-norms", J. Multivariate Anal. (2015), arXiv:1303.1284 §3, https://arxiv.org/abs/1303.1284:
  > "But it is an open problem, whether the limit of a track is again idempotent if $\left\|\cdot\right\|_{D^{(i)}}\not=\left\|\cdot\right\|_{\infty}$ for infinitely many $i\in\mathbb{N}$ ."

  Falk's Prop. 3.3: in `d = 2` the only idempotent D-norms are `‖·‖₁` and `‖·‖_∞`.
- **Still open?** No resolution found. Aulbach–Falk–Zott (arXiv:1403.6016) cite the result without settling it. Falk's
  2019 book *Multivariate Extreme Value Theory and D-Norms* was not checked: do this first.
- **Proposed answer: no** (found by the sub-search; I re-checked the logic, but it is unchecked against the book).
  Take `d = 2` and generators `Z^{(i)} = (1 + ε_i U_i, 1 − ε_i U_i)` with `U_i` iid fair signs, `ε_1 = 1/2`,
  `ε_i = 2^{−i}`.
  - No factor is `‖·‖_∞`.
  - The track increases, so the limit `f` has `f(1,1) ≥ 3/2`.
  - Every running product coordinate is `≥ c = ½ ∏_{i≥2}(1 − 2^{−i}) > 0`, so
    `f(1,1) = 2 − E min ≤ 2 − c < 2`.
  - So `f` is neither `‖·‖₁` (value 2) nor `‖·‖_∞` (value 1), hence not idempotent.
  - In Pickands terms, `f(1,1) = θ_E = 2A(1/2)`, the extremal coefficient.
- **Why it matters.** Mainly theory: it settles a stated question in the D-norm calculus behind multivariate GPD and
  max-stable modelling. It also gives a clean example that the iterated "max-stable product" need not converge to
  either extreme dependence case.
- **Library has.** `IsSimpleMaxStable`, `maxStableExponent` (the D-norm, `Multivariate/Dependence.lean`),
  `maxStableExponent_eq_pickands`, `extremalCoefficient`, `one_le_extremalCoefficient`, `extremalCoefficient_le_card`,
  and spectral measures from generators (`exists_isSimpleMaxStable_hasSpectralMeasure`).
- **Missing.** The D-norm product and track definitions, monotonicity of tracks (Falk Lemma 4.1), and the limit being
  a D-norm. All of these are elementary expectations of products of independent variables.
- **Feasibility.** *Easy.* The counterexample needs only the value at `(1,1)` and pathwise bounds.
- **Outcome.** A counterexample answering a published question: the closest analogue of the echo-process success.

### D11. Does d-separation characterize extremal conditional independence in recursive max-linear models? (OPEN-EXPLICIT, 2024)

- **Source.** Engelke, Hentschel et al. (author list not checked), "Graphical models for multivariate extremes" (2024),
  arXiv:2402.02187, https://arxiv.org/abs/2402.02187:
  > "On the other hand, it is still unknown whether $d$ -separation fully characterizes extremal conditional independence or if it is strictly stronger. It is also an open question whether in these models, extremal conditional independence is stronger than, weaker than, equivalent to (or none of the above) *-separation."
- **Related, same family.** Améndola, Hollering, Sullivant & Tran, "Markov equivalence of max-linear Bayesian networks"
  (UAI 2021), arXiv:2106.08305, Problem 6.1:
  > "Determine if conditional independence statements that hold for the max-linear model $X$ correspond to an algebraic or tropical algebraic constraint on the tail dependence matrix $\chi$ ."

  Améndola, Klüppelberg, Lauritzen & Tran (AAP 2022), arXiv:2002.09233, Problem 1: "Find a characterization for all possible source DAGs."
- **Still open?** No resolution found (searches through 2026).
- **Why it is tractable.** The exponent measure of a max-linear model is supported on the finitely many rays given by
  the columns of the coefficient matrix. So Engelke–Ivanovs–Strokorb `Λ`-conditional independence can be computed by
  hand on a 3–4 node DAG. A single DAG on which extremal conditional independence holds without d-separation settles
  the first question ("strictly weaker"). Conversely, a proof for all DAGs settles it positively.
- **Why practitioners care.** Max-linear Bayesian networks are fitted to river networks (Danube) and to financial
  contagion. Which conditional independences the graph encodes decides what a fitted DAG means.
- **Library has.** Spectral measures and exponent functions of simple max-stable vectors in any finite dimension, and
  their uniqueness (`IsSimpleMaxStable.existsUnique_hasSpectralMeasure`). Discrete spectral measures give max-linear
  models.
- **Missing.** The definition of extremal (`Λ`-) conditional independence, d-separation, and max-linear models on
  DAGs. Mathlib has `Digraph` and basic DAG API only.
- **Feasibility.** *Medium* for a counterexample or a small-DAG validity theorem; *hard* in general.
- **Outcome.** Either a counterexample or a theorem; either is publishable.

### D12. Sharp upper bound of Spearman's ρ in terms of Kendall's τ for extreme-value copulas (OPEN-EXPLICIT for the upper half)

- **Statement.** For an extreme-value copula (Pickands function `A`), Schreyer–Paulin–Trutschnig conjectured
  `3τ/(2+τ) ≤ ρ ≤ R_ev(τ)` with `R_ev(τ) = 3τ/(2+τ³) − (1/3)(1−τ)²τ⁴`.
  - The lower bound is proved and sharp: Mroz & Trutschnig, arXiv:1811.02256.
  - The best possible upper bound is open.
- **Sources.**
  - Schreyer, Paulin & Trutschnig, arXiv:1502.04620: "Conjectured inequality for $A\in\mathcal{C}_{ev}$ : $L_{ev}(\tau)\leq\rho\leq R_{ev}(\tau)$ ".
  - Mroz & Trutschnig, arXiv:1811.02256, §4:
    > "We conjecture that in the class of EVCs the upper Hutchinson-Lai is not sharp either. Deriving the best-possible upper inequality will, however, be harder than deriving the sharp lower inequality has been."
  - Related bounds via the tail coefficient were proved by Genest & Sabbagh (C. R. Math. 2021, "These bounds settle a
    question raised in [22]"), a RESOLVED verification target.
- **Why it matters.** `τ` and `ρ` are the two dependence summaries practitioners report for fitted bivariate
  extreme-value copulas (`copula`, `evd`). The exact `(τ, ρ)` region tells which pairs are compatible with an EV copula.
  This is a model-checking diagnostic.
- **Library has.** Bivariate `pickandsDependence`, convexity (`HasSpectralMeasure.convexOn_pickands`), bounds
  (`max_le_pickands`, `pickandsDependence_le_one`), and `λ_U = 2 − θ_E`. `τ` and `ρ` of an EV copula are explicit
  integrals of `A` and `A'`.
- **Missing.** The copula/Kendall/Spearman definitions and the integral formulas in terms of `A`.
- **Feasibility.**
  - *Medium:* the proved lower bound and the Genest–Sabbagh bounds as validity theorems.
  - *Medium:* a counterexample to the conjectured upper curve, i.e. one explicit piecewise-linear `A` with
    `ρ > R_ev(τ)`, if one exists. Search numerically first.
  - *Hard:* the sharp curve.
- **Outcome.** A validity theorem, or a counterexample to the conjectured upper bound.

### D13. Pickands constants: monotonicity of the discrete constants and the 1/Γ(1/α) conjecture (mixed status)

- **Monotonicity (OPEN-EXPLICIT for `α ∉ {1,2}`).** Bisewski & Jasnovidov, "On the speed of convergence of discrete
  Pickands constants to continuous ones" (J. Appl. Probab. 2024), arXiv:2108.00756, https://arxiv.org/abs/2108.00756:
  > "It is therefore natural to speculate that $\delta\mapsto\mathcal{H}_{\alpha}^{\delta}$ is a decreasing function. The explicit formulas for $\mathcal{H}_{1}^{\delta}$ and $\mathcal{H}_{2}^{\delta}$ given in Proposition 2.2 allow us to give the positive answer to this question in these cases."
- **Dieker–Yakir Conjecture 1 (RESOLVED).** The conjecture was that the discretization error has exact order
  `δ^{α/2}`. The same paper says: "We establish that the conjecture is true when $\alpha=1$ and it is not true when $\alpha=2$".
  At `α = 2`, `H₂^δ = (2/δ)(Φ(δ/√2) − 1/2)` gives error `~ δ²/(12√π)`, a Taylor-expansion counterexample.
- **`H_α = 1/Γ(1/α)` (RESOLVED false for small `α`).** Dieker & Yakir (arXiv:1206.5840) call it "A well-known conjecture". Harper (arXiv:1404.5505): "We prove the conjecture is false for small $\alpha$".
- **Why it matters.** Pickands constants enter every Gaussian-process exceedance approximation (scan statistics,
  `P(sup X > u)` for stationary Gaussian fields). Practitioners simulate them on grids, so the sign and size of the
  grid bias (monotonicity in `δ`) is exactly the practical question.
- **Library has.** Nothing on Gaussian processes beyond Mathlib's Gaussian measures and Brownian motion.
- **Feasibility.**
  - *Easy:* the `α = 2` items (closed form, `δ²` rate, monotonicity), from the one-variable process `√2·tN − t²`.
    These are known results, not open.
  - *Out of reach:* the open monotonicity for general `α`.
- **Outcome.** Known-answer formal results and a warning about grid bias. This is a low priority for the open-problem track.

### D14. δ-records: is the martingale property characteristic of the geometric/exponential law? (RESOLVED, negative, 2025)

- **Source.** Gouet, Lafuente, López & Sanz, arXiv:2504.01927:
  > "It was therefore natural to conjecture that this is a characteristic property of the geometric distribution among discrete models and, possibly, of the exponential distribution among continuous models."

  The same paper refutes it with explicit lattice solutions (mixtures of geometric and negative-binomial laws), and
  shows the geometric solution exists iff "$c\delta\leq\left(\frac{\delta}{\delta+1}\right)^{\delta+1}$".
- **Feasibility.** *Easy–medium.* It is a series identity plus a one-step conditional expectation. The library has
  records (`Statistics/Records.lean`).
- **Outcome.** Verification of a fresh counterexample. The practical value is low.

### D15. Foss–Korshunov Conjecture 1: characterizing `𝒮(γ)` by `F*F ~ cF` (OPEN-EXPLICIT 2007; no resolution found)

- **Source.** Foss & Korshunov, "Lower limits and equivalences for convolution tails", Ann. Probab. 35 (2007),
  arXiv:math/0510273, https://arxiv.org/abs/math/0510273:
  > "Conjecture 1. The distribution F on [0, ∞) with unbounded support belongs to the class S(γ) if and only if: (a) γ = ˆγ; (b) for some c ∈ [2, ∞), F ∗ F (x) ∼ cF (x) as x → ∞. For γ > 0 we have neither a proof of the conjecture nor a counterexample."

  Their Thm 7 proves it under an extra condition (c).
- **Why it matters.** It would give a one-line test for convolution-equivalence (light-tailed analogue of subexponentiality), used in ruin
  asymptotics with exponential moments.
- **Library has.** `IsSubexponential`, convolution powers, convolution roots (`HeavyTails/ConvolutionRoots.lean`). It
  has no `𝒮(γ)`.
- **Feasibility.** *Hard* (a counterexample would be a delicate lattice tail).
- **Outcome.** A counterexample or a validity theorem.

### D16. Errata in standard texts (formal warnings)

- **de Haan & Ferreira (2006), official errata** (https://personal.eur.nl/ldehaan/EVTbook.correction.pdf):
  - p. 213, Remark 6.1.8: "Relation (6.1.15*) does not necessarily hold for Borel sets A not of the form (6.1.16)". So
    `P(Y ∈ A) = exp(−ν(A))` is valid only for complements of lower orthants. The library's max-stable/exponent-measure
    API should state exactly this. An *easy* formal counterexample also guards against a common misuse.
  - p. 265: "does not imply asymptotic independence" should read "does not imply asymptotic dependence".
  - Examples 9.4.6 and 9.8.2 (Brown–Resnick): a two-sided Brownian motion is required.
- **Charras-Garrido & Lezaud (2013), corrected 2017** (https://www.numdam.org/item/JSFS_2017__158_3_27_0.pdf): "Two
  mistakes appears in Proposition 2.9, one is due to a typographical error in Beirlant et al. (2004)." The Gumbel von
  Mises condition must read `(1/r)' → 0`. Check that `isInMDAGumbel_of_vonMises` uses the correct form (it should;
  `THEOREMS.md` describes the auxiliary-function form).

### D17. Unverified

- **Lebedev (Moscow Univ. Math. Bull. 2022): can an exact extremal index exceed 1 in series schemes?** The abstract,
  seen only in search snippets, says "The question whether the exact extremal index greater than one can exist remains
  open". The full text could not be retrieved, so this does not meet the verbatim rule. It would fit the library's
  extremal-index API if confirmed.
- **Kabluchko & Stoev, arXiv:1207.4983, Remark 4.6:** "we conjecture that the Poisson line process X for k ≥ 1 is
  generated by a null-recurrent flow". Status unverified; out of reach.

---

## 2. Ranking: top 5

Criterion: (value of the outcome) × (how explicitly open the problem is) × (feasibility with what the library already has).

| Rank | Candidate | Why | Feasibility | Outcome type |
|---|---|---|---|---|
| 1 | **D10** Falk: is the limit of a D-norm track idempotent? | Stated verbatim as "an open problem". A three-line bivariate construction appears to answer "no", using only `θ_E = ‖(1,1)‖_D` bounds. It is the same pattern as the echo-process answer to Bai–Kulik–Wang | easy (check Falk's 2019 book first) | counterexample |
| 2 | **D1** Is the max-domain of attraction `D` a Borel set? (Leonetti–Khorrami Chokami 2022) | An explicit question. The library's quantile/ERV characterization reduces `k = 1` to a countable-quantifier formula, and Mathlib has the descriptive-set-theory vocabulary. The exact Borel class gives an "MDA membership is untestable" warning | easy–medium (`k=1`), medium (`k≥2`), hard (completeness) | validity theorem plus warning |
| 3 | **D2** Minimal dependency sets with given extremal coefficients (Strokorb–Schlather) | Explicitly open. In `d = 2` an elementary argument gives a one-parameter family of minimal sets and no minimum (numerically checked: the intersection's coefficient is 0.591 < 0.6). Zorn plus compactness should give existence in any dimension. Practical payoff: sharp lower bounds for joint exceedances given `θ` | easy (`d=2`), medium (general existence) | counterexample plus validity theorem |
| 4 | **D11** d-separation vs extremal conditional independence in max-linear models (Engelke et al. 2024; Améndola et al.) | Recent and explicitly open. Exponent measures of max-linear models are finite sums of atoms, so 3–4 node DAGs are hand-checkable. Graphical extremes are used in hydrology and finance | medium | counterexample or theorem |
| 5 | **D12** Sharp upper `ρ`–`τ` bound for extreme-value copulas (Schreyer–Paulin–Trutschnig; Mroz–Trutschnig) | The upper half is explicitly open. Everything is a one-dimensional integral of the Pickands function, which the library has. A numerically found piecewise-linear `A` beating `R_ev` would be a formal counterexample, and the proved lower bound is a ready validity theorem | medium | validity theorem or counterexample |

**Runners-up.**
- **D5** (arithmetic Kesten–Goldie). Its *example* is easy and gives a good SRE/GARCH warning: a stationary SRE with
  `E A^κ = 1` whose tail is not regularly varying. Kevei's open question about when `q` is constant is hard. Note that
  the `A ∈ {0,2}` example has `P(A=0) > 0`, which the library's `E log|A| < 0` hypothesis (with `log 0 = 0`) does not
  cover. Handle that case directly, or use a lattice `A ∈ {2, 1/2}`.
- **D6** (Breiman's conjecture). A brand-new single-author proof (arXiv:2608.24616, Sep 2026). High verification
  value, but hard.
- **D3** (TCF polytope (G) at `n = 7`): a finite certificate, probably derivable from the cut-polytope literature.

---

## 3. Sources consulted (URLs)

- Leonetti, Khorrami Chokami, https://arxiv.org/abs/2203.15761
- Strokorb, Schlather, https://arxiv.org/abs/1205.1315 , https://arxiv.org/abs/1504.03459
- Fiebig, Strokorb, Schlather, https://arxiv.org/abs/1405.6876
- Janßen, Neblung, Stoev, https://arxiv.org/abs/2212.01044
- Corradini, Strokorb (stochastic ordering), https://arxiv.org/abs/2209.02039
- Jacobsen, Mikosch, Rosiński, Samorodnitsky, https://arxiv.org/abs/0712.0576
- Damek, Mikosch, Rosiński, Samorodnitsky, https://arxiv.org/abs/1401.5777
- Kevei (arithmetic implicit renewal), https://arxiv.org/abs/1609.07339 ; Kevei (KGG note), https://arxiv.org/abs/1512.07262
- Kevei, Mason (Breiman conjecture), https://arxiv.org/abs/1508.01533 ; Lenzi, https://arxiv.org/abs/2608.24616
- Wang, Stoev, https://arxiv.org/abs/0903.3594 ; Dombry, Kabluchko, https://arxiv.org/abs/1601.00792
- Watanabe, https://arxiv.org/abs/1511.01246 ; Xu, Foss, Wang, https://arxiv.org/abs/1501.07458 ; https://arxiv.org/abs/1609.00912
- Foss, Korshunov, https://arxiv.org/abs/math/0510273
- Falk, https://arxiv.org/abs/1303.1284 ; Aulbach, Falk, Zott, https://arxiv.org/abs/1403.6016
- Engelke et al., https://arxiv.org/abs/2402.02187 ; Améndola et al., https://arxiv.org/abs/2106.08305 , https://arxiv.org/abs/2002.09233
- Schreyer, Paulin, Trutschnig, https://arxiv.org/abs/1502.04620 ; Mroz, Trutschnig, https://arxiv.org/abs/1811.02256
- Dieker, Yakir, https://arxiv.org/abs/1206.5840 ; Harper, https://arxiv.org/abs/1404.5505 ; Bisewski, Jasnovidov, https://arxiv.org/abs/2108.00756
- Gouet, Lafuente, López, Sanz, https://arxiv.org/abs/2504.01927
- Ayed et al. (missing mass), https://arxiv.org/abs/1806.09712 ; Lo, https://arxiv.org/abs/1201.5962 ; Kevei (Seneta), https://arxiv.org/abs/2007.04668
- Boman, Lindskog, https://arxiv.org/abs/0802.4373 ; Bladt, Hashorva, Shevchenko, https://arxiv.org/abs/2103.04396
- MathOverflow 473489, https://mathoverflow.net/questions/473489
- de Haan–Ferreira errata, https://personal.eur.nl/ldehaan/EVTbook.correction.pdf ; Charras-Garrido–Lezaud correction, https://www.numdam.org/item/JSFS_2017__158_3_27_0.pdf
- Searched with no explicit open problems found: Foss–Korshunov–Zachary (1st ed., exercises only), Jessen–Mikosch survey,
  Hult–Samorodnitsky (math/0702112), Denisov–Foss–Korshunov (0808.3697), Planinić–Soulier (1706.04767), the Berman-condition
  literature, multivariate GPD papers, and Lindskog–Resnick–Roy.
