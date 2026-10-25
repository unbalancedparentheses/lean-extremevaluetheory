# Novelty check: the P1 results (θ vs ϑ, late-return mass, echo process, block-length transition, mixture)

Date: 2026-10-18. Scope: the files `Dependence/{ThetaLeVartheta,ThetaGap,EchoProcess,EchoPhaseTransition,EchoConditionA,MixtureProcess}.lean` (none of them contains `sorry`) and RESEARCH.md, "Progress on P1".

Sources read in full text: Bai–Kulik–Wang (BKW) arXiv:2409.17966; Bai–Wang (BW) arXiv:2110.07499; Planinić–Soulier arXiv:1706.04767; Segers (2006, JAP); Abadi–Freitas–Freitas arXiv:1808.02970; Kevei–Kubatovics arXiv:2510.02004.

Not accessible (paywalled or 403): the Kulik–Soulier (2020) book itself; Smith (1988); Weissman–Cohen (1995). Statements about these are marked **[unverified]**.

---

## Summary table

| # | Result | Verdict | Closest prior work |
|---|---|---|---|
| 1 | θ ≤ ϑ under stationarity, spectral tail process and existence of θ only | **Known** in substance (KS20 Lemma 7.5.4, cited as "always holds"). The value we add is a formally checked proof with explicit, minimal hypotheses | KS20 Lemma 7.5.4; Segers 2006 Lemma 4.1; O'Brien 1987 |
| 2 | Gap formula: cluster ratio → L ⇔ η = ϑ − L; under 𝒜, θ = ϑ − η | **Partially known.** It is a clean repackaging of a classical blocks/runs identity combined with the tail process. The exact two-sided "θ = ϑ − η" statement and the name "late-return mass" were not found in the literature | Segers 2006 (p_m = Σ p θ^R_i); O'Brien 1987; Leadbetter 1983; Planinić–Soulier 2018 Lemma 4.1; BKW 2024/26 |
| 3 | Echo process: Θ_t = 1{t=0} (ϑ = 1) but θ = 1/2 | **Likely new** as an explicit construction. No prior example found with extremal independence at every fixed lag together with θ < 1 and an existing θ | BW 2023 and BKW 2026 (the only published θ < ϑ examples, per BW); Weissman–Cohen 1995 (random translations, lags independent of size) |
| 4 | Block-length phase transition at scale log n with a closed form and a kink at c = 1/α; 𝒜 holds iff blocks are long | **Likely new** as a result. The phenomenon type is known from BKW (polynomial "mesoscopic" scale) and BW (AC for r_n = o(log b_n)). It answers the first open question of BKW §1.4 in a different form | BKW Thm 1.5 and Cor 1.6; BW §1, (1.16)–(1.17) |
| 5 | Mixture (constant w.p. p, iid otherwise): η = 0, no θ | **Known / folklore** (non-ergodic mixtures have no extremal index). The only new part is the remark "η = 0 does not imply that θ exists" | Leadbetter 1983; LLR 1983; Weissman–Cohen 1995 [unverified] |

---

## 1. θ ≤ ϑ without anticlustering or mixing

**Literature.**
- BKW, arXiv:2409.17966 v2, p. 2: "they do not necessarily agree, although the relation θ ≤ ϑ always holds [12, Lemma 7.5.4]". Here [12] is Kulik & Soulier, *Heavy-Tailed Time Series*, Springer 2020.
  - Published as Ann. Appl. Probab. 36(4) (2026) 3132–3168, doi:10.1214/26-AAP2298, per Crossref.
  - Links: https://arxiv.org/abs/2409.17966 and https://doi.org/10.1214/26-AAP2298
- BW, arXiv:2110.07499 (Bernoulli 29(4) (2023) 3255–3279, doi:10.3150/22-BEJ1582):
  - Remark 1.3: their right-tail ϑ is "the right-tail candidate extremal index in [KS, Eq. (7.5.4b)]".
  - After Remark 1.5: "D_{β,p} ∈ (0,1), which implies θ < ϑ, is consistent with Kulik and Soulier [16, Lemma 7.5.4]".
  - So KS §7.5 treats both the |X| version and the right-tail (ℝ₊) version.
- **Exact hypotheses of KS Lemma 7.5.4: [unverified].** The book text was not accessible. Both citing papers use it unconditionally ("always holds"). That suggests the lemma assumes only a stationary regularly varying series and the existence of θ, but this could not be confirmed. The lemma may also rely on the tail process tending to 0, for instance through Planinić–Soulier Lemma 4.1 (below). That would be a stronger hypothesis than ours, because our proof does not need Y_t → 0.
- The proof ingredients are classical:
  - **First-exceedance decomposition** P(M_n > u) = Σ_{k<n} P(X_0 > u, M_{1,k} ≤ u). This is Segers, "Rare events, temporal dependence, and the extremal index", J. Appl. Probab. 43(2) (2006) 463–485, doi:10.1239/jap/1152413735, §4.2: "p_m = Σ_{i=1}^m p θ^R_i", and Lemma 4.1: θ^R_m ≤ θ^B_m ≤ θ^M_m ≤ θ^B_m/q_m. The decomposition goes back to O'Brien, Ann. Probab. 15 (1987) 281–291.
  - **Monotonicity of θ^R_i in i**, which gives θ^B_n ≤ m/n + θ^R_m.
- **Planinić–Soulier**, "The tail process revisited", Extremes 21 (2018) 551–579, arXiv:1706.04767, Lemma 4.1. If Y_t → 0 a.s., then for every c_n → ∞ there exists r_n with P(X*_{1,r_n} > c_n u)/(r_n P(|X_0| > c_n)) → ϑ u^{−α}. This holds without anticlustering. Combined with subadditivity of block maxima it gives θ ≤ ϑ at once, but it needs Y_t → 0.

**How our result relates.** Our statement is `HasSpectralTailProcess.le_candidateExtremalIndex'`. Its hypotheses are α > 0, measurability, stationarity, the spectral tail process, and HasExtremalIndex for |X|. It does not assume A(u_n), block lengths, anticlustering, or Y → 0.
- It is at least as general as anything that can be read off the citations, and possibly slightly more general than KS if KS assume Y → 0 [unverified].
- Mathematically it is a one-paragraph argument. **Verdict: known.** It is worth stating in a paper only as a lemma with its minimal hypotheses, noting that it is machine-checked.
- One detail to state: the level sequences u_n(τ) are obtained for every τ from regular variation alone (LLR Thm 1.7.13). The formalization handles this point.

---

## 2. Gap formula and late-return mass

**What we prove** (`ThetaGap.lean`):
- **Exact identity (stationarity only):** 0 ≤ CR_n − (q_n(m) − ε_n(m)) ≤ m/r_n. Here:
  - CR_n is the cluster ratio P(M_{r_n} > u_n)/(r_n P(|X_0| > u_n));
  - q_n(m) = P(M_{1,m} ≤ u_n | |X_0| > u_n);
  - ε_n(m) = E[(1 − T_n/r_n)^+ ; T_n > m | |X_0| > u_n], with T_n the first return time.
- **Gap formula:** CR_n → L ⇔ the late-return mass η = lim_m lim_n ε_n(m) exists and η = ϑ − L.
- **Under 𝒜:** θ = ϑ − η, so θ < ϑ ⇔ η > 0. The late-return mass is independent of (u_n, r_n) whenever 𝒜 holds and θ exists.

**Prior work.**
- **The averaging identity is classical.** CR_n = (1/r_n) Σ_{k<r_n} q_n(k): blocks index = average of runs indices. This is Segers 2006 (above, §4.2 and Lemma 4.1); Weissman & Novak, "On blocks and runs estimators of the extremal index", J. Stat. Plann. Inference 66 (1998) 281–288; and Smith & Weissman, JRSS B 56 (1994) 515–528.
- **O'Brien (1987)** (https://doi.org/10.1214/aop/1176992270): θ = lim P(M_{1,r_n} ≤ u_n | X_0 > u_n) under a mixing condition. Leadbetter, Z. Wahrsch. 65 (1983) 291–306: θ = lim CR_n under D(u_n). These give the "θ = lim CR_n under 𝒜" half.
- **Chernick, Hsing & McCormick**, Adv. Appl. Probab. 23 (1991) 835–850, the D^(k)(u_n) conditions: θ = lim P(M_{2,k} ≤ u_n | X_1 > u_n) for a fixed k. In tail-process terms, D^(k) is exactly what rules out escape. Our η is the defect of the D^(k) formula as k → ∞.
- **Basrak & Segers**, SPA 119 (2009) 1055–1080, and **KS20 ch. 6–7**, e.g. Cor. 6.2.6 as cited by BKW: anticlustering ⇒ CR_n → ϑ. This is our `ForwardAntiClusteringAt.hasLateReturnMass_zero`.
- **BKW abstract:** the θ/ϑ gap "is a reflection of [a] phase transition … prohibited by the anticlustering condition". This is the same idea stated qualitatively; BKW give no general identity.
- **Terminology clash:** "escape of mass" is already used by Abadi, Freitas & Freitas, "Dynamical counterexamples regarding the extremal index and the mean of the limiting cluster size distribution", arXiv:1808.02970 (journal version not checked), §4. There it means loss of point-process mass, i.e. mean cluster size ≠ 1/θ (Smith 1988 type). That is a related but different phenomenon. Cite it and distinguish, or rename ours (for example "escaping cluster mass" or "late-return mass").
- No source was found that states the two-sided equivalence CR_n → L ⇔ η = ϑ − L, or θ = ϑ − η, as a theorem.

**Assessment: partially known.** Given the averaging identity and q_n(m) → ϑ_m (from the tail process), the equivalence is close to a reformulation: η is defined so that the equation balances. Its value is conceptual.
- It turns "θ < ϑ" into a checkable, quantitative criterion.
- It shows η is canonical, meaning independent of (u_n, r_n), under 𝒜.
- It isolates exactly what anticlustering is used for.

Present it as a proposition, not the headline. Referees in this area (Kulik, Soulier, Segers, Wang) will recognise the identity immediately.

---

## 3. The echo process

**Our claim (formally proved).** Take iid Pareto(α) shocks Z_t and X_t = max(Z_t, max{Z_s : s < t, s + L(Z_s) = t}). Assume L ≥ 1, L(z) → ∞ and E L(Z) < ∞. Then:
- the process is stationary;
- P(X_0 > x) ~ 2x^{−α};
- Θ_t = 1{t = 0}, so ϑ = 1;
- θ = 1/2 and η = 1/2.

The concrete lag is L(z) = ⌊log z⌋ + 1.

**Searches run** (several formulations): "extremal index" with tail-process counterexample; "Θ_t = 0 / asymptotic independence at all lags yet θ < 1"; random-lag, random-delay or random-translation moving maxima; long-memory stochastic volatility; Mikosch–Wintenberger; Davis–Hsing 1995; Leadbetter's examples; dynamical-systems extremal index. I also checked papers citing BKW and BW (Semantic Scholar): Bai–Düker arXiv:2510.10578, Kevei–Kubatovics arXiv:2510.02004, and "Multiple extremal integrals" arXiv:2503.23142. None contains a similar construction.

**Closest relatives found.**
1. **BW 2023 and BKW 2026**, the stable-regenerative multiple-stable model.
   - BW write: "we are not aware of any other examples of a regularly varying stochastic process so that θ and ϑ are both between 0 and 1 and yet not the same."
   - BKW, p. 2: "for most examples … the two indices are the same", and the model is "qualitatively different from all the other examples we are aware of in the sense that θ < ϑ".
   - So as of 2024–26 the experts know of no other θ < ϑ example. Ours has ϑ = 1, which is at the edge of the BW phrasing ("both between 0 and 1").
   - A trivial modification gives both indices in (0,1): add a fixed-lag component, e.g. max(Z_t, aZ_{t−1}, echo). This is not formalized; the values have not been computed.
2. **Weissman & Cohen**, "The extremal index and clustering of high values for derived stationary sequences", J. Appl. Probab. 32 (1995) 972–981, doi:10.2307/3215211. It covers moving maxima with *random translations*, plus maxima and mixtures of sequences.
   - [unverified details] If the random lags are independent of the shock sizes, as the abstract suggests, the lags stay tight at high levels. The tail process then sees them, so θ = ϑ.
   - The essential new ingredient in the echo is that **the lag depends on the shock size and diverges at extreme levels**.
3. **Smith**, "A counterexample concerning the extremal index", Adv. Appl. Probab. 20 (1988) 681–683, and its dynamical emulation by Abadi–Freitas–Freitas (θ = 1/2 with a Poisson limit).
   - This is a different pathology: mean cluster size ≠ 1/θ.
   - BW Remark 1.7 cites KS Example 14.4.5: in Smith's example θ = ϑ.
4. **Gaussian sequences with r_n log n → γ** (Mittal & Ylvisaker, SPA 3 (1975) 1–18). They are asymptotically independent at every fixed lag, yet the classical limit fails. But that is not a regularly varying setting and there is no θ there. This is only a loose analogy: dependence at a level-dependent scale that is invisible to finite-dimensional tail limits.
5. **Ferro's tail-chain chapter** (https://empslocal.ex.ac.uk/people/staff/ferro/Publications/chapter10.pdf) states that asymptotic independence of (X_1, X_2) gives θ = 1 in the Markov tail-chain setting. The echo is not Markov, and it shows the claim fails beyond that setting.

**Additional observation (my analysis, not formalized; worth checking and including).** The echo process is **geometrically β-mixing**. Couple the future after time t + h with an independent copy. The two disagree only if some shock at s ≤ t has L(Z_s) > t − s + h, so β_h ≤ Σ_{j≥0} P(L(Z) > j + h) = O(e^{−αh}) for the log lag.
- This makes the example sharper. With exponentially decaying β-mixing coefficients, the KS mixing condition needs blocks r_n ≳ (1/α) log n. Anticlustering needs r_n ≪ (1/α) log n. The two never hold together.
- The example therefore shows that **"strong (even geometric) mixing + Y_t → 0" does not imply θ = ϑ**. The KS-type theorem genuinely needs AC and mixing *at a common block length*.
- I found this statement nowhere in the literature. BW Remark 1.4 says only that (1.17) fails for r_n = o(log b_n) in their model.

**Verdict: likely new**, with medium-high confidence.
- It is the simplest known stationary regularly varying process with θ < ϑ, and the first explicit one with a trivial spectral tail process.
- Caveat: a construction this simple could exist in a thesis, a lecture note or the KS book's exercises. KS §7.5 and ch. 14 could not be checked. Ask an expert (e.g. P. Soulier, R. Kulik, Y. Wang) before claiming priority.

---

## 4. Block-length phase transition

**Our claim** (log lag): the cluster ratio tends to
- 1 if r_n = o(log n);
- (1 + min(1/(cα), 1))/2 if r_n / log n → c;
- 1/2 if log n = o(r_n).

Condition 𝒜 fails when r_n → ∞ with r_n / log n bounded, and holds for log n ≪ r_n = o(n).

**Prior work.**
- **BKW, Theorem 1.5:** for log d_n / log n → ρ ∈ [0,1], P(max_{k ≤ d_n} X_k > b_n x) ~ ϑ_ρ d_n P(X_0 > b_n x), with ϑ_ρ = (1 − 2ρβ) q_{F,2}, ϑ_0 = ϑ and ϑ_1 = θ.
  - This is a **continuous, linear transition across polynomial scales**.
  - Cor. 1.6: AC(d_n, b_n) fails whenever d_n ≫ n^ε.
  - §1.4: "A sufficient condition d_n = o(log n) can be established by adapting the proof of [3, Lemma 5.2]."
- **BW (1.16)–(1.17):** AC holds for r_n = o(log b_n); the mixing condition (1.17) therefore fails for such r_n.
- **BKW's open questions (§1.4, verbatim):**
  - "It would be very interesting to know whether such a phase transition exists for any other regularly varying stochastic processes."
  - "It would also be interesting to know whether there are models such that the anticlustering condition holds with lim log d_n / log n = ρ for ρ up to certain ρ_0 < 1 only."
- **Estimators and block size.** Theory and simulations show sensitivity to the run length or block size: Smith–Weissman 1994; Weissman–Novak 1998; Ferro & Segers, JRSS B 65 (2003) 545–556 (intervals estimator, free of a block length); Süveges, Extremes 10 (2007) 41–55 (K-gaps, assumes D^(K+1)); Robert, Ann. Statist. 37 (2009) 271–310; Robert, Segers & Ferro, EJS 3 (2009) 993–1020; Drees & Rootzén, Ann. Statist. 38 (2010) 2145–2186. These treat the effect as bias under mixing + AC. None exhibits a limit that depends on the scale of r_n.

**How ours relates.**
- **First BKW question:** answered "yes, in a different form". Ours is a second model with a block-length transition, at the **logarithmic** scale, with an explicit kink at c = 1/α (the echo-lag scale (1/α) log n).
  - In BKW's polynomial parametrisation it is degenerate: ϑ_ρ = θ for every ρ > 0, and ρ = 0 splits according to c.
  - So it is not a counterexample to anything BKW say; it is a complementary "sub-mesoscopic" transition.
- **Second BKW question (heuristic, not formalized but cheap to add):**
  - Take a power lag L(z) = ⌈z^γ⌉ with 0 < γ < α. Then E L(Z) < ∞ and L → ∞, so the **existing formal theorem already gives θ = 1/2 and ϑ = 1**.
  - At level b_n ≈ n^{1/α}, the echo lag is ≈ n^{γ/α} = n^{ρ_0} with ρ_0 = γ/α ∈ (0,1).
  - I expect AC(d_n, b_n) to hold iff d_n = o(n^{ρ_0}), up to slowly varying effects at ρ = ρ_0.
  - The mesoscopic index would then be a **step**: ϑ_ρ = 1 for ρ < ρ_0 and 1/2 for ρ > ρ_0. That contrasts with BKW's linear ϑ_ρ.
  - The β-mixing coefficients decay like h^{1 − 1/ρ_0}, which still allows A(u_n) for n^{ρ_0} ≪ r_n ≪ n.
  - This would **answer BKW's second question affirmatively for every ρ_0 ∈ (0,1)**. It is the strongest selling point available and should be proved before writing.
- **Estimators (heuristic).**
  - In the echo, the normalized inter-exceedance times p_n T converge to (1 − θ)δ_0 + θ·Exp(θ), because echo gaps ~ log n are o(1/p_n). So the Ferro–Segers intervals estimator should be consistent for θ = 1/2.
  - The runs estimator with fixed run length, short blocks, and plausibly K-gaps with fixed K should converge to ϑ = 1, i.e. be inconsistent. K-gaps sees every echo gap as > K, so the MLE is pushed to 1.
  - A short simulation table would make this concrete. It is the part statisticians will care about.

**Verdict:** the phenomenon type is known (BKW); our explicit log-scale transition and the power-lag answer to BKW's question are **likely new**.

---

## 5. Mixture example

The mixture (constant w.p. p, iid w.p. 1 − p) satisfies P(M_n ≤ u_n) → p + (1 − p)e^{−τ}, so no θ exists. This is standard non-ergodic folklore. Leadbetter (1983) shows that under D(u_n) the limit must be e^{−θτ}, and non-ergodic mixtures are the textbook way to break this. Weissman–Cohen (1995) treat mixtures of stationary sequences explicitly [unverified details]. In tail-process language, Θ ≡ 1 w.p. p and e_0 w.p. 1 − p, so ϑ = 1 − p. That is routine.

The only new content is the remark that **η = 0 (cluster ratio → ϑ) is strictly weaker than AC and does not imply that θ exists**. **Verdict: known example, minor new remark.** Use it as a one-paragraph illustration.

---

## Is a short paper warranted?

**Yes, a short note is justified**, provided it is centred on the echo process and not on the gap identity.

- **New:** a strikingly simple, explicit, geometrically mixing [to verify] regularly varying process with Θ = e_0 (ϑ = 1) and θ = 1/2. It is only the second θ < ϑ mechanism in the literature and by far the simplest. It also gives an explicit logarithmic block-length transition.
- **Possibly new:** a power-lag variant that appears to answer BKW's second open question (AC exactly up to n^{ρ_0}) and gives a step-shaped mesoscopic index.
- **Supporting material (repackaging):** θ ≤ ϑ with minimal hypotheses, and the identity θ = ϑ − η under 𝒜 with η the late-return mass.
- **Selling point for some venues:** all statements are machine-checked in Lean 4/Mathlib. Put this in a remark or appendix with a repository link. Do not make it the main contribution for a probability journal.
- **Risks:**
  - The KS book (§7.5, ch. 14 examples and exercises) could contain a similar example. Check a physical copy.
  - Referees will view item 2 as elementary.
  - The power-lag AC claim and the β-mixing claim are not formalized. Prove them on paper at least.

**Venue options.**
- **Extremes** — best fit if the note includes the power-lag result answering BKW plus the estimator consequences. Direct audience (Kulik, Soulier, Segers, Wang publish there).
- **Statistics & Probability Letters** — appropriate for a ≤ 10-page note with just the echo process, θ ≤ ϑ, the gap identity and the log-scale transition. Fast and accepts "simple counterexample" papers.
- **J. Appl. Probab. (short communication)** — also fine for the minimal version, comparable to Smith 1988 and Weissman–Cohen 1995.
- **arXiv (math.PR, cross-list stat.TH)** in any case, posted first.

**Recommendation:** add the power-lag theorem (at least on paper) and a small estimator simulation, then submit to *Extremes*. Without them, submit to *Statistics & Probability Letters*.

**Suggested title:** "An echo process: a simple regularly varying sequence whose extremal index is invisible to its tail process". Alternative: "Late returns and the gap between the extremal index and the candidate extremal index".

**Suggested abstract.**
> For a stationary regularly varying sequence the candidate extremal index ϑ, computed from the spectral tail process, always dominates the extremal index θ, with equality under the usual anticlustering and mixing conditions; the only previously known examples with θ < ϑ are stable-regenerative multiple-stable models. We show that the gap is governed by an explicit quantity: the late-return mass η, the limiting conditional probability that an exceedance is followed, within the same block but beyond every fixed lag, by another exceedance. Without any mixing or anticlustering assumption, the normalised block-exceedance ratio converges to ϑ − η whenever either side exists, and θ = ϑ − η under Leadbetter-type block asymptotic independence. We then introduce the echo process, in which each iid Pareto shock reappears once after a lag that grows with its size. It is stationary, regularly varying and geometrically β-mixing, its spectral tail process is that of an iid sequence (ϑ = 1), yet θ = 1/2. For logarithmic lags the block ratio exhibits an explicit phase transition at block lengths of order log n, and anticlustering and mixing can never hold for a common block length. With power lags the transition moves to polynomial block lengths n^{ρ_0}, for any ρ_0 ∈ (0,1), answering a question of Bai, Kulik and Wang. We discuss consequences for runs, blocks and inter-exceedance estimators of θ. All results except [list] have been formally verified in the Lean 4 proof assistant.

(Drop the clauses on β-mixing and power lags unless they are proved.)

---

## Reference list (with links)

- Bai, Kulik, Wang. A remarkable example on clustering of extremes for regularly-varying stochastic processes. Ann. Appl. Probab. 36(4) (2026) 3132–3168. https://arxiv.org/abs/2409.17966 , https://doi.org/10.1214/26-AAP2298
- Bai, Wang. Tail processes for stable-regenerative multiple-stable model. Bernoulli 29(4) (2023) 3255–3279. https://arxiv.org/abs/2110.07499 , https://doi.org/10.3150/22-BEJ1582
- Bai, Wang. Phase transition for extremes of a family of stationary multiple-stable processes. AIHP 60(3) (2024) 2157–2193. https://arxiv.org/abs/2110.07497
- Kulik, Soulier. Heavy-Tailed Time Series. Springer 2020 (Lemma 7.5.4, Eq. (7.5.4b), Cor. 6.2.6, Example 14.4.5 — text not checked).
- Planinić, Soulier. The tail process revisited. Extremes 21 (2018) 551–579. https://arxiv.org/abs/1706.04767
- Basrak, Segers. Regularly varying multivariate time series. SPA 119 (2009) 1055–1080.
- Segers. Rare events, temporal dependence, and the extremal index. J. Appl. Probab. 43 (2006) 463–485. https://doi.org/10.1239/jap/1152413735
- O'Brien. Extreme values for stationary and Markov sequences. Ann. Probab. 15 (1987) 281–291.
- Leadbetter. Extremes and local dependence in stationary sequences. Z. Wahrsch. Verw. Gebiete 65 (1983) 291–306.
- Chernick, Hsing, McCormick. Calculating the extremal index for a class of stationary sequences. Adv. Appl. Probab. 23 (1991) 835–850.
- Hsing. Extremal index estimation for a weakly dependent stationary sequence. Ann. Statist. 21 (1993) 2043–2071.
- Smith. A counterexample concerning the extremal index. Adv. Appl. Probab. 20 (1988) 681–683. https://doi.org/10.1017/S0001867800018218
- Smith. The extremal index for a Markov chain. J. Appl. Probab. 29 (1992) 37–45.
- Smith, Weissman. Estimating the extremal index. JRSS B 56 (1994) 515–528.
- Weissman, Novak. On blocks and runs estimators of the extremal index. JSPI 66 (1998) 281–288.
- Weissman, Cohen. The extremal index and clustering of high values for derived stationary sequences. J. Appl. Probab. 32 (1995) 972–981. https://doi.org/10.2307/3215211
- Ferro, Segers. Inference for clusters of extreme values. JRSS B 65 (2003) 545–556.
- Süveges. Likelihood estimation of the extremal index. Extremes 10 (2007) 41–55.
- Robert. Inference for the limiting cluster size distribution of extreme values. Ann. Statist. 37 (2009) 271–310.
- Robert, Segers, Ferro. A sliding blocks estimator for the extremal index. EJS 3 (2009) 993–1020.
- Drees, Rootzén. Limit theorems for empirical processes of cluster functionals. Ann. Statist. 38 (2010) 2145–2186.
- Davis, Hsing. Point process and partial sum convergence for weakly dependent random variables with infinite variance. Ann. Probab. 23 (1995) 879–917.
- Buriticá, Meyer, Mikosch, Wintenberger. Some variations on the extremal index. Zap. Nauchn. Sem. POMI 501 (2021). https://arxiv.org/abs/2106.05117
- Abadi, Freitas, Freitas. Dynamical counterexamples regarding the extremal index and the mean of the limiting cluster size distribution. https://arxiv.org/abs/1808.02970
- Kevei, Kubatovics. Heavy-tailed critical Galton–Watson processes with immigration (θ = 0 = ϑ, AC fails). https://arxiv.org/abs/2510.02004
- Mittal, Ylvisaker. Limit distributions for the maxima of stationary Gaussian processes. SPA 3 (1975) 1–18.
