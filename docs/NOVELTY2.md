# Novelty check 2: power-lag echo (A) and mixing without θ = ϑ (B)

Date: 2026-10-18. This builds on `novelty_report.md` (same scratchpad), which covered the log-lag echo, θ ≤ ϑ, the gap formula and the mixture.

Lean statements checked against the source:
- `ExtremeValueTheory/Dependence/EchoPowerLag.lean`: `powEchoProcess_polyBlocks`, `powEchoProcess_antiClustering_iff`, `powEchoProcess_critical`.
- `ExtremeValueTheory/Dependence/EchoMixing.lean`: `isBetaMixing_echoProcess`, `powEchoProcess_not_conditionA`, `powEchoProcess_not_conditionA_and_antiClustering`.
- `ExtremeValueTheory/Dependence/Anticlustering.lean`: the definitions `AntiClusteringAt` and `AntiClustering`.

Sources read in full text:
- BKW: Bai, Kulik, Wang, arXiv:2409.17966 v2. The local copy is `pdfs/bkw.txt`.
- BW: Bai, Wang, arXiv:2110.07499 (Bernoulli 2023).
- AFF: Abadi, Freitas, Freitas, arXiv:1808.02970 (J. London Math. Soc. 2020).
- KK: Kevei, Kubatovics, arXiv:2510.02004, abstract and introduction.
- BD: Bai, Düker, arXiv:2510.10578, abstract and introduction.

Not accessible:
- The published Ann. Appl. Probab. version of BKW (36(4), 2026, doi:10.1214/26-AAP2298); the site is behind a bot wall.
- The Kulik–Soulier (2020) book.
- Weissman–Cohen (1995), full text; only the abstract was read.
- Chernick–Hsing–McCormick (1991), full text.
- Smith (1988, 1992), full text.

Everything that depends on these is marked **[unverified]**.

---

## 1. What BKW actually ask, and whether (A) answers it

**Verbatim (arXiv v2, §1.4 "Comments", p. 7):**

> "It would be very interesting to know whether such a phase transition exists for any other regularly varying stochastic processes. It would also be interesting to know whether there are models such that the anticlustering condition holds with lim_{n→∞} log d_n / log n = ρ for ρ up to certain ρ₀ < 1 only."

**Context and definitions (BKW pp. 1–7):**
- **Levels.** b_n satisfies n P(X₀ > b_n) → 1, see their (1.1)/(1.8). The processes are nonnegative.
- **AC(d_n, b_n).** For all x, y > 0, lim_{m→∞} limsup_n P(max_{m≤|j|≤d_n} X_j > b_n x | X₀ > b_n y) = 0.
- **The setting is "weak extremal dependence".** This means (1.1) holds, i.e. an extremal index θ exists. It is not otherwise restricted to a model class.
- **Their own model.** AC holds for d_n = o(log n) (claimed via BW Lemma 5.2) and fails whenever d_n ≫ n^ε (Cor. 1.6). The range log n ≪ d_n ≪ n^ε is left open. So, as far as is known, their model has "ρ₀ = 0".
- **Contrast they draw.** For iid and "most" weakly dependent models, AC holds for every d_n = o(n), i.e. "ρ₀ = 1".
- **What the question asks.** An intermediate cutoff ρ₀ ∈ (0,1).

**Match with the Lean statement.**
- **Levels.** Lean uses a_n with n P(X₀ > a_n) → τ > 0 and all levels a_n x. This contains BKW's b_n (τ = 1).
- **Window.** Lean's `AntiClusteringAt` is two-sided (m ≤ |t| ≤ r_n), as in BKW.
- **Levels in the conditioning and the event.** Lean uses the same level for both (Basrak–Segers / KS form); BKW use x and y.
  - The two forms are equivalent, by an elementary argument that is not in Lean.
  - If y ≥ x, then P(max > b_n x, X₀ > b_n y) ≤ P(max > b_n x, X₀ > b_n x), and P(X₀ > b_n x)/P(X₀ > b_n y) → (y/x)^α.
  - If y < x, then {max > b_n x} ⊂ {max > b_n y}.
  - So the same-level condition for all x implies BKW's condition. The converse is the case x = y.
- **Failure direction.** The failure part proves that even the *forward* half fails, which is stronger.

**The result (A), as proved.**
- For every γ ∈ (0, α), every ρ ∈ (0,1) with ρ ≠ γ/α, and every r_n with log r_n / log n → ρ: AC(r_n) at the normalizing levels holds **iff** ρ < γ/α.
- Since γ/α ranges over all of (0,1), every cutoff ρ₀ ∈ (0,1) is realized.
- **Endpoints ρ = 0 and ρ = 1.** These follow from monotonicity of AC in the block length, which is not formalized.
  - If AC holds for r'_n ≥ r_n eventually, it holds for r_n.
  - So ρ = 0 (with r_n → ∞) gives AC: compare with ⌈n^{ρ'}⌉ for some ρ' < γ/α.
  - And ρ = 1 gives failure: compare with ⌈n^{ρ'}⌉ for some ρ' > γ/α.
- **The critical scale ρ = γ/α.** The answer depends on the constant in r_n ~ c n^{γ/α}: AC fails if κ = (2/τ)^{γ/α}/c < 1 and holds if κ > 1. The case κ = 1 is not decided.
  - The question is about ranges of ρ, so this does not matter for the answer. It must still be stated as "for ρ ≠ ρ₀".
- **Requirement (1.1).** θ = 1/2 exists (Lean, `powEchoProcess_theta_lt_vartheta`), so the process has "weak extremal dependence" in BKW's sense.

**Verdict on fit: (A) answers the second question as literally stated, for every ρ₀ ∈ (0,1).** Caveats to state honestly:
1. **The question is informal ("models such that…").** Nothing in BKW suggests they wanted a particular class, such as stable or long-memory models. The text calls for "other regularly varying stochastic processes". A very simple iid-driven, β-mixing model is a legitimate answer. Arguably it is a *stronger* one, because it shows that the phenomenon does not need long-range dependence.
2. **The cutoff is exact and the mesoscopic transition is a step.** In BKW's mesoscopic language, P(max_{k≤d_n} X_k > b_n x) ~ ϑ_ρ d_n P(X₀ > b_n x) holds with ϑ_ρ = 1 for ρ < γ/α and ϑ_ρ = 1/2 = θ for ρ > γ/α.
   - This is our `powEchoProcess_polyBlocks` statement: the cluster ratio tends to 1 below the cutoff and to 1/2 above it.
   - `clusterRatio` (`Dependence/Anticlustering.lean:296`) is P(max_{0≤t<r_n} |X_t| > u_n)/(r_n P(|X₀| > u_n)), which is exactly BKW's ratio in (1.15). Any u_n with n P(X₀ > u_n) → τ covers b_n x.
   - It is a different shape from BKW's linear ϑ_ρ = (1 − 2ρβ) q_{F,2}. So the same example also gives a partial answer to the *first* question ("such a phase transition"): it is a mesoscopic transition, but discontinuous rather than interpolating. Say "a phase transition of a different (step) type", not "the same".
3. **Only the normalizing levels are covered.** KS-style AC(r_n, c_n) at intermediate levels (r_n P(X > c_n) → 0) is not covered.
   - Heuristically, AC(r_n, c_n) holds iff r_n ≪ c_n^γ. This is unproved and should be stated as a remark at most.
4. **The published version could not be checked.** It is possible that the AAP 2026 version rephrases or drops the question. **[unverified; check the journal PDF before citing page numbers.]** Cite "arXiv:2409.17966v2, §1.4" explicitly.

---

## 2. Search for prior examples

### Papers citing BKW or BW, checked October 2026

**Citations of BKW** (Semantic Scholar and OpenAlex; Google Scholar not reachable):
- **Only one citing paper:** "Multiple extremal integrals" (arXiv:2503.23142, EJP 2026). It is about integrals, not an AC example (checked in the first report).

**Citations of BW:**
- **Bai–Düker, "On extremes for Gaussian subordination"** (arXiv:2510.10578, SPA 2026). It covers subordinated Gaussian processes and m-extremal dependence. It does not address AC at polynomial block scales or θ ≠ ϑ.
- **Kevei–Kubatovics, "Heavy-tailed critical Galton–Watson processes with immigration"** (arXiv:2510.02004, SPA 2026). The abstract says "the extremal index of the process is 0". The persistence of a large immigration means the tail process does not vanish, so AC fails at every block length. This does not answer either question.
- **Others:** "Tail measures and regular variation" (EJP 2022), "Cluster random fields and random-shift representations" (JTP 2025), and "Joint sum-and-max limit…" (JTP 2023). None of these is about AC cutoffs (titles and abstracts only).

**arXiv API sweeps** (abstract or full metadata, sorted by date, Sept 2024 to Oct 2026):
- Queries: "candidate extremal index", "anticlustering" / "anti-clustering", "extremal index" + "tail process", "extremal index" + mixing, "spectral tail process".
- Result: no new paper on AC cutoffs or θ ≠ ϑ beyond those listed above.

### Classical and other candidates

| Source | What it has | Relation to (A) and (B) |
|---|---|---|
| BW 2023 (Bernoulli 29, doi:10.3150/22-BEJ1582) | θ < ϑ for the stable-regenerative model; AC for r_n = o(log b_n); the mixing condition (1.17) fails for such r_n | BW, p. 3: "we are not aware of any other examples of a regularly varying stochastic process so that θ and ϑ are both between 0 and 1 and yet not the same." BW, p. 7: "Our results indicate that our model does not enjoy very strong mixing properties." So the only prior θ < ϑ example is explicitly *not* claimed to be strongly mixing. This supports (B) directly. |
| BKW 2024/26 | "ρ₀ = 0" (AC fails above n^ε) | This is the question itself, not an answer to it. |
| Kulik–Soulier 2020, Lemma 7.5.4 (θ ≤ ϑ); Cor. 6.2.6; §7.4.1 (β-mixing ⇒ condition A) | The standard sufficient route to θ = ϑ: AC(r_n) and the mixing condition at the same r_n | (B) shows that the shared r_n cannot be dropped. **[unverified: KS ch. 6–7 and 14–15 examples and problems not read.]** BKW (Kulik is a coauthor) call their model "qualitatively different from all the other examples we are aware of", which is strong indirect evidence that the book has no θ < ϑ example. |
| KS Example 14.4.5 and Smith 1988 (Adv. Appl. Probab. 20, 681–683) | θ < 1 with a simple Poisson limit (mean cluster size ≠ 1/θ) | Per BW Remark 1.7 citing KS Example 14.4.5, θ = ϑ there. This is a different pathology, and the tail process does not vanish. |
| AFF 2020 (arXiv:1808.02970) | Dynamical counterexamples (Manneville–Pomeau, indifferent fixed point): EI ≠ 1/mean cluster size, "escape of mass" | A different phenomenon: it mixes EI = 0 with EI > 0 behaviour. There is no tail process and no AC cutoff. |
| Weissman–Cohen 1995 (J. Appl. Probab. 32, 972–981, doi:10.1017/S0021900200103456) | Abstract: "moving-maximum sequence (with random translations)" from iid variables | This is the closest structural relative. **[unverified]** Whether the random translations may depend on the shock size: the abstract suggests they do not. If they are independent of the shocks, the lag is tight at high levels, the tail process sees it, AC holds for r_n = o(n), and θ = ϑ. **Must be read before submission.** If WC allow size-dependent translations that grow with the shock size, they would contain the mechanism, though almost certainly not the AC-cutoff or tail-process analysis. |
| Chernick–Hsing–McCormick 1991 (Adv. Appl. Probab. 23, 835–850); Hsing–McCormick; O'Brien 1987 | θ = lim P(M_{1,k} ≤ u_n \| X₀ > u_n) under D^{(k)}(u_n); under mixing, O'Brien's formula with run length r_n → ∞ | In tail-process terms, D^{(k)} for some k means "no late returns". (B) is equivalent to a β-mixing sequence for which D^{(k)} fails for every k while lim_k of the fixed-k runs formula exists and differs from θ. That such sequences *can* exist is implicit in the classical theory (D^{(k)} is an extra hypothesis). **I found no explicit published example with strong mixing and pairwise extremal independence at every fixed lag.** CHM's own examples were not read. **[unverified]** |
| Mikosch–Wintenberger 2013/14/16; Davis–Hsing 1995; Basrak–Segers 2009; Kulik–Soulier–Wintenberger 2019 | AC verified for Markov, GARCH and linear models, typically for every r_n = o(n) or under drift conditions | No model where AC holds only below n^{ρ₀}. Linear processes with summable \|ψ_j\|^α satisfy AC because the echo of a big jump at lag j has tail weight ψ_j^α, independent of the shock size. |
| Coupled continuous-time random maxima (Meerschaert–Stoev 2009; Hees–Scheffler and coauthors) | Waiting times coupled with magnitudes | These are scaling limits of renewal-type maxima, not stationary sequences with AC or a tail process. At most a loose analogy for "delay depending on size". **[from memory; not re-read]** |
| Gaussian subordination (BD 2025); Mittal–Ylvisaker 1975 | Extremal independence at fixed lags; long memory | θ = 1 (Berman-type) or no RV setting; no cutoff. |

---

## 3. Verdicts

### (A) Power-lag echo: AC holds exactly for log r_n / log n < γ/α

**Verdict: new, with medium-high confidence.** It appears to be the first published or publishable answer to BKW's second question.
- No example with an AC cutoff strictly inside (0,1) was found in BKW, BW, papers citing either, KS (indirectly, via BKW's statement), or the classical AC literature.
- The mechanism (a delayed echo whose delay grows with the shock size) was not found in that form either, beyond the unverified Weissman–Cohen caveat.

**Suggested phrasing:**

> "Bai, Kulik and Wang [arXiv:2409.17966v2, §1.4] ask whether there are models for which the anticlustering condition AC(d_n, b_n) holds when log d_n/log n → ρ only for ρ up to some ρ₀ < 1. For every ρ₀ ∈ (0,1) the power-lag echo process with γ = ρ₀α is such a model: it is stationary, regularly varying with index α, β-mixing, has extremal index θ = 1/2, and AC(d_n, b_n) holds if log d_n/log n → ρ < ρ₀ and fails if ρ > ρ₀ (at ρ = ρ₀ the answer depends on the constant in d_n ~ c n^{ρ₀})."

Do **not** write:
- "the" model BKW had in mind;
- "resolves the open problem" without the "for every ρ₀ ∈ (0,1)" qualifier;
- that the transition is "of the same type" as BKW's (theirs is linear in ρ, ours is a step).

Mention in the same paragraph that the example also has θ < ϑ (θ = 1/2, ϑ = 1). Because it is β-mixing, it is the second known θ < ϑ mechanism and the first in which mixing is available.

### (B) β-mixing with a vanishing tail process does not imply θ = ϑ

**Verdict: likely new as an explicit example in the regularly-varying / tail-process framework; the principle is partially known.**
- **Known.** The standard theorem (Basrak–Segers 2009; KS20 ch. 7) needs AC(r_n) *and* the mixing condition A(a_n) at the same r_n. Classically, the runs/local formula for θ needs D^{(k)} (CHM 1991) on top of D(u_n). So experts will not be surprised that mixing alone is insufficient.
- **New, as far as I can tell.**
  1. An explicit, very simple stationary model that is β-mixing (geometrically for the log lag; for the power lag β(h) ≲ Σ_{m≥0} P(Z^γ ≥ h+m) ~ h^{1−α/γ}, so polynomial), regularly varying, with the iid spectral tail process Θ_t = 1{t=0} (ϑ = 1), yet θ = 1/2.
  2. A proof that on every polynomial block scale (ρ ∈ (0,1), ρ ≠ γ/α) AC and condition A are never simultaneously satisfied, although each holds on its own range of scales.

  BW explicitly say that their θ < ϑ model lacks "very strong mixing properties", so no prior θ < ϑ example in the RV literature is known to be strongly mixing.
- **Caveats.**
  - The Lean `IsBetaMixing` only asserts β(h) → 0. "Geometric" is `betaMixing_logEchoProcess_le`, for the log lag only.
  - The power-lag rate h^{1−α/γ} above is my heuristic from the coupling bound in `isBetaMixing_echoProcess` (Σ_m P(L(Z) ≥ h+m)), not a stated Lean theorem.
  - "Strong mixing" should be read as α- or β-mixing; the echo is not φ-mixing-proved.

**Suggested phrasing:**

> "Strong mixing and a vanishing tail process (even Θ_t = 0 for all t ≠ 0) do not imply θ = ϑ: the echo process is β-mixing, has the spectral tail process of an iid sequence, and θ = 1/2 < 1 = ϑ. In the standard argument (Basrak–Segers; Kulik–Soulier, Ch. 7) the anticlustering and mixing conditions must hold for a common block length; for the echo process they hold on disjoint ranges of block lengths. Equivalently, in Leadbetter's framework, D(u_n) holds but D^{(k)}(u_n) fails for every k."

The last sentence is a consequence I have not formalized: β-mixing implies D(u_n), and D^{(k)} must fail because θ ≠ ϑ. Mark it as a remark.

Avoid "counterexample to a conjecture": nobody conjectured the implication. Present it as a "sharp example showing that the common-block-length hypothesis cannot be removed".

---

## 4. Remaining checks before claiming priority (ordered by risk)

1. **Weissman–Cohen 1995, full text:** are the random translations allowed to depend on the shock size? This is the highest risk for the *mechanism*, though not for the AC-cutoff result.
2. **Kulik–Soulier 2020:** §6.1–6.2, §7.4–7.5 (around Lemma 7.5.4) and ch. 14–15 examples and problems. Look for any "delayed copy" or "random lag" example. Also confirm the exact hypotheses of Lemma 7.5.4 and Cor. 6.2.6.
3. **The published AAP version of BKW:** confirm the open question survives with the same wording, and get page numbers.
4. **Chernick–Hsing–McCormick 1991, examples section:** check for any D(u_n)-but-no-D^{(k)} example with extremal independence at all lags. This is a risk for (B)'s classical framing only.
5. **Optional:** email Y. Wang, S. Bai or R. Kulik with the example; they posed the question and would know of unpublished answers.

## Sources

- BKW: https://arxiv.org/abs/2409.17966 (v2, §1.4, p. 7; Cor. 1.6); AAP 36(4) 2026, https://doi.org/10.1214/26-AAP2298
- BW: https://arxiv.org/abs/2110.07499 (p. 3 "not aware of any other examples"; Remark 1.4, p. 7 "does not enjoy very strong mixing properties"; Remark 1.7 on Smith/KS Ex. 14.4.5); https://doi.org/10.3150/22-BEJ1582
- AFF: https://arxiv.org/abs/1808.02970
- Kevei–Kubatovics: https://arxiv.org/abs/2510.02004
- Bai–Düker: https://arxiv.org/abs/2510.10578
- Multiple extremal integrals: https://arxiv.org/abs/2503.23142
- Weissman–Cohen 1995 (abstract only): https://doi.org/10.1017/S0021900200103456
- Smith 1988: https://www.cambridge.org/core/journals/advances-in-applied-probability/article/a-counterexample-concerning-the-extremal-index/42B0AC0CBC4D0EB6A9642ED91B785702
- Smith 1992, Markov chain EI (abstract): https://iaorifors.com/paper/10211
- Chernick–Hsing–McCormick 1991: https://doi.org/10.1017/S0001867800023971
- Kulik–Soulier, Heavy-Tailed Time Series (2020): https://doi.org/10.1007/978-1-0716-0737-4
