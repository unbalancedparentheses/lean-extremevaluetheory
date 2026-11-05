# Comparison with Hirata's Isabelle formalization

Date: 2026-11-04.

Michikazu Hirata independently formalized extreme value theory in Isabelle/HOL, in two entries of
the Archive of Formal Proofs (AFP), both dated 11 September 2026:
[Extreme Value Theory](https://isa-afp.org/entries/Extreme_Value_Theory.html) and
[Regular Variation](https://isa-afp.org/entries/Regular_Variation.html). The Extreme Value Theory
entry page carries the note "More than 95% of the Isabelle codes were written by a generative AI."
The Regular Variation page has no such note.

Two independent formal statements of one theorem check each other. This document compares them,
in both directions.

**What was read.**

| Source | Version | sha256 (start) |
|---|---|---|
| `afp-Extreme_Value_Theory-current.tar.gz` | current release on 2026-11-04 (`Last-Modified` 4 Nov 2026 15:53 GMT); the page names no other version number | `f744d1f89aea363e` |
| `afp-Regular_Variation-current.tar.gz` | same | `d3021a23c279a9df` |
| Isabelle library: `Weak_Convergence.thy`, `Uniform_Limit.thy`, `Topological_Spaces.thy`, `Transcendental.thy` | `isabelle-prover/mirror-isabelle` on GitHub, master, 2026-11-04, for `right_continuous_mono`, `weak_conv`, `uniform_limit`, `at_left`, `powr` | not recorded |
| This library | commit `99fe16a` | |

**Limits of this comparison.** All statements and definitions were read in the theory sources, about
18,600 lines. Most proofs were not read. Nothing was run: neither Isabelle nor Lean. A search of the
sources finds no `sorry`, `oops` or `axiomatization`, and AFP entries are machine-checked on
submission. Books were not consulted: citations to them below are as the two libraries give them,
and BGT Theorem 1.5.2 is partly from memory (marked where used). "Equivalent" below is an argument
written here, not a mechanized one. Absence claims ("we lack") rest on searches of the source tree;
they may miss a differently named theorem.

In quotations, Isabelle symbols such as `\<gamma>` are written `γ`.

## Summary

| Topic | Hirata | This library | Verdict |
|---|---|---|---|
| Distribution function, degenerate, normalization | `right_continuous_mono F 0 1`, `degenerate_df`, `F (a n * x + b n) ^ n` | `CumulativeDistributionFunction`, `IsDegenerate`, `((As n • F) x) ^ n` | Same notions |
| GEV family | `EVD_cdf ξ μ σ` | `gevCDF ξ`, `gevFun`, `gevLocScaleCDF` | Same formula and sign |
| GPD | `GPD_cdf ξ μ σ` | `gpdSurvivalAll ξ β` | Same on `x ≥ 0` |
| Fisher–Tippett–Gnedenko | `Fisher_Tippett_Gnedenko` | `IsExtremeValueDistr.classification`, `.exists_smul_eq_gevCDF` | Equivalent |
| Maximum domain of attraction | `domain_of_attraction F (EVD_cdf γ 0 1)` | `IsInMDAGEV ξ`, a case split on `Φ`, `Ψ`, `Λ` | Equivalent, but on our side the link to `gevCDF ξ` is not a theorem |
| Pickands–Balkema–de Haan | `Pickands_Balkema_de_Haan` | `isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival` | Equivalent. Same filter, no condition on the endpoint |
| Regular variation, definition | `regularly_varying` | `IsRegularlyVarying` | Differ by design; equivalent up to measurability and changing `f` away from `∞` |
| Uniform convergence on compacts | `regularly_varying_UCT_interval` | `tendstoUniformlyOn_of_measurable` | Equivalent by truncation |
| Uniform convergence on `(0,a]`, `[a,∞)` | `regularly_varying_pos_UCT`, `_neg_UCT` | not found | **Ours lacks it** |
| Representation | all indices `ρ` | slowly varying only | Equal at `ρ = 0`; **ours weaker in form** |
| Karamata, tail integrals, `ρ < -1` | `Karamata_theorem_half2` | `tendsto_integral_Ioi_div_of_measurable` | Equivalent by truncation |
| Karamata, `∫_a^t`, `ρ > -1` | `Karamata_theorem_half1` | `tendsto_integral_zero_div` | **Ours weaker**: lower limit `0`, stronger integrability |
| Karamata, `ρ = -1` | general | tail side only, antitone only | **Ours weaker** |
| Karamata, converse | `ρ < -1` and `ρ > -1`, no monotonicity | `α > 1`, antitone only | **Ours weaker** (already recorded in `FAITHFULNESS.md`) |
| Potter bounds | `Potter_bounds`, `_lower` | `potter_bounds_of_measurable` | Equivalent |
| Gnedenko's conditions, `γ ≠ 0` | `MDA_regularly_varying_pos`, `_neg` | `isInMDAFrechet_iff`, `isInMDAWeibull_iff` | Equivalent |
| Quantile form (dHF 1.1.6) | `MDA_iff_tail_quantile'` | `isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile` | Equivalent |
| von Mises | one second-order condition for all `γ`, plus first-order for `γ ≠ 0` | first-order for `γ ≠ 0`, second-order for `γ = 0` | Ours has weaker hypotheses; **theirs is unified** |

**No statement of ours was found to be wrong.** The two libraries agree on the main theorems,
including the sign of `ξ`, the filter along which the threshold moves, and the treatment of atoms at
the endpoint. No statement of Hirata's was found to be wrong either. Where they differ, ours is
missing results or assumes more, chiefly in regular variation. See the last section.

## Foundations

**Distribution functions.** Hirata works with plain functions `real ⇒ real` under
`right_continuous_mono F 0 1`:

```isabelle
locale right_continuous_mono =
  fixes f :: "real ⇒ real" and a b :: real
  assumes cont: "⋀x. continuous (at_right x) f"
  assumes mono: "mono f"
  assumes bot: "(f ⤏ a) at_bot"
  assumes top: "(f ⤏ b) at_top"
```

Ours is `CumulativeDistributionFunction`, a `StieltjesFunction ℝ` with `tendsto_atTop` to `1` and
`tendsto_atBot` to `0`. A Stieltjes function is monotone and right-continuous. The fields agree.
`ContinuousWithinAt f (Ici x) x` and `continuous (at_right x) f` agree since the point `x` itself
adds nothing.

**Degenerate.** `degenerate_df F ⟷ (∀x. F x = 0 ∨ F x = 1)` and `IsDegenerate F := ∀ x, F x = 0 ∨ F x = 1`.
Identical.

**Normalization.** Ours `(As n • F) x = F ((As n)⁻¹ x)` (`mulAction_apply_eq`, by `rfl`), with
`As n : AffineIncrEquiv`. So `F (a n * x + b n)` with `a n > 0`, as in Hirata. Both require positivity
for every `n`, including `n = 0`, where it says nothing. `F ^ 0 = 1` in both.

**Weak convergence.** `weak_conv F_seq F ≡ ∀x. isCont F x ⟶ (λn. F_seq n x) ⇢ F x`. Ours states the
same at `ContinuousAt G x`. Both are convergence at continuity points. Not along a subsequence, and
not with vague or improper limits: the limit must be a proper c.d.f. in both.

## Definitions of the limit laws

**Extreme value distribution.** Ours is intrinsic:

```lean
def IsExtremeValueDistr (G : CumulativeDistributionFunction) : Prop :=
  ¬G.IsDegenerate ∧
    ∃ (F : CumulativeDistributionFunction) (As : ℕ → AffineIncrEquiv),
      ∀ x, ContinuousAt G x → Tendsto (fun n ↦ ((As n • F) x)^n) atTop (𝓝 (G x))
```

Hirata has no such predicate. The same content appears as the hypotheses of his theorem.

**GEV and its sign.** Hirata defines a density, `EVD_density`, takes `EVD_cdf ξ μ σ` to be the `cdf` of
the resulting measure, and proves the closed form:

```isabelle
corollary EVD_cdf_def:
  assumes "0 < σ"
  shows "EVD_cdf ξ μ σ x =
           (let y = (x - μ) / σ in
            if ξ = 0 then exp (- exp (- y))
            else if ξ * y > - 1 then exp (- ((1 + ξ * y) powr (- 1 / ξ)))
            else if ξ > 0 then 0 else 1)"
```

```lean
noncomputable def gevFun (ξ x : ℝ) : ℝ :=
  if ξ = 0 then Real.exp (-Real.exp (-x))
  else if 0 < 1 + ξ * x then Real.exp (-(1 + ξ * x) ^ (-1 / ξ))
  else if 0 < ξ then 0 else 1
```

These are the same at `μ = 0, σ = 1`, and `gevLocScaleCDF ξ μ hσ x = H_ξ((x - μ)/σ)` matches the rest.
Both use the Jenkinson–von Mises sign: `ξ > 0` is Fréchet, `ξ < 0` is bounded above.

One trap on our side: in `classification` the bound variable called `ξ` in the Fréchet and Weibull
branches is the tail index `α` of `Φ_α`, `Ψ_α`, not the GEV shape. So `ξ` means `1/α` in `gevCDF` and
`α` in `classification`. Nothing is wrong, but a reader comparing the two would be misled.

**Generalized Pareto.** Hirata again defines a density and `GPD_cdf` as its `cdf`, and proves
`GPD_tail_eq`:

```isabelle
lemma GPD_tail_eq:
  assumes x: "0 ≤ x"
  shows "1 - GPD_cdf γ 0 1 x
           = (if γ = 0 then exp (- x)
              else if 0 ≤ 1 + γ * x then (1 + γ * x) powr (- 1 / γ) else 0)"
```

```lean
noncomputable def gpdSurvivalAll (ξ β x : ℝ) : ℝ :=
  if ξ = 0 then exp (-x / β) else (max (1 + ξ * x / β) 0) ^ (-(1 / ξ))
```

For `x ≥ 0`, `β = 1` these agree. When `1 + γ x ≥ 0` the `max` does nothing. When `1 + γ x < 0`, then
`γ < 0`, the exponent is positive, and Lean's `0 ^ p = 0` gives Hirata's `0`. At the endpoint
`1 + γ x = 0`, Isabelle's `0 powr p = 0` and Lean's `0 ^ p = 0` agree. Ours is not a survival function
for `x < 0` (it exceeds `1`), but no theorem compared here uses it there. Ours also has `gpdCDF`
(`1 - gpdSurvivalAll ξ σ (max x 0)`), which equals `GPD_cdf ξ 0 σ` for `σ > 0`.

**Maximum domain of attraction.**

```isabelle
definition domain_of_attraction :: "(real ⇒ real) ⇒ (real ⇒ real) ⇒ bool" where
"domain_of_attraction F G ⟷
   right_continuous_mono F 0 1 ∧ right_continuous_mono G 0 1 ∧
   (∃a b. (∀n::nat. 0 < a n) ∧ weak_conv (λn x. F (a n * x + b n) ^ n) G)"
```

```lean
def IsInMDAGEV (ξ : ℝ) : Prop :=
  if hξ : 0 < ξ then F.IsInMDAFrechet (one_div_pos.2 hξ)
  else if hξ' : ξ < 0 then F.IsInMDAWeibull (div_pos_of_neg_of_neg neg_one_lt_zero hξ')
  else F.IsInMDAGumbel
```

where each case is `∃ As, ∀ x, Tendsto (fun n ↦ ((As n • F) x) ^ n) atTop (𝓝 (Φ x))`, with `Ψ` or `Λ`
for `Φ`.

Verdict: `IsInMDAGEV ξ ⟷ domain_of_attraction F (EVD_cdf ξ 0 1)`, with two steps:

1. `Φ_α`, `Ψ_α`, `Λ` and `H_ξ` are continuous (`isCont_EVD_cdf`, `weak_conv_EVD_cdf_iff`), so "for
   every `x`" and "at continuity points" coincide.
2. The target is `Φ_{1/ξ}` in ours and `H_ξ` in his. These differ by a fixed affine map:
   `mkOfCoefs_smul_gevCDF_of_pos` says `B • H_ξ = Φ_{1/ξ}` with `B x = ξ x + 1`, and
   `mkOfCoefs_smul_gevCDF_of_neg` gives the Weibull case. If `((As n • F) x) ^ n → Φ_{1/ξ} x` for all `x`,
   then with `As' n = B⁻¹ * As n` we get `((As' n • F) x) ^ n = ((As n • F) (B x)) ^ n → Φ_{1/ξ} (B x) =
   H_ξ x`. The converse is the same with `B` inverted. Hirata proves the analogue,
   `domain_of_attraction_EVD_cdf_iff`.

This step is **not a theorem in our library**. Nothing connects `IsInMDAGEV ξ` to `gevCDF ξ`: the
`IsInMDAGEV` docstring names `H_ξ`, but the definition never mentions it, and `gevCDF` does not occur
in `DomainOfAttraction/` or `PeaksOverThreshold/`. Hirata's statement is against `H_ξ` directly. The
argument above shows ours is correct, but this is the one place where a reader must trust prose.

Hirata's `domain_of_attraction F G` also allows degenerate `G`. His theorems add
`¬ degenerate_df G` where needed. Ours fix the target, so the point does not arise, except in
`ExtremeValueDistr.domainOfAtraction`, whose `G` is nondegenerate by type.

## Fisher–Tippett–Gnedenko

```isabelle
theorem Fisher_Tippett_Gnedenko:
  fixes F G :: "real ⇒ real" and a b :: "nat ⇒ real"
  assumes F: "right_continuous_mono F 0 1" and G: "right_continuous_mono G 0 1"
    and deg: "¬ degenerate_df G"
    and a: "⋀n. 0 < a n"
    and wc: "weak_conv (λn x. F (a n * x + b n) ^ n) G"
  obtains γ μ σ where "0 < σ" and "G = EVD_cdf γ μ σ"
```

```lean
theorem classification {G : CumulativeDistributionFunction}
    (G_evd : G.IsExtremeValueDistr) :
    (∃ (A : AffineIncrEquiv), A • G = standardGumbelCDF) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ) , A • G = standardFrechetCDF hξ) ∨
      (∃ (A : AffineIncrEquiv) (ξ : ℝ) (hξ : 0 < ξ) , A • G = standardWeibullCDF hξ)

theorem IsExtremeValueDistr.exists_smul_eq_gevCDF
    {G : CumulativeDistributionFunction} (hG : G.IsExtremeValueDistr) :
    ∃ (A : AffineIncrEquiv) (ξ : ℝ), A • G = gevCDF ξ
```

**Verdict: equivalent.** The hypotheses are the same once `IsExtremeValueDistr` is unfolded, using
the Foundations section. For the conclusions: `A • G = gevCDF ξ` says `G (A⁻¹ x) = H_ξ x`, that is
`G y = H_ξ (A y)`. Writing `A y = (y - μ)/σ`, this is `G = EVD_cdf ξ μ σ` by `EVD_cdf_location_scale`.
Each step reverses. Hirata's `Fisher_Tippett_Gnedenko'` (`G x = EVD_cdf γ 0 1 (α * x + β)`) is the same
form as ours.

The converse, that every GEV law arises, is `isExtremeValueDistr_gevCDF` on our side and
`EVD_cdf_MDA` with `EVD_cdf_nondegenerate` on his.

No junk values enter: `σ > 0` is part of the conclusion, and `EVD_cdf` is used only there.

The proofs are different, which makes the agreement more informative. Ours goes through self-similarity
and a Cauchy equation on the affine group (`SelfSimilarCDF.lean`, after ExtremeValueProject). His
follows de Haan–Ferreira Theorem 1.1.3 through the quantile function `limit_quantile`, without a
convergence-of-types theorem.

Two things he has and we do not:

- `Fisher_Tippett_Gnedenko_MDA`: `¬ degenerate_df G ⟹ domain_of_attraction F G ⟹ ∃γ. domain_of_attraction F (EVD_cdf γ 0 1)`. Ours would need the bridge above.
- `Fisher_Tippett_Gnedenko_sample_max`: the same for i.i.d. random variables, with `indep_vars` and
  `weak_conv_m` of the laws of `(MAX i∈{..<n}. X i - b n) / a n`. Ours is about c.d.f.s only. The
  link exists (`tendsto_measureReal_normalized_blockMax_le` in `Statistics/BlockMaxima.lean`), but the
  theorem is not stated.

## Pickands–Balkema–de Haan

```isabelle
definition excess_cdf :: "(real ⇒ real) ⇒ real ⇒ real ⇒ real" where
"excess_cdf F u x = 1 - (1 - F (u + x)) / (1 - F u)"

definition x_star :: "(real ⇒ real) ⇒ real" where "x_star F = Sup {x. F x < 1}"
abbreviation bdd_support where "bdd_support F ≡ bdd_above {x. F x < 1}"
definition endpoint_filter :: "(real ⇒ real) ⇒ real filter" where
"endpoint_filter F = (if bdd_support F then at_left (x_star F) else at_top)"

theorem Pickands_Balkema_de_Haan:
  fixes F :: "real ⇒ real" and γ :: real
  assumes F: "right_continuous_mono F 0 1"
  shows "domain_of_attraction F (EVD_cdf γ 0 1)
          ⟷ (∃β. (∀u. 0 < β u) ∧
                  uniform_limit {0..} (λu x. excess_cdf F u x - GPD_cdf γ 0 (β u) x)
                    (λx. 0) (endpoint_filter F))"
```

```lean
noncomputable def excessSurvival (F : ℝ → ℝ) (u x : ℝ) : ℝ := F (u + x) / F u

def upperEndpointFilter : Filter ℝ :=
  ⨅ x ∈ {x | F x < 1}, 𝓟 (Ioi x ∩ {y | F y < 1})

theorem isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival (ξ : ℝ) :
    F.IsInMDAGEV ξ ↔ ∃ β : ℝ → ℝ, (∀ᶠ u in F.upperEndpointFilter, 0 < β u) ∧
      TendstoUniformlyOn (fun u x ↦ excessSurvival (fun y ↦ 1 - F y) u (β u * x))
        (gpdSurvivalAll ξ 1) F.upperEndpointFilter (Ici 0)
```

**Verdict: equivalent, for every `γ`.** Neither is conditional on the endpoint, neither assumes
anything of `F` beyond being a distribution function, and neither assumes a density. Step by step:

1. **Domain of attraction.** See above.
2. **Filter.** Identical. If `F < 1` everywhere: `bdd_support F` is false (`not_bdd_supportI'`), his
   filter is `at_top`, and ours is `atTop` by `upperEndpointFilter_eq_atTop`. Otherwise `F` reaches `1`:
   there is `x_F` with `F x_F = 1` and `F < 1` to its left (`exists_rightEndpoint_of_not_lt_one`,
   `F_x_star_eq_1`, `lt_x_star_iff_F_lt_1`), and both filters are the left neighbourhood filter of `x_F`
   (`upperEndpointFilter_eq_nhdsLT`; `at_left x ≡ at x within {..< x}`, the same as `𝓝[<] x`). Both are
   nontrivial (`upperEndpointFilter_neBot`, `endpoint_filter_neq_bot`), so neither statement is vacuous.
3. **Excess.** `1 - excess_cdf F u x = excessSurvival (1 - F) u x` identically, including the junk
   case: at `F u = 1` both divide by zero, giving `excess_cdf = 1` and `excessSurvival = 0`. That case
   is excluded eventually along either filter (`F_lt_1_endpoint`).
4. **Scale.** His difference with `GPD_cdf γ 0 (β u)` against ours, rescaled, is his own lemma
   `excess_uniform_scaled_iff`, using `GPD_cdf_location_scale`. For `β u > 0` the map `x ↦ β u * x` is a
   bijection of `[0, ∞)`.
5. **Tail.** `1 - GPD_cdf γ 0 1 x = gpdSurvivalAll γ 1 x` on `x ≥ 0`, as shown above.
6. **Positivity of `β`.** His `∀u`, ours `∀ᶠ u`. Only the values of `β` eventually along the filter
   matter (`excess_uniform_beta_cong`), so replace `β` by `1` where it is not positive.
7. **Uniform limit.** `uniform_limit S f l F ⟷ (∀e>0. ∀⇩F n in F. ∀x∈S. dist (f n x) (l x) < e)`
   (`uniform_limit_iff`). This is `Metric.tendstoUniformlyOn_iff`.

**Atoms.** An atom at a finite endpoint is handled the same way: the filter is still the left
neighbourhood of `x_F`, and both converses derive `F̄ u → 0` along it (`F_tendsto_1_endpoint_of_excess`;
step 1 of `Converse.lean`). Then the uniform relation fails for such `F`, as it should, since the
conditional law keeps a jump. Both libraries agree here; `Minimality/ClassicalVonMises.lean` has a
concrete example on our side.

**Explicit `β`.** Hirata has them as named one-way theorems: `Pickands_Balkema_de_Haan_pos` (`β u = γ * u`),
`_neg` (`β u = - γ * (x_star F - u)`), `_normalization` (`β u = a (1 / (1 - F u))`). Ours has the first two
as equivalences, `isInMDAFrechet_iff_tendstoUniformlyOn_excessSurvival` (`β u = u / α`) and
`isInMDAWeibull_iff_tendstoUniformlyOn_excessSurvival` (`β u = (xF - u) / α`), which are stronger. The
third occurs on our side only inside the proof of `isInMDAGEV_of_isExtendedRegularlyVarying_tailQuantile`.

**Conditional probability form.** `Pickands_Balkema_de_Haan_cond_prob` states the direct half with
`P(w in M. X w - u ≤ x | u < X w)`. Ours says so only in the docstring of `excessSurvival`. We have law
forms for Gnedenko (`DomainOfAttraction/OfMeasure.lean`) but not for this theorem.

## Regular variation: the definition

```isabelle
definition regularly_varying :: "(real ⇒ real) ⇒ real ⇒ bool" where
"regularly_varying U ρ ⟷
   U ∈ borel_measurable (restrict_space borel {0<..}) ∧
   U ` {0<..} ⊆ {0<..} ∧
   (∀x>0. ((λt. U (t * x) / U t) ⤏ x powr ρ) at_top)"
```

```lean
def IsRegularlyVarying (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < f x) ∧ ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ ρ))
```

**Verdict: different by design, and neither is wrong.**

- **Measurability.** His has it, ours does not. Ours therefore admits functions built from Hamel bases,
  for which the uniform convergence theorem fails, so every theorem of ours that needs it carries
  `Measurable f` explicitly. Algebra (`mul`, `inv`, `rpow`, the decomposition `x ^ ρ * L x`) holds without
  it. Gnedenko's theorem and the like are unaffected, since `1 - F` is monotone.
- **Positivity.** His demands `U > 0` on all of `(0, ∞)`. BGT and ours ask this only near `∞`. So the
  density of a Pareto law, `α x^{-α-1} 1_{x≥1}`, is regularly varying in ours and in BGT but not in his,
  as stated. `regularly_varying_cong` only helps if the functions agree on all of `(0, ∞)`. To apply his
  theorems, change the function on `(0, X)`.

For `f` measurable near `∞`: `f` satisfies ours iff some modification of `f` on `(0, X)` satisfies his.
Ours is the more general predicate, and it has `IsRegularlyVarying.congr` for eventual equality.

## Uniform convergence theorem

```isabelle
theorem slowly_varying_UCT:
  assumes sv:"slowly_varying L" and a: "0 < a"
  shows "uniform_limit {a..b} (λt x. L (t * x) / L t) (λx. 1) at_top"
corollary regularly_varying_UCT_interval:
  assumes sv:"regularly_varying U ρ" and a: "0 < a"
  shows "uniform_limit {a..b} (λt x. U (t * x) / U t) (λx. x powr ρ) at_top"
corollary regularly_varying_pos_UCT:
  assumes rv:"regularly_varying U ρ"
    and bdd:"⋀x. 0 < x ⟹ bounded (U ` {0<..x})"
    and ρ:"0 < ρ" and a: "0 < a"
  shows "uniform_limit {0<..a} (λt x. U (t * x) / U t) (λx. x powr ρ) at_top"
corollary regularly_varying_neg_UCT:
  assumes rv:"regularly_varying U ρ" and ρ:"ρ < 0" and a: "0 < a"
  shows "uniform_limit {a..} (λt x. U (t * x) / U t) (λx. x powr ρ) at_top"
```

```lean
theorem tendstoUniformlyOn_of_measurable (hf : IsRegularlyVarying f ρ) (hm : Measurable f)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    TendstoUniformlyOn (fun x c => f (c * x) / f x) (fun c => c ^ ρ) atTop K
```

**Verdict on compacts: equivalent by truncation.** Compact `K ⊂ (0, ∞)` lies in some `[a, b]`. For `t`
large and `x ∈ [a, b]`, `t x ≥ a t` is large, so only `f` near `∞` matters. From our hypotheses set
`U = f` on `[X, ∞)` and `1` below. From his set `f = U` on `(0, ∞)` and `0` elsewhere.

**Our hypothesis is stronger than the literature's, formally.** `Measurable f` is on all of `ℝ`; his is
on `(0, ∞)`, and BGT's on some `[X, ∞)`. So ours cannot be applied directly to a function that is only
measurable near `∞`. The truncation is easy but not stated.

**Our statement is weaker than the theorem we cite.** The docstring cites [BGT, Theorem 1.5.2]. From
memory, that theorem also contains the two extra ranges of Hirata's `regularly_varying_pos_UCT` and
`regularly_varying_neg_UCT`. Ours has only compacts. Ours also has a monotone variant,
`tendstoUniformlyOn_of_isCompact`. On his side this is covered by the general theorem, since monotone functions are
measurable.

## Karamata's representation theorem

```isabelle
lemma Karamata_representation_ex:
  assumes rv:"regularly_varying U ρ"
  shows "∃A>0. ∃c r C.
              (∀x ≥ A. U x = c x * exp (∫t∈{A<..x}. r t / t ∂lborel))
            ∧ (∀x ≥ A. set_integrable lborel {A<..x} (λt. r t / t))
            ∧ r ∈ borel_measurable borel
            ∧ (r ⤏ ρ) at_top
            ∧ bounded (r ` {A..})
            ∧ c ∈ borel_measurable borel
            ∧ (∀x. 0 < c x)
            ∧ (c ⤏ C) at_top
            ∧ 0 < C"
lemma Karamata_representation_iff:
  assumes U_meas:"U ∈ borel_measurable (restrict_space borel {0<..})"
    and U_pos:"⋀x. 0 < x ⟹ 0 < U x"
  shows "regularly_varying U ρ ⟷ (∃A>0. ∃c r C. ... (r ⤏ ρ) at_top ∧ (c ⤏ C) at_top ∧ 0 < C)"
```

```lean
theorem isSlowlyVarying_iff_exists_representation (hm : Measurable L) :
    IsSlowlyVarying L ↔ ∃ a : ℝ, 0 < a ∧ ∃ c ε : ℝ → ℝ, Measurable c ∧ Measurable ε ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ Tendsto c atTop (𝓝 c₀)) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ x ≥ a, IntervalIntegrable (fun t => ε t / t) volume a x) ∧
      ∀ x ≥ a, L x = c x * exp (∫ t in a..x, ε t / t)
```

**Verdict.** At `ρ = 0` the two agree, using `∫ t in a..x = ∫ t in Ioc a x` for `a ≤ x`. In both,
integrability is explicit, so the integral is not junk.

- Ours states only `ρ = 0`. His states every `ρ`, with `r → ρ`. Ours follows by applying
  `isRegularlyVarying_iff_exists_isSlowlyVarying`, but is not stated.
- His adds `r` bounded on `[A, ∞)` and `c > 0` everywhere. Ours has these only after moving `a`.
- Ours has `IsSlowlyVarying.of_representation` for arbitrary, possibly nonmeasurable `L`, `c`, `ε`, which
  is slightly stronger than his `⟸`.

An artefact on his side: `Karamata_representation_ex_total` says `∀x. U x = c x * exp (∫t∈{0<..x}. ...)`
for all real `x`. For `x ≤ 0` the set is empty, so `c x = U x` there. This is harmless, since `U` carries
no information on `x ≤ 0`, but the quantifier reads as more than it is. Its `∀x y` also has an unused `x`.

## Karamata's theorem

**Tail integrals, `ρ < -1`.**

```isabelle
lemma
  assumes rv: "regularly_varying U ρ" and ρ:"ρ < - 1"
  shows Karamata_theorem_half2:"((λt. (∫x∈{t<..}. U x ∂lborel) / (t * U t)) ⤏ - 1 / (ρ + 1)) at_top"
    and regularly_varying_tail_integrable:"∃T>0. set_integrable lborel {T<..} U"
```

```lean
theorem tendsto_integral_Ioi_div_of_measurable {F : ℝ → ℝ} {α : ℝ} (hm : Measurable F)
    (hRV : IsRegularlyVarying F (-α)) (hα : 1 < α) :
    Tendsto (fun x => (∫ t in Ioi x, F t) / (x * F x)) atTop (𝓝 (1 / (α - 1)))

theorem tendsto_integral_Ioi_div (hF : Antitone F) (hRV : IsRegularlyVarying F (-α))
    (hα : 1 < α) :
    Tendsto (fun x => (∫ t in Ioi x, F t) / (x * F x)) atTop (𝓝 (1 / (α - 1)))
```

**Verdict: equivalent by truncation**, with `ρ = -α`, `-1/(ρ+1) = 1/(α-1)`. Non-integrable integrands
give `0` in both provers, but the limit is nonzero, so the integrals are genuine eventually in both. The
antitone form is a special case: antitone implies measurable, and `pos_of_antitone` gives positivity
everywhere. He states integrability explicitly. Ours states it only for antitone `F`
(`integrableOn_Ioi`). In the measurable case it follows from the conclusion, but is not stated.

**`∫_a^t`, `ρ > -1`.**

```isabelle
lemma Karamata_theorem_half1:
  assumes rv: "regularly_varying U ρ"
    and a: "0 ≤ a" and ρ:"- 1 < ρ"
    and integrable:"⋀c d. a ≤ c ⟹ set_integrable lborel {c<..d} U"
  shows "((λt. (∫x∈{a<..t}. U x ∂lborel) / (t * U t)) ⤏ 1 / (ρ + 1)) at_top"
lemma Karamata_theorem_half1_ex:
  assumes rv: "regularly_varying U ρ" and ρ:"- 1 ≤ ρ"
  shows "∃a. ((λt. (t * U t) / (∫x∈{a<..t}. U x ∂lborel)) ⤏ ρ + 1) at_top"
```

```lean
theorem tendsto_integral_zero_div {f : ℝ → ℝ} {ρ : ℝ} (hf : IsRegularlyVarying f ρ)
    (hm : Measurable f) (hρ : -1 < ρ) (hint : ∀ x, IntervalIntegrable f volume 0 x) :
    Tendsto (fun x => (∫ t in (0 : ℝ)..x, f t) / (x * f x)) atTop (𝓝 (1 / (ρ + 1)))
```

**Verdict: ours is weaker, in two ways.**

1. The lower limit is fixed at `0`, so `f` must be integrable near `0`. Take `f t = t⁻²` on `(0, 1]`,
   `f t = 1` on `(1, ∞)`: it is regularly varying of index `0`, and the theorem does not apply.
2. `hint` quantifies over all real `x`, so it also demands integrability on `[x, 0]` for negative `x`.
   The conclusion says nothing about negative arguments. The docstring says "integrable on every `[0, x]`",
   which reads as `x ≥ 0`; the hypothesis says more.

Truncation recovers the general case, as `f · 1_{[X, ∞)}` differs by a constant in the integral. But the
reader must do this, and the literature's form (BGT Proposition 1.5.8, starting from `X`) is his, not ours.
`Karamata_theorem_half1_ex` needs no integrability hypothesis at all, because the UCT provides it.

**`ρ = -1`.** He has `Karamata_theorem_half_uminus1` (`∫_a^t U / (t U t) → ∞`) and
`Karamata_theorem_half_uminus2_at_top` (`∫_t^∞ U / (t U t) → ∞` if integrable), for all `U`. Ours has only
the second, for antitone `F`: `tendsto_integral_Ioi_div_atTop_of_neg_one`. We did not find the first.

**Converse.**

```isabelle
lemma
  assumes U_pos:"⋀r. 0 < r ⟹ 0 < U r"
    and U_meas:"U ∈ borel_measurable (restrict_space borel {0<..})"
    and ρ:"- 1 > ρ"
    and lim: "((λt. t * U t / (∫x∈{t<..}. U x ∂lborel)) ⤏ - (ρ + 1)) at_top"
  shows Karamata_theorem_converse2:"regularly_varying U ρ"
    and Karamata_theorem_converse2_itegrable: "∃a>0. set_integrable lborel {a..} U"
```

and `Karamata_theorem_converse1` for `ρ > -1` with `∫_{a<..t}`.

```lean
theorem of_tendsto_mul_div_integral_Ioi {F : ℝ → ℝ} {α a : ℝ} (hF : Antitone F)
    (hint : IntegrableOn F (Ioi a)) (hα : 1 < α)
    (h : Tendsto (fun x => x * F x / ∫ t in Ioi x, F t) atTop (𝓝 (α - 1))) :
    IsRegularlyVarying F (-α)
```

**Verdict: ours is weaker.** It assumes `Antitone F` and integrability; he assumes neither, and also
treats `ρ > -1`. `FAITHFULNESS.md` already records the antitone restriction against BGT Theorem 1.6.1.
No integrability hypothesis is needed in such a statement, and this is our reading, not taken from his proof: a
non-integrable integrand gives integral `0`, then `t U t / 0 = 0`, which contradicts the limit being nonzero.

**Consequences he states and we do not:** `regularly_varying_integral`, `regularly_varying_tail_integral`
(integrals of regularly varying functions are regularly varying, including `ρ = -1`),
`regularly_varying_integral_limit`, `regularly_varying_integral_infinity`.

## Other results stated in both

**Potter bounds. Equivalent.** Hirata's `Potter_bounds`
(`U y / U x ≤ A * max ((y/x) powr (ρ+d)) ((y/x) powr (ρ-d))` for `x, y ≥ T`) and `Potter_bounds_lower`
(with `A < 1`) are our `potter_bounds_of_measurable` (with `A > 1`, `A⁻¹`). His one-sided
`Potter_bounds1`, `_bounds2` are the same, since the `max` is attained by the `ρ+d` term when `y ≥ x`.

**Gnedenko's conditions. Equivalent.** `MDA_regularly_varying_pos` has `(∀x. F x < 1) ∧ regularly_varying
(λx. 1 - F x) (-1/γ)`, and ours `IsRegularlyVarying (fun x ↦ 1 - F x) (-α)`. The extra conjunct follows from
monotonicity. `MDA_regularly_varying_neg` has `bdd_support F ∧ regularly_varying (λs. 1 - F (x_star F - 1/s)) (1/γ)`,
and ours `isInMDAWeibull_iff` the same with `xF` explicit. Monotone functions are measurable, so the
measurability difference does not matter here.

**Quantile form. Equivalent.** `MDA_iff_tail_quantile'` against
`isInMDAGEV_iff_exists_isExtendedRegularlyVarying_tailQuantile`.
`tail_quantile F t = Inf {x. 1 - 1/t ≤ F x}` and `tailQuantile t = sInf {y | 1 - F y ≤ 1 / t}` are the same set.
`boxCox` matches his limit. Junk values at `t ≤ 1` (infimum of an unbounded set) do not matter, since
the limit is along `at_top`.

**von Mises conditions. Neither contains the other.**

| | Hirata | This library |
|---|---|---|
| General `γ`, second order | `von_Mises_condition`: `(1 - F) f' / f² → -γ - 1`, with `f'` continuous, `f > 0`, `F → 1` at the endpoint | none |
| `γ = 0` | the above | `isInMDAGumbel_of_vonMises`, `_nhdsLT`: `F''` need not be continuous |
| `γ > 0`, first order | `von_Mises_condition_pos`: `f` continuous, `f > 0`, unbounded support | `isInMDAFrechet_of_vonMises`: only differentiable; positivity and the support follow |
| `γ < 0`, first order | `von_Mises_condition_neg`: `f` continuous, `f > 0`, `x0 < x_star F`, bounded support assumed | `isInMDAWeibull_of_vonMises`: only differentiable; that `xF` is the endpoint is derived |

Ours are stronger where they overlap, and `ClassicalVonMises.lean` shows the condition `F → 1` cannot be
dropped. He has the single statement, and the explicit constants `von_Mises_normalization`.

Citations differ. He cites de Haan–Ferreira 1.1.8 for the general condition, 1.1.11 for `γ > 0`, 1.1.13 for
`γ < 0`. Our `DomainOfAttraction/VonMises.lean` cites 1.1.8 for the Fréchet and Weibull conditions. Check against
the book.

**Threshold stability. Equivalent.** `excess_cdf_GPD` against `gpdSurvivalAll_add`. **Max-stability.**
`EVD_cdf_max_stable` against `gevFun_pow_apply`, `isMaxStable_gevCDF`.

**Examples.** Both place Pareto-type, uniform and exponential laws, with consistent indices: Hirata's
`uniform_MDA` at `γ = -1`, ours `isInMDAGEV_powerCDF` at `ξ = -1/α`; his `GPD_cdf_MDA` at `γ = 0`, `γ = 1`
agrees with `isInMDAGEV_standardExponentialCDF` and `isInMDAGEV_paretoCDF`. This is a small independent
check of the sign. **He also has** `std_normal_MDA`, `normal_MDA`, `std_normal_normalization`, `erlang_MDA`,
`erlang_normalization`, `std_Cauchy_MDA`, `Cauchy_MDA`, `std_Cauchy_normalization`. We did not find these on
our side. Our normal-law results concern the central limit domain, not maxima.

**He has, and we did not find:**

- `MDA_iff_tail_probability'`, `MDA_iff_divide_tail`: the other equivalents of de Haan–Ferreira 1.1.2 and 1.1.6 as
  stated equivalences for every `γ`. We have the Gumbel case (`isInMDAGumbel_iff`) and the forward extension to
  negative `x` (`tendsto_div_tail_of_tendstoUniformlyOn_excessSurvival`).
- `MDA_canonical_normalization`, `MDA_normalization_pos`, `MDA_normalization_neg`, `MDA_normalization_zero_spacing`:
  canonical constants, as in de Haan–Ferreira Corollary 1.2.4, the last with no auxiliary function at `γ = 0`.
- `normalizing_ratio1`, `normalizing_ratio2`: `a (n+1) / a n → 1`, `(b (n+1) - b n) / a n → 0`.
- `divide_limit_imp_regularly_varying`: if `U (t x) / U t` converges for every `x`, the limit is a power.
  `regularly_varying_sequentialy`: the sequential criterion for monotone `U`. Ours cites BGT 1.4.1 for the decomposition
  only.
- `regularly_varying_compose`: composition, index `ρ η`.
- `regularly_varying_pos_at_top`, `regularly_varying_neg_at_top`: `ρ > 0` gives `U → ∞`, `ρ < 0` gives `U → 0`. Ours has
  this for antitone `g` only (`Weibull.tendsto_zero_of_isRegularlyVarying`).

**We have, and he does not:** the rest of the library. Within the same subject: a convergence of types theorem
(`SelfSimilarCDF.lean`), extended regular variation as a named notion (`IsExtendedRegularlyVarying`),
second-order regular variation, Breiman's lemma and multivariate regular variation, the counterexamples in
`Minimality/`, and uniqueness of the normalizing map (`unique_orientationPreservingAffineEquiv_smul_eq_not_isDegenerate`).
His development has no estimators, no dependence and no multivariate results.

**Neither has:** a statement that `ξ` is unique, `MDA(H_ξ) ∩ MDA(H_ξ') ≠ ∅ → ξ = ξ'`. It is a short consequence of
convergence of types, or of comparing `boxCox` at two points. (The parameters of the law itself are identified in
ours: `gev_params_eq_of_measure_eq`.)

## Differences that suggest a problem or an improvement in our library

In order of value. None of these is an error in a statement.

1. **Prove `F.IsInMDAGEV ξ ↔ ∃ As, ∀ x, Tendsto (fun n ↦ ((As n • F) x) ^ n) atTop (𝓝 (gevCDF ξ x))`.** This is the only
   gap in the chain from our Pickands–Balkema–de Haan theorem to the textbook statement. It takes a few lines from
   `mkOfCoefs_smul_gevCDF_of_pos` and `_of_neg`. With it, state the analogue of `Fisher_Tippett_Gnedenko_MDA`: a nondegenerate
   limit means `∃ ξ, F.IsInMDAGEV ξ`.
2. **Generalize `tendsto_integral_zero_div`.** Arbitrary lower limit, and integrability only on `[a, x]` with `x ≥ a`. Better, an
   existential form with no integrability hypothesis, like `Karamata_theorem_half1_ex`. The present `∀ x` over negative `x` is
   an artefact.
3. **Remove `Antitone` from `of_tendsto_mul_div_integral_Ioi`, and add the `ρ > -1` converse** (BGT Theorem 1.6.1, in full). He shows
   that only positivity and measurability are needed.
4. **Add the tails of the UCT:** `[a, ∞)` for `ρ < 0`, `(0, a]` for `ρ > 0` with local boundedness. These are in the theorem the docstring
   cites, and the docstring should say it proves only the compact part until then.
5. **State the `ρ = -1` Karamata results without monotonicity**, including `∫_a^t` (BGT Proposition 1.5.9a), and state that integrals of
   regularly varying functions are regularly varying.
6. **Weaken `Measurable f` to measurability near `∞`** in `tendstoUniformlyOn_of_measurable`, the Potter bounds, the representation theorem
   and Karamata, or add `of_measurableOn` wrappers. BGT's hypothesis is on `[X, ∞)`.
7. **State the representation theorem for index `ρ`** (`r → ρ`), a direct corollary, with `ε` bounded on `[a, ∞)`.
8. **Add random-variable forms:** Fisher–Tippett–Gnedenko for i.i.d. sample maxima and Pickands–Balkema–de Haan for conditional
   probabilities. They are what a user expects to read, and both follow easily.
9. **Add standard examples:** the normal law in `MDA(H_0)` with its explicit constants, Gamma or Erlang, and Cauchy. The normal case is the
   most commonly cited example in the subject and we do not have it. The Cauchy case follows from `isInMDAFrechet_of_vonMises`.
10. **Add canonical norming constants** for every `γ`, including de Haan–Ferreira Corollary 1.2.4, and the stated equivalences `MDA_iff_divide_tail`,
    `MDA_iff_tail_probability'`.
11. **Add the unified von Mises condition** for all `γ`, using our weaker hypotheses where possible.
12. **Add to `RegularVariation/Basic.lean`:** composition; the limit-is-a-power theorem; `ρ > 0` gives `f → ∞`, `ρ < 0` gives `f → 0`, without monotonicity.
13. **Add uniqueness of `ξ`.**
14. **Rename the bound variable `ξ` to `α`** in `classification`. It is the tail index, and `ξ` means the shape everywhere else.
15. **Check two citations against the books:** de Haan–Ferreira 1.1.8 in `DomainOfAttraction/VonMises.lean`, and BGT 1.4.1 and 1.5.2 where our theorem covers only part of what is cited.
