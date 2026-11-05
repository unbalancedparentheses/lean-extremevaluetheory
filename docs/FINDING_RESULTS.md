# How to find a result

The library has more than 4,000 theorems. There are four places to look, and they answer different
questions.

| You have | Look in | What you get |
|---|---|---|
| a topic or a textbook theorem | [`THEOREMS.md`](../THEOREMS.md) | a catalogue by topic, with the main Lean names |
| a theorem and you want its proof structure | the [blueprint](https://unbalancedparentheses.github.io/lean-extremevaluetheory/blueprint/) | mathematical statements, proof sketches, a dependency graph, and the Lean names |
| a Lean name or part of one | the [API documentation](https://unbalancedparentheses.github.io/lean-extremevaluetheory/docs/) | the exact statement, the docstring and the file; the search box matches names |
| a guess at the name | the conventions below, and `grep` | the declaration in the source |

`THEOREMS.md` lists the main results and can lag behind the code, so a name missing from it does not mean
the result is missing. The source is the final word. To compare a statement with its textbook form, see
[`FAITHFULNESS.md`](../FAITHFULNESS.md); for R and Python functions, see
[`PRACTITIONERS.md`](PRACTITIONERS.md). For what the library leaves out, see the README's Limitations
section.

## Guessing a name

[`DESIGN.md`](DESIGN.md) has the full conventions. These are the ones that help most when searching:

- **Domains of attraction** are `IsInMDAFrechet`, `IsInMDAWeibull`, `IsInMDAGumbel` and the unified
  `IsInMDAGEV ξ`. Membership of a named law is `isInMDA…_<law>`, as in `isInMDAGEV_paretoCDF`. For a law
  given as a measure, `ofMeasure` appears in the name, as in `isInMDAGEV_ofMeasure_gpdMeasure`.
- **Named laws**: a c.d.f. is `<name>CDF`, a measure is `<name>Measure`.
- **Predicates** are `Is…`, and facts about them use dot notation: `IsRegularlyVarying.index_eq`.
- **Limits** follow Mathlib: `tendstoInMeasure_…` for convergence in probability, and
  `tendstoInDistribution_…` for convergence in distribution, followed by the estimator
  (`tendstoInMeasure_hill`).
- **Namespaces**: the c.d.f. API is in `CumulativeDistributionFunction`, everything else in
  `ExtremeValueTheory`.

## Worked search 1: is the Cauchy law in the Fréchet domain?

*By the naming conventions.* Membership of a law is `isInMDA…_<law>`, so search the source for it:

```sh
grep -rnE "theorem isInMDA.*[cC]auchy" ExtremeValueTheory
```

This finds `isInMDAFrechet_ofMeasure_cauchyMeasure` in `DomainOfAttraction/NamedLaws.lean`. A narrower
pattern with one underscore misses it, because a law given as a measure has `_ofMeasure_` in its name. Check
what it says:

```lean
import ExtremeValueTheory
open CumulativeDistributionFunction
#check @isInMDAFrechet_ofMeasure_cauchyMeasure
```

`Examples/StandardLaws.lean` uses it as `cauchy_domain`.

## Worked search 2: what is the limit law of the Hill estimator?

*By the catalogue.* Search `THEOREMS.md`:

```sh
grep -n "Hill estimator" THEOREMS.md
```

The entry "Hill estimator asymptotic normality" names `tendstoInDistribution_hill`: under second-order
regular variation with `√k A(n/k) → λ`, `√k(γ̂ − γ) ⇒ N(λ/(1−ρ), γ²)`. It also names the exact Pareto case
`tendstoInDistribution_hill_pareto`, used in `Examples/Applications/HillTailIndex.lean`.

To see how this compares with the textbook, search `FAITHFULNESS.md` for the name; its row cites
de Haan and Ferreira, Theorem 3.2.5.

## Worked search 3: Karamata's theorem without monotonicity

*By the blueprint.* The blueprint has a chapter called "Karamata's theorem". Its source is
`blueprint/src/sections/karamata.tex`, so you can search it directly:

```sh
grep -n "lean{" blueprint/src/sections/karamata.tex
```

The theorem "Karamata's theorem, relaxed hypotheses" (`thm:karamata-relaxed`) is for every measurable
`F`, and names `ExtremeValueTheory.IsRegularlyVarying.tendsto_integral_Ioi_div_of_measurable`.

*Then the API documentation.* Search that name there for the exact statement. It is on the page
[`ExtremeValueTheory/RegularVariation/KaramataConverse.html`](https://unbalancedparentheses.github.io/lean-extremevaluetheory/docs/ExtremeValueTheory/RegularVariation/KaramataConverse.html).
The published documentation follows the last deployment, so a very recent result may not be there yet.

## When a search finds nothing

Do not conclude too quickly in either direction. Two cases, both checked:

- **In the source but not in the catalogue.** `grep -n "gpdReturnLevelInterval" THEOREMS.md` finds nothing,
  yet the interval for a peaks-over-threshold return level exists:
  `tendsto_measure_mem_gpdReturnLevelInterval` in `Statistics/ConfidenceIntervals.lean`, and the blueprint
  has it under "Return levels and confidence intervals".
- **Really not proved.** `grep -rn "theorem tendstoInDistribution_pickands" ExtremeValueTheory` finds nothing,
  and the README's Limitations section confirms it: normality of the Pickands and moment estimators is not
  proved.

If you need a lemma while writing a proof, Mathlib's `exact?` also searches this library once it is
imported. Remove it before committing, since `scripts/check_source.py` rejects search tactics.
