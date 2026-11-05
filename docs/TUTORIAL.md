# Your first extreme value theory proof in Lean

This tutorial is for a reader who knows Lean basics and extreme value theory. It walks through one
example, [`Examples/Tutorial.lean`](../Examples/Tutorial.lean), which the build checks with
`lake build Examples`. Keep that file open beside this one. It imports only `ExtremeValueTheory`, as your
own project would.

We take the law with tail `F̄(x) = (1 + x)⁻²` on `[0, ∞)`, a Lomax law. The library has no name for it, so
every step is visible. We show that it is in the Fréchet domain `MDA(Φ₂)` and that the Hill estimator of
an iid sample from it converges in probability to `1/2`.

To check the file as you read:

```sh
lake exe cache get
lake build Examples.Tutorial
```

## Step 1: define the law

The classical theory of maxima works with `CumulativeDistributionFunction`, a Stieltjes function with
limits `0` and `1` (see "One representation of laws" in [`DESIGN.md`](DESIGN.md)). To build one, give the
function and four proofs: `mono'`, `right_continuous'`, `tendsto_atTop` and `tendsto_atBot`.

```lean
noncomputable def lomaxCDF : CumulativeDistributionFunction where
  toFun x := 1 - (1 + max x 0) ^ (-2 : ℝ)
  ...
```

Writing `max x 0` gives one formula on all of `ℝ`, which keeps the monotonicity and continuity proofs
short. The library's `paretoCDF` is built the same way. The lemma `one_sub_lomaxCDF` then gives the tail
in the form used afterwards: `1 - F x = (1 + x) ^ (-2)` for `x ≥ 0`.

Lean's `rpow` is total, so `x ^ (-2 : ℝ)` makes sense at `x = 0` and for negative `x` as well, with values
you may not want. Evaluation lemmas should therefore state the range of `x` they hold on.

## Step 2: regular variation of the tail

`IsRegularlyVarying f ρ` says that `f` is eventually positive and that `f (c * x) / f x → c ^ ρ` for every
`c > 0`. You can prove it from the definition, but the algebra is usually quicker:

- `IsRegularlyVarying.rpow_id ρ`: `x ^ ρ` has index `ρ`.
- `IsRegularlyVarying.of_tendsto_div`: if `f / g → L > 0` and `g` has index `ρ`, so does `f`.
- `IsRegularlyVarying.rpow`: raising to the power `r` multiplies the index by `r`.
- `IsRegularlyVarying.congr`: the property depends only on `f` near `+∞`.

`isRegularlyVarying_one_add` shows that `1 + x` has index `1`, since `(1 + x) / x → 1`. Then
`isRegularlyVarying_tail` raises it to the power `-2` and uses `congr` to replace `(1 + x) ^ (-2)` by
`1 - F x`, which is valid for `x ≥ 0`.

## Step 3: Gnedenko's theorem

`isInMDAFrechet_iff` is the equivalence: `F` is in the Fréchet domain of `Φ_α` if and only if `1 - F` is
regularly varying with index `-α`.

```lean
theorem isInMDAFrechet_lomaxCDF : lomaxCDF.IsInMDAFrechet (two_pos : (0 : ℝ) < 2) :=
  (lomaxCDF.isInMDAFrechet_iff two_pos).2 isRegularlyVarying_tail
```

The proof of `0 < 2` appears in the statement because `standardFrechetCDF` takes it as an argument.

The `example` after the theorem unfolds the definition: there exist affine maps `As n` with
`(As n • F)(x) ^ n → Φ₂(x)` for every `x`. Gnedenko's theorem gives their existence and no formula. For
this law you would still have to compute norming constants yourself. The library has explicit ones for
Pareto, power and exponential laws (`tendsto_paretoCDF_pow`, `tendsto_powerCDF_pow`,
`tendsto_standardExponentialCDF_pow`).

A second `example` moves to the GEV scale with `IsInMDAFrechet.isInMDAGEV`: `ξ = 1/α = 1/2`. That is the
form the peaks-over-threshold theorem takes
(`isInMDAGEV_iff_exists_tendstoUniformlyOn_excessSurvival`); see
[`Examples/StandardLaws.lean`](../Examples/StandardLaws.lean).

## Step 4: the Hill estimator

Statistical theorems take a sample as `X : ℕ → Ω → ℝ`. The estimator on the first `n` observations is
`hill (fun i : Fin n ↦ X i ω) (k n)`.

```lean
theorem tendstoInMeasure_hill_lomax {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) lomaxCDF.measure P) (hindep : iIndepFun X P) :
    TendstoInMeasure P (fun n ω ↦ hill (fun i : Fin n ↦ X i ω) (Nat.sqrt n)) atTop
      (fun _ ↦ 1 / 2)
```

Three things happen in the proof:

- `F.measure` is the law of `F`, and `HasLaw` is Mathlib's way of saying a random variable has that law.
- `tendstoInMeasure_hill_of_hasLaw` needs regular variation of `x ↦ μ.real (Ioi x)`. The simp lemma
  `measureReal_Ioi` turns this into `1 - F x`, which is step 2.
- `k n = Nat.sqrt n` satisfies `k → ∞` and `k / n → 0`, by `tendsto_sqrt_atTop` and `tendsto_sqrt_div`.

## Is the theorem vacuous?

A theorem about samples says nothing if no sample satisfies its hypotheses.
`exists_sample_tendstoInMeasure_hill_lomax` builds one with Mathlib's `exists_iid`, so the hypotheses can
all be met at once.

## What this does and does not say

The theorem says that for an iid sample of exactly this law, and for `k n = ⌊√n⌋`, the probability that the
Hill estimator is further than any fixed `ε` from `1/2` tends to `0`.

It gives no rate and no statement about a finite `n`. It says nothing about whether `⌊√n⌋` is a good choice
of `k`, or about dependent data. See the README's Limitations section for the library as a whole.

## Where to go next

- [`Examples/StandardLaws.lean`](../Examples/StandardLaws.lean): the same theorems for the standard laws.
- [`Examples/Applications/`](../Examples/Applications): a return level, a reinsurance layer and a tail index,
  each ending in one checked statement.
- [`FINDING_RESULTS.md`](FINDING_RESULTS.md): how to find a result in the library.
