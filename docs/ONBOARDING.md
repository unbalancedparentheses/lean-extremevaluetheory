# From clone to merged pull request

This walks through one real contribution: two known-answer tests for L-moments, which are now in
`Test/KnownAnswers/Statistics.lean`. You will not repeat them; do the same steps for an issue labelled
`good first issue`. Some Lean is assumed. Docstrings and documentation issues need very little.

## 1. Set up

Install [elan](https://github.com/leanprover/elan), and on GitHub fork the repository. Then:

```sh
gh repo fork unbalancedparentheses/lean-extremevaluetheory --clone
cd lean-extremevaluetheory
lake exe cache get
lake build
```

`cache get` fetches the prebuilt Mathlib. `lake build` compiles this library, once; later builds only redo what
changed. If something fails, see [`TROUBLESHOOTING.md`](TROUBLESHOOTING.md).

For editing, use VS Code with the Lean 4 extension and open the repository root.

## 2. Pick a task and find what exists

The task: nothing in `Test/` checked the L-moments, so a slip in their definition would go unnoticed. Hosking
(1990) gives known values: the L-skewness is `1/3` for the exponential law and `0` for the uniform law.

Search before writing anything:

```sh
grep -rn "lSkewness" Test                                    # no tests yet
grep -n "theorem lSkewness" ExtremeValueTheory/Statistics/LMoments.lean
```

The second search finds the closed form for the generalized Pareto law, which contains both laws
(`GPD(0, 1)` is exponential, `GPD(-1, 1)` is uniform):

```lean
theorem lSkewness_gpdMeasure (hσ : 0 < σ) (hξ : ξ < 1) :
    lSkewness (gpdMeasure ξ σ) = (1 + ξ) / (3 - ξ)
```

## 3. Make a branch and write the change

```sh
git switch -c test-lskewness
```

Known-answer tests go in `Test/KnownAnswers/`, as described in [`DESIGN.md`](DESIGN.md). Each is a `theorem test_…`
with a docstring citing the value. A one-line application of a library lemma is fine: what is tested is that the
lemma's statement has the textbook value.

```lean
/-- The L-skewness of the exponential law, `GPD(0, 1)`, is `τ₃ = 1/3` (Hosking, *L-moments*,
JRSS B 52 (1990)). -/
theorem test_lSkewness_exponential : lSkewness (gpdMeasure 0 1) = 1 / 3 := by
  rw [lSkewness_gpdMeasure one_pos (by norm_num)]
  norm_num
```

Check that one file, which is much faster than a full build:

```sh
lake env lean Test/KnownAnswers/Statistics.lean
```

No output, or only warnings, means it passed. Warnings about `module` imports are expected.

## 4. Run the checks

```sh
lake build
lake build Test
python3 scripts/check_source.py
```

`lake build Test` ends with the axiom audit, which should report only `Quot.sound`, `Classical.choice` and
`propext`. If you added a library file, it must be imported from `ExtremeValueTheory.lean`, and
`check_source.py` fails if it is not.

## 5. Credit yourself

In your first pull request, add yourself to the Acknowledgements section of the README. In a new file, put your
name on the `Copyright` and `Authors:` lines. See [Credit](../CONTRIBUTING.md#credit).

## 6. Commit and open the pull request

Add the files you changed by name:

```sh
git add Test/KnownAnswers/Statistics.lean README.md
git commit -m "Known answers: the L-skewness of the exponential and uniform laws"
git push -u origin HEAD
gh pr create --fill
```

Fill in the template: link the issue, name the source, and say how the statement differs from it.

## 7. Review and merge

CI runs the checks from step 4. A reviewer will compare the statement and docstring with the source, and that is
usually where the discussion is. Push further commits to the same branch to answer. The pull request is merged
with a merge commit, so your commits reach `main` as you wrote them.
