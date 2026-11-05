# Issue labels

Give each issue one label from each group below, where the group applies.

| Group | Label | Use for |
|---|---|---|
| Area | `area:classical` | maxima, types, GEV, max-stability, regular variation, domains of attraction |
| | `area:pot` | peaks over threshold, the generalized Pareto law |
| | `area:statistics` | estimators, likelihood, return levels, intervals |
| | `area:dependence` | stationary sequences, extremal index, tail process, mixing |
| | `area:multivariate` | multivariate regular variation, max-stable vectors, tail dependence |
| | `area:processes` | point processes, Skorokhod space, max-stable processes |
| | `area:heavy-tails` | subexponential laws, stable laws, ruin |
| | `area:formathlib` | `ForMathlib/` and upstreaming |
| | `area:docs` | Markdown documentation, docstrings, the blueprint |
| | `area:tooling` | scripts and CI |
| Type | `type:proof` | a new Lean result or test |
| | `type:refactor` | same mathematics, better code |
| | `type:docs` | documentation only |
| | `type:tooling` | scripts and CI |
| | `type:research` | the mathematics is not settled |
| Difficulty | `difficulty:small` | an afternoon, for someone who knows some Lean |
| | `difficulty:medium` | days; a proof plan is in the issue |
| | `difficulty:hard` | weeks, or genuinely open |
| Status | `status:ready` | can start now |
| | `status:blocked-upstream` | needs mathematics Mathlib lacks |
| | `status:research` | needs mathematical work before any Lean |
| Entry points | `good first issue` | a newcomer can start from the issue alone |
| | `open-problem` | a sourced problem from the surveys, numbered `EVT-OP-…`; kept after it is solved |

Draft issues are in `.github/issue-drafts/`: the first line of each file is `Title: …`, the second
`Labels: …`, and the rest is the body.

## Creating the labels

Run once, from the repository, with an authenticated `gh`. `--force` updates a label that already exists.

```sh
gh label create "area:classical" --color 1d76db --description "Maxima, types, GEV, regular variation, domains of attraction" --force
gh label create "area:pot" --color 1d76db --description "Peaks over threshold, generalized Pareto" --force
gh label create "area:statistics" --color 1d76db --description "Estimators, likelihood, return levels, intervals" --force
gh label create "area:dependence" --color 1d76db --description "Stationary sequences, extremal index, tail process, mixing" --force
gh label create "area:multivariate" --color 1d76db --description "Multivariate regular variation, max-stable vectors" --force
gh label create "area:processes" --color 1d76db --description "Point processes, Skorokhod space, max-stable processes" --force
gh label create "area:heavy-tails" --color 1d76db --description "Subexponential laws, stable laws, ruin" --force
gh label create "area:formathlib" --color 1d76db --description "ForMathlib and upstreaming" --force
gh label create "area:docs" --color 1d76db --description "Documentation, docstrings, blueprint" --force
gh label create "area:tooling" --color 1d76db --description "Scripts and CI" --force
gh label create "type:proof" --color 5319e7 --description "A new Lean result or test" --force
gh label create "type:refactor" --color 5319e7 --description "Same mathematics, better code" --force
gh label create "type:docs" --color 5319e7 --description "Documentation only" --force
gh label create "type:tooling" --color 5319e7 --description "Scripts and CI" --force
gh label create "type:research" --color 5319e7 --description "The mathematics is not settled" --force
gh label create "difficulty:small" --color 0e8a16 --description "An afternoon, with some Lean" --force
gh label create "difficulty:medium" --color fbca04 --description "Days; a proof plan is in the issue" --force
gh label create "difficulty:hard" --color b60205 --description "Weeks, or genuinely open" --force
gh label create "status:ready" --color 0e8a16 --description "Can start now" --force
gh label create "status:blocked-upstream" --color b60205 --description "Needs mathematics Mathlib lacks" --force
gh label create "status:research" --color fbca04 --description "Needs mathematical work before any Lean" --force
gh label create "open-problem" --color d93f0b --description "A sourced research problem, EVT-OP-..." --force
gh label create "good first issue" --color 7057ff --description "A newcomer can start from the issue alone" --force
```
