# Specification tests

Lean checks that every proof is correct. It cannot check that a theorem *states* what the
literature states. The files here are tests of the statements and definitions themselves. They are
built in CI (`lake build Test`), so any change that breaks one fails the build.

| Kind | What it catches | Files |
|---|---|---|
| **Non-vacuity** | Hypotheses that can never hold together, so the theorem says nothing. Each test builds a concrete object (a distribution, a sequence, a process) satisfying all hypotheses of a headline theorem and applies the theorem to it. | `Test/NonVacuity/*.lean` |
| **Known answers** | Sign, parametrization and normalization slips in definitions. Each test checks a definition on a case with a textbook answer (the Gumbel CDF at 0 is `e⁻¹`, the extremal index of an iid sequence is 1, …). | `Test/KnownAnswers/*.lean` |
| **Junk values** | Statements that are true only because of Lean's conventions (`x / 0 = 0`, `log 0 = 0`, truncated subtraction, `∞ * 0 = 0`). | `Test/JunkValues.lean`, report in [`JUNK_VALUES.md`](JUNK_VALUES.md) |
| **Negative tests** | Hypotheses so strong that the theorem is empty, or a theorem that would still hold if a hypothesis were dropped. These live in the library itself: `ExtremeValueTheory/Minimality/`. | see `RESEARCH.md` |
| **Mutation checks** | Statements that are proved "too easily": perturbed statements that still compile. | `scripts/mutation_check.py`, report in [`MUTATION.md`](MUTATION.md) |

Conventions: each test is an `example` or a `theorem` named `test_…`, with a comment citing the
textbook value it checks. Tests use only the public statements of the library, never its internals.
