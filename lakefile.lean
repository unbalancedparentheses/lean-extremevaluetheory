import Lake
open Lake DSL

package «lean-extremevaluetheory»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.35.0"

@[default_target]
lean_lib «ExtremeValueTheory» where

/-- Specification tests: non-vacuity, known answers and junk-value checks for the statements of
the library. Built in CI by `lake build Test`; see `Test/README.md`. -/
lean_lib «Test» where
  globs := #[.andSubmodules `Test]

/-- Worked examples for downstream users: a tutorial, the standard laws and applied problems. They
import only the umbrella `ExtremeValueTheory`, and nothing in the library imports them. Built in CI
by `lake build Examples`; see `docs/TUTORIAL.md`. -/
lean_lib «Examples» where
  globs := #[.andSubmodules `Examples]

/-- The comparator challenge and its solution (see `comparator.json`). Not a default target and not
part of the library. `roots` is empty so that tools that import every library root, such as
`checkdecls`, do not load these two modules together: they declare the same names on purpose. -/
lean_lib «ComparatorChallenge» where
  roots := #[]
  globs := #[.one `Challenge, .one `Solution]
