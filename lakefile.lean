import Lake
open Lake DSL

package «lean-extremevaluetheory»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0-rc1"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.36.0-rc1"

@[default_target]
lean_lib «ExtremeValueTheory» where

/-- Specification tests: non-vacuity, known answers and junk-value checks for the statements of
the library. Built in CI by `lake build Test`; see `Test/README.md`. -/
lean_lib «Test» where
  globs := #[.andSubmodules `Test]
