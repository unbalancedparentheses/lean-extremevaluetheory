import Lake
open Lake DSL

package «lean-extremevaluetheory»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib «ExtremeValueTheory» where
