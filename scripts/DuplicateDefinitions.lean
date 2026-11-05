import ExtremeValueTheory

/-!
# Duplicate definitions

Reports definitions of the library whose bodies are the same term, so that the same concept under two
names shows up however it was written (`Real.log` or `log` under `open Real`, other binder names). It
compares elaborated terms, not text, and only the bodies of definitions written by a person: no
instances, structure projections or generated declarations, and no aliases or other bodies too small
to mean anything.

Run with `lake env lean scripts/DuplicateDefinitions.lean`, normally through
`scripts/check_architecture.py`, which reads the `duplicate definitions:` lines printed here.
-/

open Lean Elab Command Meta

run_cmd do
  let env ← getEnv
  let inLibrary (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => (`ExtremeValueTheory).isPrefixOf env.header.moduleNames[i.toNat]!
    | none => true -- this file: the self-test appends bad definitions to a copy of it
  let isGenerated (n : Name) : Bool :=
    n.isInternalDetail || isInstanceCore env n || (env.isProjectionFn n) || isMatcherCore env n ||
      isRecCore env n || isAuxRecursor env n || isNoConfusion env n
  let bodies : Std.HashMap Expr (Array Name) := env.constants.fold (init := {}) fun acc n c ↦
    match c with
    | .defnInfo d =>
      if inLibrary n && !isGenerated n && d.value.approxDepth > 3 then
        acc.alter d.value fun names ↦ some ((names.getD #[]).push n)
      else acc
    | _ => acc
  let groups := bodies.toArray.filterMap fun (_, names) ↦
    if names.size > 1 then some names else none
  for names in groups.qsort (fun a b ↦ a[0]!.toString < b[0]!.toString) do
    logInfo m!"duplicate definitions: {", ".intercalate (names.toList.map toString |>.mergeSort)}"
