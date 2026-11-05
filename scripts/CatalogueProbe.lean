import ExtremeValueTheory

/-!
# What Lean says about the catalogue's names

Reads declaration names, one per line, from the file named by `CATALOGUE_NAMES`, and writes a JSON
array to the file named by `CATALOGUE_OUT`. Run by `scripts/catalogue.py`, not by hand, and not part
of any library target.

For each name it reports:
* `statement`: the signature `#check` prints, at a fixed width;
* `closure`: a hash of the statement's type and of every library definition it reaches, so a change
  to a definition changes the hash of a theorem whose text did not change. Theorems in the closure
  count by their type only, and Mathlib stops the walk (the Mathlib revision is hashed separately);
* `trivial`: why the theorem has no mathematical content of its own, or `null`. See `triviality`;
* `axioms`, and the `library_deps` and `mathlib_deps` of the proof, as evidence for a `wrapper` status.
-/

open Lean Meta Elab Command

namespace CatalogueProbe

/-- Heartbeat budget for one `isDefEq` in the triviality check, in the unit of `maxHeartbeats`. -/
def defEqBudget : Nat := 5000

def inPrefix (env : Environment) (pre : Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => pre.isPrefixOf env.header.moduleNames[i.toNat]!
  | none => false

def inLibrary (env : Environment) : Name → Bool := inPrefix env `ExtremeValueTheory

/-- `foo.eq_1`, `foo.eq_def`: the equations `unfold` and `rw [foo]` use. Using one is unfolding. -/
def isEquationLemma (n : Name) : Bool :=
  match n with
  | .str _ s => s == "eq_def" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
  | _ => false

/-- A proof term that is `rfl` (or `Iff.rfl`, …) under its binders. -/
partial def isRflTerm (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ b _ => isRflTerm b
  | e' => [``rfl, ``Eq.refl, ``HEq.refl, ``HEq.rfl, ``Iff.rfl, ``Iff.refl].contains e'.getAppFn.constName

/-- The theorems a proof really uses: not the core logic in `Init` (congruence, `Eq.mpr`, `And.intro`),
not equation lemmas, not Mathlib lemmas that are themselves `rfl`. -/
def realDeps (env : Environment) (value : Expr) : Array Name :=
  value.getUsedConstants.filter fun n ↦
    match env.find? n with
    | some (.thmInfo t) =>
      !isEquationLemma n && !inPrefix env `Init n && !inPrefix env `Std n &&
        !(!inLibrary env n && isRflTerm t.value)
    | _ => false

/-- A theorem uses no real theorem, or only library theorems that are themselves empty in this sense:
it follows from its hypotheses and definitions alone. Mathlib theorems end the walk as real; without
that, everything would count as empty, since all proofs bottom out in `Init`. -/
partial def isEmptyProof (cache : IO.Ref NameSet) (env : Environment) (value : Expr) (seen : NameSet) :
    IO Bool := do
  for d in realDeps env value do
    unless inLibrary env d do return false
    if (← cache.get).contains d || seen.contains d then continue
    let some (.thmInfo t) := env.find? d | return false
    unless ← isEmptyProof cache env t.value (seen.insert d) do return false
    cache.modify (·.insert d)
  return true

/-- Run `isDefEq` under a budget; running out counts as "not known to be defeq". -/
def defEqWithin (a b : Expr) : MetaM Bool :=
  withCurrHeartbeats <|
    withTheReader Core.Context (fun c ↦ { c with maxHeartbeats := defEqBudget * 1000 }) <|
      tryCatchRuntimeEx (isDefEq a b) fun _ ↦ pure false

/-- Why a theorem is empty, or `none`.
* `rfl`: the proof term is `rfl`, possibly under binders;
* `no-theorem`: it uses no real theorem (unfolding, projecting and pairing hypotheses);
* `defeq-sides`: the conclusion is an `=` or `↔` whose sides are defeq, whatever the proof looks like;
* `defeq-hypothesis`: the conclusion is defeq to one of the hypotheses. -/
def triviality (cache : IO.Ref NameSet) (type value : Expr) : MetaM (Option String) := do
  if isRflTerm value then return some "rfl"
  if ← isEmptyProof cache (← getEnv) value {} then return some "no-theorem"
  forallTelescope type fun xs concl ↦ do
    if let some (_, a, b) := concl.eq? then
      if ← defEqWithin a b then return some "defeq-sides"
    if let some (a, b) := concl.iff? then
      if ← defEqWithin a b then return some "defeq-sides"
    for x in xs do
      let t ← inferType x
      if ← isProp t then
        if ← defEqWithin t concl then return some "defeq-hypothesis"
    return none

/-- The hash of a statement and of the library definitions it reaches. -/
partial def closureHash (env : Environment) (type : Expr) : UInt64 := Id.run do
  let mut seen : NameSet := {}
  let mut todo := type.getUsedConstants.toList
  let mut acc := type.hash
  let mut parts : Array (Name × UInt64) := #[]
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n || !inLibrary env n then continue
      seen := seen.insert n
      let some c := env.find? n | continue
      let mut h := hash c.type
      let mut more := c.type.getUsedConstants.toList
      match c with
      | .thmInfo _ | .recInfo _ | .axiomInfo _ | .quotInfo _ => pure ()
      | .inductInfo i => more := i.ctors ++ more
      | _ =>
        if let some v := c.value? (allowOpaque := true) then
          h := mixHash h (hash v)
          more := v.getUsedConstants.toList ++ more
      parts := parts.push (n, h)
      todo := more ++ todo
  for (n, h) in parts.qsort (fun a b ↦ a.1.quickLt b.1) do
    acc := mixHash acc (mixHash (hash n) h)
  return acc

def report (cache : IO.Ref NameSet) (n : Name) : MetaM Json := do
  let env ← getEnv
  let some c := env.find? n | return Json.mkObj [("name", toString n), ("found", false)]
  let statement := (← PrettyPrinter.ppSignature n).fmt.pretty 100
  let isTheorem ← isProp c.type
  let value? := c.value? (allowOpaque := true)
  let trivial ← match isTheorem, value? with
    | true, some v => triviality cache c.type v
    | _, _ => pure none
  let deps := (value?.map (realDeps env)).getD #[]
  let axioms ← collectAxioms n
  return Json.mkObj [
    ("name", toString n), ("found", true),
    ("is_theorem", isTheorem),
    ("deprecated", Linter.isDeprecated env n),
    ("module", toString (((env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)).getD .anonymous)),
    ("statement", statement),
    ("closure", toString (closureHash env c.type).toNat),
    ("trivial", match trivial with | some s => Json.str s | none => Json.null),
    ("axioms", toJson (axioms.map toString)),
    ("library_deps", toJson ((deps.filter (inLibrary env)).map toString)),
    ("mathlib_deps", toJson ((deps.filter (!inLibrary env ·)).map toString))]

set_option maxHeartbeats 0 in
run_cmd do
  let names ← IO.getEnv "CATALOGUE_NAMES"
  let out ← IO.getEnv "CATALOGUE_OUT"
  let (some names, some out) := (names, out) | throwError "set CATALOGUE_NAMES and CATALOGUE_OUT"
  let lines := (← IO.FS.lines names).filter (!·.isEmpty)
  let cache ← IO.mkRef {}
  let results ← liftTermElabM <| lines.mapM fun line ↦ report cache line.toName
  IO.FS.writeFile out (Json.arr results).pretty

end CatalogueProbe
