import ExtremeValueTheory

/-!
# Junk-value scanner

Lean totalizes partial operations: `x / 0 = 0`, `Real.log 0 = 0`, `Real.sqrt (-1) = 0`, `2 - 3 = 0`
in `ℕ`, `ENNReal.toReal ∞ = 0`, the sum of a non-summable series is `0`, the integral of a
non-integrable function is `0`, `sSup` of an unbounded set of reals is `0`, and so on. A theorem
can be true only because one of these conventions fires. This script lists every theorem of the
library whose *statement* (its type, not its proof) contains a junk-prone operation, together with
a heuristic classification of each occurrence. It also lists the definitions whose *bodies* contain
such an operation (the convention-dependent definitions).

Run from the repository root (not part of any library target, so CI does not run it):

```
lake env lean scripts/JunkScan.lean > junk_scan.tsv
```

Output (tab separated):

```
THM <priority?> <name> <module> <ops> <classes>
DEF <name> <module> <ops>
```

Each occurrence is classified as
* `G` guarded: some hypothesis mentions the very term the operation could junk on (`b ≠ 0`,
  `0 < b`, `Integrable f`, `Summable f`, `BddAbove s`, `IsFiniteMeasure μ`, …);
* `C` constant: the term is a closed numeral or literal (e.g. `x / 2`);
* `L` lambda-bound: the term mentions a variable bound by a `fun` inside the statement (a sequence
  under `Tendsto`, an integrand, a set-builder); usually asymptotic or almost-everywhere, so a junk
  value at isolated points is irrelevant;
* `Q` quantifier-bound: the term mentions a variable bound by `∀` or `∃` inside the statement; the
  junk point could be chosen by the quantifier, so this needs a manual look;
* `U` unguarded: a free parameter of the theorem that no hypothesis visibly constrains; manual look.

`hyp:` marks occurrences that only appear in hypotheses (junk there makes a hypothesis weaker or
stronger, never the conclusion trivially true by itself).
-/

open Lean Meta

namespace JunkScan

/-- Kinds of binders on the traversal stack. -/
inductive BK | lam | quant
  deriving BEq, Inhabited

structure Occ where
  op : String
  cls : Char
  inHyp : Bool
  /-- The term the operation could junk on. -/
  term : Expr := .bvar 0
  /-- Pretty-printed `term`, filled for `U` occurrences in detail mode. -/
  detail : String := ""

/-- Short name of a type, for the common carriers. -/
def carrier (t : Expr) : Option String :=
  match t.constName? with
  | some ``Real => "ℝ"
  | some ``ENNReal => "ℝ≥0∞"
  | some ``NNReal => "ℝ≥0"
  | some ``Nat => "ℕ"
  | some ``Int => "ℤ"
  | some ``EReal => "EReal"
  | _ => none

/-- Is `e` a closed literal (numeral, `π`, `exp` of something closed...)? -/
partial def isClosedConst (e : Expr) : Bool :=
  !e.hasFVar && !e.hasLooseBVars && !e.hasMVar

/-- The junk-prone operation at the head of `e`, the term it could junk on, and the hypothesis
heads that count as guards. -/
def classifyHead (e : Expr) : Option (String × Expr × List Name) :=
  let f := e.getAppFn
  let args := e.getAppArgs
  let n := args.size
  match f.constName? with
  | some ``HDiv.hDiv =>
    if n == 6 then (carrier args[0]!).bind fun c =>
      if c == "ℝ≥0∞" then some (s!"div[{c}]", args[5]!, [``Ne, ``LT.lt, ``GT.gt, ``Not])
      else some (s!"div[{c}]", args[5]!, [``Ne, ``LT.lt, ``GT.gt, ``Not])
    else none
  | some ``Inv.inv =>
    if n == 3 then (carrier args[0]!).bind fun c =>
      if c == "ℝ" || c == "ℝ≥0" then some (s!"inv[{c}]", args[2]!, [``Ne, ``LT.lt, ``GT.gt, ``Not])
      else none
    else none
  | some ``Real.log => if n == 1 then some ("log", args[0]!, [``Ne, ``LT.lt, ``GT.gt, ``Not]) else none
  | some ``Real.logb => if n == 2 then some ("logb", args[1]!, [``Ne, ``LT.lt, ``GT.gt]) else none
  | some ``Real.sqrt => if n == 1 then some ("sqrt", args[0]!, [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt]) else none
  | some ``Real.rpow => if n == 2 then some ("rpow", args[0]!, [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt]) else none
  | some ``HPow.hPow =>
    if n == 6 && args[0]!.isConstOf ``Real && args[1]!.isConstOf ``Real then
      some ("rpow", args[4]!, [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt])
    else none
  | some ``HSub.hSub =>
    if n == 6 && args[0]!.isConstOf ``Nat then
      some ("natSub", args[5]!, [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt])
    else none
  | some ``ENNReal.toReal => if n == 1 then some ("toReal", args[0]!, [``Ne, ``LT.lt, ``Not]) else none
  | some ``ENNReal.toNNReal => if n == 1 then some ("toNNReal", args[0]!, [``Ne, ``LT.lt, ``Not]) else none
  | some ``EReal.toReal => if n == 1 then some ("ERealToReal", args[0]!, [``Ne, ``LT.lt]) else none
  | some ``ENNReal.ofReal => if n == 1 then some ("ofReal", args[0]!, [``LE.le, ``LT.lt]) else none
  | some ``Real.toNNReal => if n == 1 then some ("toNNReal'", args[0]!, [``LE.le, ``LT.lt]) else none
  | some ``Nat.floor => if n == 4 then some ("floor", args[3]!, [``LE.le, ``LT.lt]) else none
  | some ``Nat.ceil => if n == 4 then some ("ceil", args[3]!, [``LE.le, ``LT.lt]) else none
  | some ``Int.toNat => if n == 1 then some ("toNat", args[0]!, [``LE.le, ``LT.lt]) else none
  | some ``tsum =>
    if n ≥ 5 then
      match carrier args[0]! with
      | some "ℝ≥0∞" => none
      | _ => some ("tsum", args[4]!, [``Summable, ``HasSum])
    else none
  | some ``MeasureTheory.integral =>
    if n == 7 then some ("integral", args[6]!,
      [``MeasureTheory.Integrable, ``MeasureTheory.IntegrableOn, ``MeasureTheory.MemLp,
       ``IntervalIntegrable, ``MeasureTheory.HasFiniteIntegral])
    else none
  | some ``Filter.limUnder => some ("limUnder", e, [``Filter.Tendsto, ``CauchySeq])
  | some ``Filter.lim => some ("lim", e, [``Filter.Tendsto])
  | some ``Classical.epsilon => some ("epsilon", e, [``Exists])
  | some ``SupSet.sSup =>
    if n == 3 then (carrier args[0]!).bind fun c =>
      if c == "ℝ" || c == "ℕ" || c == "ℝ≥0" then some (s!"sSup[{c}]", args[2]!, [``BddAbove, ``Set.Nonempty]) else none
    else none
  | some ``InfSet.sInf =>
    if n == 3 then (carrier args[0]!).bind fun c =>
      if c == "ℝ" then some (s!"sInf[{c}]", args[2]!, [``BddBelow, ``Set.Nonempty]) else none
    else none
  | some ``iSup =>
    if n == 4 then (carrier args[0]!).bind fun c =>
      if c == "ℝ" || c == "ℕ" || c == "ℝ≥0" then some (s!"iSup[{c}]", args[3]!, [``BddAbove]) else none
    else none
  | some ``iInf =>
    if n == 4 then (carrier args[0]!).bind fun c =>
      if c == "ℝ" then some (s!"iInf[{c}]", args[3]!, [``BddBelow]) else none
    else none
  | some ``Filter.limsup =>
    if n == 5 && args[0]!.isConstOf ``Real then
      some ("limsup[ℝ]", args[3]!, [``Filter.IsBoundedUnder, ``Filter.IsCoboundedUnder]) else none
  | some ``Filter.liminf =>
    if n == 5 && args[0]!.isConstOf ``Real then
      some ("liminf[ℝ]", args[3]!, [``Filter.IsBoundedUnder, ``Filter.IsCoboundedUnder]) else none
  | some ``deriv => if n ≥ 7 then some ("deriv", args[5]!, [``Differentiable, ``DifferentiableAt,
      ``HasDerivAt, ``DifferentiableOn, ``ContDiff]) else none
  | some ``ProbabilityTheory.variance =>
    some ("variance", e, [``MeasureTheory.MemLp])
  | some ``MeasureTheory.condExp =>
    some ("condExp", e, [``MeasureTheory.Integrable])
  | _ => none

/-- Head constant of a proposition, after stripping leading `∀` binders. -/
partial def propHead (e : Expr) : Option Name :=
  match e with
  | .forallE _ _ b _ => propHead b
  | _ =>
    let f := e.getAppFn
    match f.constName? with
    | some n => some n
    | none => none

/-- `t` occurs in `h` as a subterm. -/
def occursIn (t h : Expr) : Bool :=
  (h.find? (· == t)).isSome

/-- Does some hypothesis with an allowed head mention `t`? The finite-measure classes also guard
`ENNReal.toReal (μ s)`. -/
def guarded (hyps : Array Expr) (op : String) (t : Expr) (heads : List Name) : Bool :=
  hyps.any fun h =>
    let headOk := match propHead h with
      | some n => heads.contains n || (op == "toReal" || op == "toNNReal") &&
          (n == ``MeasureTheory.IsFiniteMeasure || n == ``MeasureTheory.IsProbabilityMeasure)
      | none => false
    headOk && (occursIn t h ||
      -- `μ s`: a hypothesis about `μ` (e.g. `IsFiniteMeasure μ`) guards it.
      ((op == "toReal" || op == "toNNReal") && (t.getAppArgs.any fun a => a.isFVar && occursIn a h)))

/-- Positive "always nonzero" denominators: `Real.exp _`, numerals. -/
def obviouslyPositive (t : Expr) : Bool :=
  t.getAppFn.isConstOf ``Real.exp || t.getAppFn.isConstOf ``OfNat.ofNat && isClosedConst t

/-- Traverse `e`, recording occurrences. `stk` lists the binders entered, innermost first. -/
partial def visit (hyps : Array Expr) (inHyp : Bool) (stk : List BK) (e : Expr) :
    StateM (Array Occ) Unit := do
  match e with
  | .lam _ t b _ => visit hyps inHyp stk t; visit hyps inHyp (BK.lam :: stk) b
  | .forallE _ t b _ => visit hyps inHyp stk t; visit hyps inHyp (BK.quant :: stk) b
  | .letE _ t v b _ =>
    visit hyps inHyp stk t; visit hyps inHyp stk v; visit hyps inHyp (BK.lam :: stk) b
  | .mdata _ b => visit hyps inHyp stk b
  | .proj _ _ b => visit hyps inHyp stk b
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    -- `∃ x, p x` and `∃ x ∈ s, ...`: the bound variable is quantifier-bound.
    if f.isConstOf ``Exists && args.size == 2 then
      match args[1]! with
      | .lam _ t b _ => visit hyps inHyp stk t; visit hyps inHyp (BK.quant :: stk) b; return
      | _ => pure ()
    if let some (op, t, heads) := classifyHead e then
      let cls : Char :=
        if isClosedConst t || obviouslyPositive t then 'C'
        else if t.hasLooseBVars then
          -- Which binders does `t` mention?
          let quant := (List.range stk.length).any fun i =>
            t.hasLooseBVar i && stk[i]! == BK.quant
          if quant then 'Q' else 'L'
        else if guarded hyps op t heads then 'G'
        else 'U'
      modify (·.push { op, cls, inHyp, term := t })
    visit hyps inHyp stk f
    for a in args do visit hyps inHyp stk a
  | _ => pure ()

/-- Occurrences in the statement `ty` of a theorem. -/
def scanType (ty : Expr) : MetaM (Array Occ) :=
  forallTelescope ty fun xs concl => do
    let hyps ← xs.mapM fun x => inferType x
    let act : StateM (Array Occ) Unit := do
      for h in hyps do visit hyps true [] h
      visit hyps false [] concl
    let occs := (act.run #[]).2
    if (← IO.getEnv "JUNK_DETAIL").isNone then return occs
    occs.mapM fun o => do
      if o.cls == 'U' then
        let d ← try (toString <$> ppExpr o.term) catch _ => pure "?"
        return { o with detail := d.replace "\n" " " }
      else return o

/-- Occurrences in a definition body. -/
def scanValue (v : Expr) : Array Occ :=
  (visit #[] false [] v |>.run #[]).2

def summarize (occs : Array Occ) : String × String :=
  let ops := occs.foldl (fun (acc : Array String) o =>
    let s := (if o.inHyp then "hyp:" else "") ++ o.op
    if acc.contains s then acc else acc.push s) #[]
  let cls := occs.foldl (fun (acc : Array String) o =>
    let s := (if o.inHyp then "hyp:" else "") ++ o.op ++ "=" ++ toString o.cls
    if acc.contains s then acc else acc.push s) #[]
  (String.intercalate "," ops.toList, String.intercalate "," cls.toList)

/-- Lean names mentioned by the README, THEOREMS.md and the blueprint `\lean{...}` lists. -/
def priorityNames : IO (Array String) := do
  let mut out : Array String := #[]
  for f in ["README.md", "THEOREMS.md"] do
    let s ← IO.FS.readFile f
    let parts := s.splitOn "`"
    for i in [0:parts.length] do
      if i % 2 == 1 then
        let p := parts[i]!.trimAscii.toString
        if !p.isEmpty && !p.contains ' ' then out := out.push p
  let dir : System.FilePath := "blueprint/src/sections"
  for entry in ← dir.readDir do
    let s ← IO.FS.readFile entry.path
    for chunk in (s.splitOn "\\lean{").drop 1 do
      let body := (chunk.splitOn "}").head!
      for nm in body.splitOn "," do
        let nm := nm.trimAscii.toString
        if !nm.isEmpty then out := out.push nm
  return out

def isPriority (prio : Array String) (n : Name) : Bool :=
  let s := n.toString
  prio.any fun p => s == p || s.endsWith ("." ++ p)

def skipName (n : Name) : Bool :=
  n.isInternalDetail || n.isInternal ||
    (n.components.any fun c => match c with
      | .str _ s => s.startsWith "eq_" || s == "eq_def" || s.startsWith "match_" ||
          s.startsWith "proof_" || s == "injEq" || s == "inj" || s == "sizeOf_spec" ||
          s.startsWith "_" || s == "ext_iff" || s == "noConfusion"
      | _ => false)

def main : MetaM Unit := do
  let env ← getEnv
  let prio ← priorityNames
  let mods := env.header.moduleNames
  let mut thms : Array (Name × Name × Expr) := #[]
  let mut defs : Array (Name × Name × Expr) := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless (`ExtremeValueTheory).isPrefixOf m do continue
    if skipName n then continue
    match ci with
    | .thmInfo t => thms := thms.push (n, m, t.type)
    | .defnInfo d =>
      if !(← isInstance n) && !(← isProp d.type) then defs := defs.push (n, m, d.value)
    | _ => pure ()
  thms := thms.qsort (fun a b => a.1.toString < b.1.toString)
  defs := defs.qsort (fun a b => a.1.toString < b.1.toString)
  let mut nThmHit := 0
  let mut nPrio := 0
  let mut nPrioHit := 0
  let mut opCount : Std.HashMap String Nat := {}
  for (n, m, ty) in thms do
    let occs ← try scanType ty catch _ => pure #[]
    let pr := isPriority prio n
    if pr then nPrio := nPrio + 1
    if occs.isEmpty then continue
    nThmHit := nThmHit + 1
    if pr then nPrioHit := nPrioHit + 1
    for o in occs do
      let k := o.op ++ "/" ++ toString o.cls
      opCount := opCount.insert k (opCount.getD k 0 + 1)
    let (ops, cls) := summarize occs
    IO.println s!"THM\t{if pr then "P" else "-"}\t{n}\t{m}\t{ops}\t{cls}"
    if (← IO.getEnv "JUNK_DETAIL").isSome then
      for o in occs do
        if o.cls == 'U' then
          IO.println s!"  U\t{if o.inHyp then "hyp:" else ""}{o.op}\t{o.detail}"
  let mut nDefHit := 0
  for (n, m, v) in defs do
    let occs := scanValue v
    if occs.isEmpty then continue
    nDefHit := nDefHit + 1
    IO.println s!"DEF\t{n}\t{m}\t{(summarize occs).1}"
  IO.println s!"SUMMARY\ttheorems={thms.size}\ttheorems_with_hits={nThmHit}\tpriority={nPrio}\tpriority_with_hits={nPrioHit}\tdefs={defs.size}\tdefs_with_hits={nDefHit}"
  let counts := opCount.toArray.qsort (fun a b => a.1 < b.1)
  for (k, c) in counts do IO.println s!"COUNT\t{k}\t{c}"

end JunkScan

#eval JunkScan.main
