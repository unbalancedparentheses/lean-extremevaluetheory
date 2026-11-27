/-
Copyright (c) 2026 Federico Carrone.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Federico Carrone
-/
import Executable.Estimators

open ExtremeValueTheory.Executable

private def parseFloat (s : String) : Option Float :=
  let s := s.trimAscii.toString
  if s.isEmpty then none
  else
    let (neg, body) :=
      if s.startsWith "-" then (true, (s.drop 1).toString)
      else if s.startsWith "+" then (false, (s.drop 1).toString)
      else (false, s)
    -- Split scientific notation `mantissa e/E exp`
    let expParts :=
      match body.splitOn "e" with
      | [a, b] => (a, some b)
      | _ =>
        match body.splitOn "E" with
        | [a, b] => (a, some b)
        | _ => (body, none)
    let mantParts := expParts.1.splitOn "."
    let parseNat (t : String) : Option Nat :=
      if t.isEmpty then some 0 else t.toNat?
    let mantOpt : Option Float :=
      match mantParts with
      | [intStr] =>
        if intStr.isEmpty then none
        else intStr.toNat?.map (·.toFloat)
      | [intStr, fracStr] =>
        match parseNat intStr, parseNat fracStr with
        | some i, some f =>
          let scale := (10.0 : Float) ^ fracStr.length.toFloat
          some (i.toFloat + f.toFloat / scale)
        | _, _ => none
      | _ => none
    let expOpt : Option Int :=
      match expParts.2 with
      | none => some 0
      | some eStr =>
        if eStr.startsWith "-" then ((eStr.drop 1).toString.toNat?).map (fun n => -(n : Int))
        else if eStr.startsWith "+" then ((eStr.drop 1).toString.toNat?).map (fun n => (n : Int))
        else eStr.toNat?.map (fun n => (n : Int))
    match mantOpt, expOpt with
    | some m, some e =>
      let v :=
        if e >= 0 then m * ((10.0 : Float) ^ e.toNat.toFloat)
        else m / ((10.0 : Float) ^ (-e).toNat.toFloat)
      some (if neg then -v else v)
    | _, _ => none

private def parseFloats (tokens : List String) : IO (Array Float) := do
  let mut out : Array Float := #[]
  for t in tokens do
    if t.trimAscii.toString.isEmpty then continue
    match parseFloat t with
    | some x => out := out.push x
    | none => throw <| IO.userError s!"cannot parse float: {t}"
  return out

private def readStdinFloats : IO (Array Float) := do
  let stdin ← IO.getStdin
  let content ← stdin.readToEnd
  let tokens := content.split (fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t' || c == ',')
  parseFloats (tokens.toList.map (·.toString))

private def getData (rest : List String) : IO (Array Float) :=
  match rest with
  | ["--stdin"] => readStdinFloats
  | _ => parseFloats rest

private def parseFloatArg (s : String) : IO Float :=
  match parseFloat s with
  | some x => pure x
  | none => throw <| IO.userError s!"cannot parse float argument: {s}"

private def parseNatArg (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw <| IO.userError s!"cannot parse nat argument: {s}"

/-- Format a `Float` with 15 decimal places (Lean's default `Float.toString` prints only 6). -/
private def fmtFloat (x : Float) : String :=
  if x.isNaN then "nan"
  else if !x.isFinite then if x > 0.0 then "inf" else "-inf"
  else
    let neg := x < 0.0
    let ax := if neg then -x else x
    -- Normalize to scientific notation `m × 10^e` with `1 ≤ m < 10` (or `0` if `ax == 0`)
    if ax == 0.0 then "0.0"
    else
      let eFloat := Float.floor (Float.log10 ax)
      let eInt : Int :=
        if eFloat >= 0.0 then (eFloat.toUInt64.toNat : Int)
        else -((-eFloat).toUInt64.toNat : Int)
      let scale := (10.0 : Float) ^ eFloat
      let m0 := ax / scale
      let (m, e) :=
        if m0 >= 10.0 then (m0 / 10.0, eInt + 1)
        else if m0 < 1.0 then (m0 * 10.0, eInt - 1)
        else (m0, eInt)
      let d0 := (Float.floor m).toUInt64.toNat
      let frac := Float.round ((m - d0.toFloat) * 1e15)
      let fracNat := frac.toUInt64.toNat
      let (d0', fracNat') :=
        if fracNat >= 1000000000000000 then (d0 + 1, fracNat - 1000000000000000)
        else (d0, fracNat)
      let fracStrRaw := toString fracNat'
      let padLen := if fracStrRaw.length < 15 then 15 - fracStrRaw.length else 0
      let fracStr := String.ofList (List.replicate padLen '0') ++ fracStrRaw
      let signStr := if neg then "-" else ""
      s!"{signStr}{d0'}.{fracStr}e{e}"

def main (args : List String) : IO UInt32 := do
  match args with
  | "hill" :: kStr :: rest =>
    let k ← parseNatArg kStr
    let xs ← getData rest
    IO.println (fmtFloat (hill xs k))
    return 0
  | "pickands" :: kStr :: rest =>
    let k ← parseNatArg kStr
    let xs ← getData rest
    IO.println (fmtFloat (pickands xs k))
    return 0
  | "moment" :: kStr :: rest =>
    let k ← parseNatArg kStr
    let xs ← getData rest
    IO.println (fmtFloat (momentEstimator xs k))
    return 0
  | "weissman" :: kStr :: pStr :: rest =>
    let k ← parseNatArg kStr
    let p ← parseFloatArg pStr
    let xs ← getData rest
    IO.println (fmtFloat (weissman xs k p))
    return 0
  | "lmoments" :: rest =>
    let xs ← getData rest
    let vals := [samplePWM xs 0, samplePWM xs 1, samplePWM xs 2,
      sampleLMoment1 xs, sampleLMoment2 xs, sampleLMoment3 xs, sampleLSkewness xs,
      gpdPWMShapeEst xs, gpdPWMScaleEst xs]
    IO.println (" ".intercalate (vals.map fmtFloat))
    return 0
  | "gev-loglik" :: xiStr :: muStr :: sigStr :: rest =>
    let xi ← parseFloatArg xiStr
    let mu ← parseFloatArg muStr
    let sig ← parseFloatArg sigStr
    let xs ← getData rest
    IO.println (fmtFloat (gevLogLik xi mu sig xs))
    return 0
  | "gev-rl" :: xiStr :: muStr :: sigStr :: mStr :: [] =>
    let xi ← parseFloatArg xiStr
    let mu ← parseFloatArg muStr
    let sig ← parseFloatArg sigStr
    let m ← parseFloatArg mStr
    IO.println (fmtFloat (gevReturnLevel xi mu sig m))
    return 0
  | "gumbel-rl-var" :: sigStr :: mStr :: [] =>
    let sig ← parseFloatArg sigStr
    let m ← parseFloatArg mStr
    IO.println (fmtFloat (gumbelReturnLevelVar sig m))
    return 0
  | "gpd-loglik" :: xiStr :: sigStr :: rest =>
    let xi ← parseFloatArg xiStr
    let sig ← parseFloatArg sigStr
    let xs ← getData rest
    IO.println (fmtFloat (gpdLogLik xi sig xs))
    return 0
  | "gpd-rl" :: uStr :: xiStr :: sigStr :: zetaStr :: nStr :: [] =>
    let u ← parseFloatArg uStr
    let xi ← parseFloatArg xiStr
    let sig ← parseFloatArg sigStr
    let zeta ← parseFloatArg zetaStr
    let N ← parseFloatArg nStr
    IO.println (fmtFloat (gpdReturnLevel u xi sig zeta N))
    return 0
  | "gev-mle" :: rest =>
    let xs ← getData rest
    let (xi, mu, sig, ll) := fitGevMLE xs
    IO.println (" ".intercalate ([xi, mu, sig, ll].map fmtFloat))
    return 0
  | "gumbel-mle" :: rest =>
    let xs ← getData rest
    let (mu, sig, ll) := fitGumbelMLE xs
    IO.println (" ".intercalate ([mu, sig, ll].map fmtFloat))
    return 0
  | "gpd-mle" :: rest =>
    let xs ← getData rest
    let (xi, sig, ll) := fitGpdMLE xs
    IO.println (" ".intercalate ([xi, sig, ll].map fmtFloat))
    return 0
  | "extremal-index" :: rStr :: uStr :: rest =>
    let r ← parseNatArg rStr
    let u ← parseFloatArg uStr
    let xs ← getData rest
    let vals := [blocksEstimator xs r u, runsEstimator xs r u,
      slidingBlocksEstimator xs r u, intervalsEstimator xs u]
    IO.println (" ".intercalate (vals.map fmtFloat))
    return 0
  | _ =>
    IO.eprintln "Usage: evt_estimators <command> [args] [--stdin | x0 x1 ...]"
    IO.eprintln "Commands: hill, pickands, moment, weissman, lmoments, gev-loglik, gev-rl, gumbel-rl-var, gpd-loglik, gpd-rl, gev-mle, gumbel-mle, gpd-mle, extremal-index"
    return 1
