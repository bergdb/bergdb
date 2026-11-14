/-
025-02 tool (2026-11-14): the cleanup's guard. Run from lean/ after `lake build`:
  lake env lean /Users/f/fl/bench/2026-11-14/cleanup/tools/Guard.lean
Writes to $GUARD_OUT (default ./guard-out.txt):
* AXIOMS: no `axiom` declared outside Lean's own modules, and no constant of ours that uses
  `sorryAx`; then the axioms of every name in $GUARD_AUDIT (default audit.txt beside this file).
* FP lines: the fingerprint of the trusted closure. The closure starts from every constant
  of a module outside SIS.Tree (SIS's other files, Check, BergDB), every constant of the
  trusted SIS.Tree modules (TRUSTED below), and the types of the names in audit.txt; it
  follows the constants named in types, and in the bodies of definitions (not of theorems:
  proofs may change). A line is "FP name kind hash(type) hash(value of a definition)".
  Two guard outputs are compared with `grep '^FP' | sort | diff`: equal means no trusted
  statement and no definition they use changed.
* SIG and NAMES lines: the audited theorems' statements, and their binders' names (for the top
  theorem, the premises' names: hchk, htb, d4, l4, hU, hHL, hMSF, hCoF, hCoU, hMF).
-/
import Lean
import SIS
import Check
import BergDB
import SIS.Tree.MergeProofBundle

open Lean

def guardDir : System.FilePath := "/Users/f/fl/bench/2026-11-14/cleanup/tools"

def TRUSTED : List Name :=
  [`SIS.Tree.Val, `SIS.Tree.Node, `SIS.Tree.Exec, `SIS.Tree.Read, `SIS.Tree.Spec,
   `SIS.Tree.Inv, `SIS.Tree.Props, `SIS.Tree.Bound, `SIS.Tree.Top, `SIS.Tree.MergeProps,
   `SIS.Tree.DeadProps]

def ours (m : Name) : Bool :=
  (`SIS).isPrefixOf m || (`Check).isPrefixOf m || (`BergDB).isPrefixOf m

#eval show MetaM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map (fun i => mods[i.toNat]!)
  let auditP : System.FilePath := (← IO.getEnv "GUARD_AUDIT").getD (guardDir / "audit.txt").toString
  let audit : List Name ← (do
    if ← auditP.pathExists then
      let s ← IO.FS.readFile auditP
      pure ((s.splitOn "\n").filter (fun l => l.trim != "" && !l.startsWith "#") |>.map (·.trim.toName))
    else pure [])
  let mut out : Array String := #[]
  -- 1. no axiom of ours, no sorryAx
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    match modOf n with
    | some m =>
      if ours m then
        if ci matches .axiomInfo _ then bad := bad.push s!"axiom {n} in {m}"
        if ci.getUsedConstantsAsSet.contains ``sorryAx then bad := bad.push s!"sorryAx in {n} ({m})"
    | none => pure ()
  out := out.push s!"AXIOMS ours: {bad.size}"
  out := out ++ bad.map (s!"AXIOMS BAD {·}")
  for n in audit do
    if env.contains n then
      let ax ← collectAxioms n
      let std := ax.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound)
      out := out.push s!"AXIOMS {if std then "ok" else "BAD"} {n} {ax.toList}"
    else out := out.push s!"AXIOMS MISSING {n}"
  -- 2. the trusted closure's fingerprint
  let mut stack : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    match modOf n with
    | some m =>
      if ours m && (!(`SIS.Tree).isPrefixOf m || TRUSTED.contains m) then stack := stack.push n
    | none => pure ()
  for n in audit do
    if let some ci := env.find? n then
      for d in ci.type.getUsedConstants do stack := stack.push d
  let mut seen : Std.HashSet Name := {}
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut next := ci.type.getUsedConstants
      match ci with
      | .defnInfo v => next := next ++ v.value.getUsedConstants
      | .inductInfo v => next := next ++ v.ctors.toArray
      | .ctorInfo v => next := next.push v.induct
      | .opaqueInfo v => next := next ++ v.value.getUsedConstants
      | _ => pure ()
      for d in next do
        if !seen.contains d then stack := stack.push d
  let mut fps : Array String := #[]
  for n in seen.toArray do
    match modOf n with
    | some m =>
      if ours m then
        if let some ci := env.find? n then
          let (k, v) : String × UInt64 := match ci with
            | .defnInfo d => ("def", d.value.hash)
            | .thmInfo _ => ("thm", 0)
            | .opaqueInfo d => ("opaque", d.value.hash)
            | .inductInfo _ => ("ind", 0)
            | .ctorInfo _ => ("ctor", 0)
            | .recInfo _ => ("rec", 0)
            | .axiomInfo _ => ("axiom", 0)
            | .quotInfo _ => ("quot", 0)
          fps := fps.push s!"FP {n} {k} {ci.type.hash} {v}"
    | none => pure ()
  out := out.push s!"FP-COUNT {fps.size}"
  out := out ++ fps.qsort (· < ·)
  -- 3. the top theorems' statements, with the premises' names
  for n in audit do
    if let some ci := env.find? n then
      let fmt ← Meta.ppExpr ci.type
      let s := (toString fmt).replace "\n" " "
      out := out.push s!"SIG {n} : {s}"
      let rec binders (e : Expr) (acc : Array String) : Array String :=
        match e with
        | .forallE b _ body _ => binders body (acc.push b.toString)
        | _ => acc
      out := out.push s!"NAMES {n} : {" ".intercalate (binders ci.type #[]).toList}"
  let dest := (← IO.getEnv "GUARD_OUT").getD "guard-out.txt"
  IO.FS.writeFile dest ("\n".intercalate out.toList ++ "\n")
  IO.println s!"guard: {bad.size} bad; {audit.length} audited; {fps.size} fingerprints -> {dest}"
