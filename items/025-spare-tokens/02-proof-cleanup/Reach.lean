/-
025-02 tool (2026-11-14): the declarations of lean/SIS/Tree and their uses, for the prune
script prune.py. Run from lean/ after a clean `lake build`:
  lake env lean /Users/f/fl/bench/2026-11-14/cleanup/tools/Reach.lean
Writes $REACH_OUT (default ./reach-decls.tsv), one line per declaration of a SIS.Tree module
(auxiliary ones folded into their owner, private ones in):
  name  module  kind  startLine  endLine  rootReach  deps
rootReach is 1 when the declaration is used, through proof terms and definitions, by a
constant of a module outside SIS.Tree (SIS's other files, Check, BergDB) or by a name in
roots.txt beside this file. deps are the SIS.Tree declarations that its type and value name.
prune.py adds the uses that terms do not show (names in the source text: rfl simp lemmas,
attributes, #guard) and computes what may go.
-/
import Lean
import SIS
import Check
import BergDB
import SIS.Tree.MergeProofBundle

open Lean

def reachDir : System.FilePath := "/Users/f/fl/bench/2026-11-14/cleanup/tools"

/-- The declaration a name belongs to: a private name's user name; an auxiliary
name (`foo.proof_1`, `foo.match_2`, `foo.eq_1`, `foo._simp_1`) its owner `foo`. -/
partial def owner (n : Name) : Name :=
  let n := (privateToUserName? n).getD n
  match n with
  | .str p s =>
    if s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "_"
      || s == "eq_def" || s == "induct" || s == "sizeOf_spec" || s == "injEq" || s == "inj"
      || s == "noConfusion" || s == "noConfusionType" || s == "rec" || s == "recOn"
      || s == "casesOn" || s == "below" || s == "brecOn" || s == "ibelow" || s == "binductionOn"
      || s == "ctorIdx" || s == "toCtorIdx" then owner p else n
  | _ => n

#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map (fun i => mods[i.toNat]!)
  let isTree (m : Name) : Bool := (`SIS.Tree).isPrefixOf m
  let extra ← (do
    let p := reachDir / "roots.txt"
    if ← p.pathExists then
      let s ← IO.FS.readFile p
      pure ((s.splitOn "\n").filter (fun l => l.trim != "" && !l.startsWith "#") |>.map (·.trim.toName))
    else pure [])
  -- the walk from the roots
  let mut stack : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  for (n, _) in env.constants.map₁.toList do
    match modOf n with
    | some m => if !isTree m then stack := stack.push n
    | none => pure ()
  let mut missing : Array Name := #[]
  for n in extra do
    if env.contains n then stack := stack.push n else missing := missing.push n
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      let mut next := ci.getUsedConstantsAsSet.toArray
      match ci with
      | .inductInfo v => next := next ++ v.ctors.toArray
      | .ctorInfo v => next := next.push v.induct
      | _ => pure ()
      for d in next do
        if !seen.contains d then stack := stack.push d
  -- a declaration is reached when it or any of its auxiliaries is
  let mut reachedOwner : Std.HashSet Name := {}
  for n in seen.toArray do reachedOwner := reachedOwner.insert (owner n)
  -- the declarations of SIS.Tree, by owner
  let mut deps : Std.HashMap Name (Std.HashSet Name) := {}
  let mut info : Std.HashMap Name (Name × String) := {}
  for (n, ci) in env.constants.map₁.toList do
    match modOf n with
    | some m =>
      if isTree m then
        let o := owner n
        if o == n then
          let k := match ci with
            | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind"
            | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | _ => "other"
          info := info.insert o (m, k)
        let mut ds := deps.getD o {}
        for d in ci.getUsedConstantsAsSet.toArray do
          match modOf d with
          | some md => if isTree md && owner d != o then ds := ds.insert (owner d)
          | none => pure ()
        deps := deps.insert o ds
    | none => pure ()
  let mut lines : Array String := #[]
  for (o, (m, k)) in info.toList do
    let r ← findDeclarationRanges? o
    let (a, b) := match r with
      | some rr => (rr.range.pos.line, rr.range.endPos.line)
      | none => (0, 0)
    let ds := (deps.getD o {}).toArray.map toString |>.qsort (· < ·)
    let reached := if reachedOwner.contains o then "1" else "0"
    lines := lines.push s!"{o}\t{m}\t{k}\t{a}\t{b}\t{reached}\t{",".intercalate ds.toList}"
  lines := lines.qsort (· < ·)
  let dest := (← IO.getEnv "REACH_OUT").getD "reach-decls.tsv"
  IO.FS.writeFile dest ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"reach: {lines.size} declarations of SIS.Tree, missing roots {missing.toList} -> {dest}"
