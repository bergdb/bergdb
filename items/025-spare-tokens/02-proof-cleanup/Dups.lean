/-
025-02 tool (2026-11-14): theorems of ours with the same statement (equal type, binder
names aside). Run from lean/ after `lake build`:
  DUPS_OUT=dups.txt lake env lean /Users/f/fl/bench/2026-11-14/cleanup/tools/Dups.lean
One group a line: "DUP hash n: name@module:start-end ...", and a total of the lines that
would go if each group kept one member.
-/
import Lean
import SIS
import Check
import BergDB
import SIS.Tree.MergeProofBundle

open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map (fun i => mods[i.toNat]!)
  let ours (m : Name) : Bool := (`SIS).isPrefixOf m || (`Check).isPrefixOf m || (`BergDB).isPrefixOf m
  let mut groups : Std.HashMap UInt64 (Array Name) := {}
  for (n, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      if let some m := modOf n then
        if ours m && !n.isInternal then
          let s := n.toString
          if !((s.splitOn ".proof_").length > 1 || (s.splitOn ".eq_").length > 1 || (s.splitOn "._").length > 1) then
            let h := ci.type.hash
            groups := groups.insert h ((groups.getD h #[]).push n)
  let mut out : Array String := #[]
  let mut save := 0
  for (h, ns) in groups.toList do
    if ns.size > 1 then
      let mut parts : Array String := #[]
      let mut sizes : Array Nat := #[]
      for n in ns do
        let r ← findDeclarationRanges? n
        let (a, b) := match r with | some rr => (rr.range.pos.line, rr.range.endPos.line) | none => (0, 0)
        sizes := sizes.push (b - a + 1)
        parts := parts.push s!"{n}@{(modOf n).getD `none}:{a}-{b}"
      let mx := sizes.foldl max 0
      save := save + (sizes.foldl (· + ·) 0) - mx
      out := out.push s!"DUP {h} {ns.size}: {" ".intercalate parts.toList}"
  out := out.qsort (· < ·)
  out := out.push s!"TOTAL groups {out.size}, lines in the copies beyond the largest of each group {save}"
  let dest := (← IO.getEnv "DUPS_OUT").getD "dups.txt"
  IO.FS.writeFile dest ("\n".intercalate out.toList ++ "\n")
  IO.println s!"dups: {out.size - 1} groups, about {save} lines -> {dest}"
