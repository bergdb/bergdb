import Lean
open Lean

/-!
005-10: the constants that each declaration of the SIS and Check libraries
uses, read from the compiled environment (the elaborated terms, so the
lemmas that `simp` or instance search chose are included).

Run from bergdb's lean/ directory after `lake build`:

    lake env lean --run LeanDeps.lean <out.tsv>

Each line: name, kind, module, and the used constants of the SIS and Check
modules, separated by spaces.
-/

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def valueOf : ConstantInfo → Option Expr
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | .opaqueInfo o => some o.value
  | _ => none

def ours (m : Name) : Bool :=
  let s := m.toString
  s == "SIS" || s == "Check" || s.startsWith "SIS." || s.startsWith "Check."

def main (args : List String) : IO Unit := do
  let out := args.head!
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `SIS}, {module := `Check}] {} (trustLevel := 1024)
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if !ours mod then continue
    let mut used : NameSet := ci.type.getUsedConstantsAsSet
    if let some v := valueOf ci then
      used := used.append v.getUsedConstantsAsSet
    if let .inductInfo i := ci then
      for c in i.ctors do
        used := used.insert c
    let mine := used.toList.filter fun u =>
      match env.getModuleIdxFor? u with
      | some j => ours env.header.moduleNames[j.toNat]! && u != n
      | none => false
    lines := lines.push s!"{n}\t{kindOf ci}\t{mod}\t{" ".intercalate (mine.map toString)}"
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")
  IO.println s!"{lines.size} constants"
