/-
The gate of the contract package (bergdb 030-15): the files a reader must
trust. `lake env lean Statements.lean` prints the source file of every
module that holds a main theorem or a declaration that the main theorems'
statements use, directly or through the definitions they use: the trusted
closure of the statements. gate.sh checks that each of these files is pinned
in statements.pin with its hash, so that a change of a statement, or of a
definition it rests on, shows in the pin file in review.

The main theorems are those of Axioms.lean, read from that file, but the
examples (a namespace with `Example` in its name): an example shows that a
statement is not vacuous; nobody trusts its definitions. The walk starts at
their types; from a definition it walks its type and its value, from an
inductive type its type and its constructors' types, from a constructor or a
recursor its inductive type, from a theorem its type only (the proof of a
theorem met in a definition is checked by Lean, not read). It stops at the
modules of Lean, Std, Batteries and Mathlib, which the toolchain and the
manifest pin (lean-toolchain, lake-manifest.json, pinned too).
-/
import Contract
import Lean

open Lean Elab Command

namespace Contract.Pins

/-- The modules whose declarations the walk does not enter. -/
def outside (m : Name) : Bool :=
  [`Init, `Std, `Lean, `Lake, `Batteries, `Mathlib, `Aesop, `Qq, `Plausible, `ProofWidgets,
   `ImportGraph, `LeanSearchClient].any (fun p => p.isPrefixOf m)

/-- The module of a declaration, if it is in an imported module. -/
def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map (fun i => env.header.moduleNames[i.toNat]!)

/-- The trusted closure from the roots: the modules met. -/
def closure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut mods : NameSet := {}
  let mut todo : List (Name × Bool) := roots.map (·, true)
  while true do
    match todo with
    | [] => break
    | (c, isRoot) :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      let some m := moduleOf env c | continue
      if outside m then continue
      let some info := env.find? c | continue
      let mut next : Array Name := info.type.getUsedConstants
      match info with
      | .thmInfo _ =>
        -- A theorem met in a definition: its statement is not trusted (Lean checks it).
        if !isRoot then continue
      | .defnInfo d => next := next ++ d.value.getUsedConstants
      | .opaqueInfo d => next := next ++ d.value.getUsedConstants
      | .inductInfo d =>
        for k in d.ctors do
          if let some ki := env.find? k then next := next ++ ki.type.getUsedConstants
      | .ctorInfo d => next := next.push d.induct
      | .recInfo d => next := next ++ d.all.toArray
      | _ => pure ()
      mods := mods.insert m
      todo := (next.toList.map (·, false)) ++ todo
  return mods

/-- The main theorems: the names of the `#print axioms` lines of Axioms.lean
but the examples. -/
def mainTheorems : CommandElabM (List Name) := do
  let text ← IO.FS.readFile "Axioms.lean"
  let mut names := []
  for line in text.splitOn "\n" do
    if let some rest := line.dropPrefix? "#print axioms " then
      let s := rest.toString.trimAscii.toString
      if (s.splitOn "Example").length > 1 then continue
      let n := s.toName
      let cands ← liftCoreM <| (do
        let r ← resolveGlobalConstNoOverload (mkIdent n)
        return [r]) <|> (do
        let r ← resolveGlobalConstNoOverload (mkIdent (`Contract ++ n))
        return [r])
      names := names ++ cands
  return names

/-- The source file of a module. -/
def fileOf (m : Name) : String :=
  let path := "/".intercalate (m.components.map (·.toString))
  if (`Contract).isPrefixOf m then s!"lean/contract/{path}.lean" else s!"lean/{path}.lean"

elab "#print_statement_files" : command => do
  let roots ← mainTheorems
  let env ← getEnv
  let mods := closure env roots
  let files := (mods.toList.map fileOf).toArray.qsort (· < ·)
  logInfo m!"{roots.length} main theorems; {files.size} files\n{"\n".intercalate files.toList}"

#print_statement_files

end Contract.Pins
