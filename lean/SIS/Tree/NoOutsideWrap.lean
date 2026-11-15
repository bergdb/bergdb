/-
The wrapper command of 025-03 (`n_wrap`, NoOutsideBase.lean): for a lemma of
the run machinery with no hypothesis over runs, its form in `SIS.Tree.N`: a
hypothesis `Within p ts` becomes `N.Within p ts` (passed on as its `w`), and a
conclusion that is a definition restated in N (or a conjunction of such) is
given in N's form (its `ofOld`). Nothing is assumed: each wrapper is a theorem
whose proof applies the lemma.
-/
import Lean

open Lean Meta Elab Command

namespace SIS.Tree.NWrap

/-- The definitions restated in N: old name ↦ N name. -/
def nOf (env : Environment) (n : Name) : Option Name :=
  if (`SIS.Tree).isPrefixOf n && !(`SIS.Tree.N).isPrefixOf n then
    let m := n.replacePrefix `SIS.Tree `SIS.Tree.N
    if env.contains m && env.contains (m ++ `ofOld) then some m else none
  else none

def isWithin (e : Expr) : Bool := e.getAppFn.isConstOf `SIS.Tree.Within

/-- Mentions `Within` or a definition restated in N. -/
def mentionsRun (env : Environment) (e : Expr) : Bool :=
  e.getUsedConstants.any (fun c => c == `SIS.Tree.Within || (nOf env c).isSome)

/-- The new type: `Within` binders to `N.Within`, the conclusion to N's form;
none if a binder mentions runs otherwise (a lemma over runs) or nothing
changes. -/
partial def newType (env : Environment) (e : Expr) : Option (Expr × Bool) :=
  match e with
  | .forallE n t b bi =>
    match newType env b with
    | none => none
    | some (b', ch) =>
      if isWithin t then some (.forallE n (mkAppN (mkConst `SIS.Tree.N.Within) t.getAppArgs) b' bi, true)
      else if mentionsRun env t then none
      else some (.forallE n t b' bi, ch)
  | c =>
    match convConcl env c with
    | some c' => some (c', true)
    | none => if mentionsRun env c then none else some (c, false)
where
  convConcl (env : Environment) (c : Expr) : Option Expr :=
    if c.isAppOfArity ``And 2 then
      let a := c.getArg! 0; let b := c.getArg! 1
      let a' := (convConcl env a).getD a
      let b' := (convConcl env b).getD b
      if (convConcl env a).isNone && (convConcl env b).isNone then none
      else if (convConcl env a).isNone && mentionsRun env a then none
      else if (convConcl env b).isNone && mentionsRun env b then none
      else some (mkApp2 (mkConst ``And) a' b')
    else match c.getAppFn with
      | .const d ls => (nOf env d).map (fun m => mkAppN (mkConst m ls) c.getAppArgs)
      | _ => none

/-- A proof of the converted conclusion from one of the old. -/
partial def convProof (env : Environment) (c : Expr) (h : Expr) : MetaM Expr := do
  if c.isAppOfArity ``And 2 then
    let a := c.getArg! 0; let b := c.getArg! 1
    let pa ← convProof env a (← mkAppM ``And.left #[h])
    let pb ← convProof env b (← mkAppM ``And.right #[h])
    mkAppM ``And.intro #[pa, pb]
  else match c.getAppFn with
    | .const d _ =>
      match nOf env d with
      | some m => mkAppM (m ++ `ofOld) #[h]
      | none => pure h
    | _ => pure h

def wrapOne (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some ci := env.find? n | return false
  unless ci matches .thmInfo _ do return false
  let m := n.replacePrefix `SIS.Tree `SIS.Tree.N
  if env.contains m then return false
  let some (ty', true) := newType env ci.type | return false
  let lvls := ci.levelParams.map mkLevelParam
  let val ← forallTelescope ty' fun xs _ => do
    let mut args : Array Expr := #[]
    for x in xs do
      let t ← inferType x
      if t.getAppFn.isConstOf `SIS.Tree.N.Within then args := args.push (← mkAppM `SIS.Tree.N.Within.w #[x])
      else args := args.push x
    let body := mkAppN (mkConst n lvls) args
    let bt ← inferType body
    let p ← convProof env bt body
    mkLambdaFVars xs p
  addDecl (.thmDecl { name := m, levelParams := ci.levelParams, type := ty', value := val })
  return true

/-- The lemmas that the values of `srcs` use and that have a form in N. -/
def wrapFor (srcs : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut todo : Std.HashSet Name := {}
  for s in srcs do
    match env.find? s with
    | some (.thmInfo v) => for c in v.value.getUsedConstants ++ v.type.getUsedConstants do todo := todo.insert c
    | _ => pure ()
  let mut done : Array Name := #[]
  for c in todo.toArray.qsort (fun a b => a.toString < b.toString) do
    if (`SIS.Tree).isPrefixOf c && !(`SIS.Tree.N).isPrefixOf c && !srcs.contains c then
      if ← wrapOne c then done := done.push c
  return done

elab "n_wrap " xs:ident* : command => do
  let names ← xs.mapM (fun x => liftCoreM (realizeGlobalConstNoOverloadWithInfo x))
  let done ← liftTermElabM (wrapFor names)
  logInfo m!"n_wrap: {done.size} wrappers"

/-- The wrappers of the named lemmas themselves (`n_wrap` wraps the lemmas that
the named declarations use). -/
elab "n_wrap_these " xs:ident* : command => do
  let names ← xs.mapM (fun x => liftCoreM (realizeGlobalConstNoOverloadWithInfo x))
  let done ← liftTermElabM do
    let mut d : Array Name := #[]
    for n in names do
      if ← wrapOne n then d := d.push n
    return d
  logInfo m!"n_wrap_these: {done.size} wrappers"

end SIS.Tree.NWrap
