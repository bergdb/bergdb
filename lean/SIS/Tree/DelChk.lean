/-
The delete with checks (bergdb 024-22, step 4; the heights' walk): copies of
the writer's delete path (`putKv` to `merge`, `takeBack`, `collapseRoot`) with
a check where the writer takes a node back. The checks:

* before each take-back of the merge and of the upward delete's loop
  (`checkFree`): no kept node holds the node, now or before the transaction;
  it is not the space root and no node of the view;
* before the loop's retarget (`checkOld`): the parent is a segment leaf, and
  the node it is pointed to is a node of the view (not taken back);
* before root collapse takes a root back (`checkRoot`): its one holder is the
  path's node above it, by the path's klong; none before the transaction; it
  is not the space root unless at depth 0, and no node of the view;
* after the upward delete's loop (`checkPathFree`): the path's nodes above it
  are not taken back; its stop node is a segment leaf.

`OpDelChkOK` (HeightsChkRun.lean) is the named premise: a delete, from a state
that the transaction's earlier operations reach, runs as its copy with the
checks. It is checked on runs by a check outside the repository (DelChk.lean, 2026-11-13).
-/
import SIS.Tree.WriterHeightsMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- x's one holder is the path's node at depth - 1, by the path's klong at
depth; none before the transaction. -/
def holderAtB (c : Ctx) (w : W) (x : NodeId) (depth : Nat) : Bool :=
  w.nodes.all (fun q => w.taken.contains q.1 ||
    (q.2.live.all (fun e => e.2 != x ||
      (depth != 0 && (w.path[depth - 1]?.map (·.2)) == some q.1 &&
        w.path[depth]? == some (some e.1, x))) &&
      !((q.2.toPrev (c.i - 1)).live.any (fun e => e.2 == x))))

/-- The check before root collapse takes x back. -/
def checkRoot (x : NodeId) (depth : Nat) : M Unit := do
  let c ← read
  let w ← (MonadState.get : M W)
  if holderAtB c w x depth && (depth == 0 || w.top.rootKey != x) && (c.view x).isNone then pure ()
  else throw "check: the root taken back is held otherwise"

/-- The check before the upward delete's loop points the parent to `old`. -/
def checkOld (pn : KNode) (old : NodeId) : M Unit := do
  let c ← read
  if pn.leaf && (c.view old).isSome then pure ()
  else throw "check: the take-back's parent is no segment leaf, or the node it names is not of the view"

/-- The check after the upward delete's loop: the path's first n nodes are not
taken back. -/
def checkPathFree (n : Nat) : M Unit := do
  let w ← (MonadState.get : M W)
  if (w.path.take n).all (fun e => !w.taken.contains e.2) then pure ()
  else throw "check: a node of the path above the loop is taken back"

/-- `takeBack` with the checks. -/
def takeBackChk (x parent : NodeId) (cv : Nat) : M Unit := do
  let c ← read
  let pn ← getNode parent
  match (← replacedBy x), pn.linkIndex x cv with
  | some old, some _ =>
    if pn.lastTime != some c.i then
      throw s!"Bug: take back of key node {x} at {c.i}: no klong of tt to it"
    checkOld pn old
    retarget parent x old
    checkFree x
    takenBack x
    note "up.takeback"
  | _, _ => throw s!"Bug: take back of key node {x} at {c.i}: no node it replaces, or no klong to it"

/-- `collapseRoot` with the check before a take-back. -/
def collapseRootChk (key : Key) (segment : Nat) : Nat → M Unit
  | 0 => throw "bounds: root collapse went below the height bound"
  | fuel + 1 => do
    let c ← read
    let root ← descendToSegmentRoot key segment
    let n ← getNode root
    if n.leaf then return
    let made := n.firstTime == some c.i
    if made && (← replacedBy root).isNone then return
    match n.onlyLiveKlong with
    | none => return
    | some only =>
      if n.cv? only != some 0 then
        throw s!"Bug: root collapse at {c.i}: the one live klong of root {root} is not the empty key"
      let depth := (← pathSize) - 1
      if made then
        checkRoot root depth
        takeBackRoot root depth only
      else replaceRoot root depth only
      collapseRootChk key segment fuel

/-- `merge` with the checked tail. -/
def mergeChk (x : NodeId) (d : Nat) : M Nat := do
  let c ← read
  let tt := c.i
  let p ← pathNode (d - 1)
  let pn ← getNode p
  let xn ← getNode x
  let inner := !xn.leaf
  let cx ← klongAt d
  let (ix?, ia, ib) := mergeIdx pn cx
  let ix ← match ix? with
    | some ix => pure ix
    | none => throw s!"Bug: merge at {tt}: key node {x} has no live klong {cx} in {p}"
  if pn.ptr? ix != some x then
    throw s!"Bug: merge at {tt}: key node {x} is not the live child of its klong in {p}"
  let left ← match ib with
    | some (ib, _) => do
      let (ls, lsn) ← sibling p pn ib inner
      if ia.isNone || lsn.cnt + xn.cnt ≤ c.p.mergeMax then pure (some (ib, ls, lsn))
      else pure none
    | none => pure none
  let (l, ln, il, r, rn, ir) ← match left with
    | some (ib, ls, lsn) => pure (ls, lsn, ib, x, xn, ix)
    | none =>
      match ia with
      | some (ia, _) => do
        let (rs, rsn) ← sibling p pn ia inner
        pure (x, xn, ix, rs, rsn, ia)
      | none => throw s!"Bug: merge at {tt}: key node {x} has no sibling in {p}"
  mergeTailChk c x d p pn xn left.isSome l ln il r rn ir

/-- `mergeUp` with the checked merge. -/
def mergeUpChk (key : Key) (g : Nat) : Nat → Nat → Bool → M Bool
  | 0, _, _ => throw "bounds: the merges went above the height bound"
  | f + 1, h, merged => do
    let c ← read
    let d ← descendToHeight key g h
    if d == 0 then return merged
    let x ← pathNode d
    let q ← pathNode (d - 1)
    if (← getNode q).leaf then return merged
    if (← getNode x).cnt ≥ c.p.mergeBelow then return merged
    let r ← mergeChk x d
    if r == 2 then return true
    mergeUpChk key g f (h + 1) true

/-- `afterDelete` with the checks. -/
def afterDeleteChk (key : Key) (g h : Nat) : M Unit := do
  let c ← read
  if c.p.merges then
    if ← mergeUpChk key g c.p.fuel h false then
      collapseRootChk key g c.p.fuel

/-- `deleteUpward` with the checks; its stop node a segment leaf. -/
def deleteUpwardChk (leaf : NodeId) (depth : Nat) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let tt := c.i
  let n ← getNode leaf
  let leafDel := n.lastBitmap
  let leafUnion := bitsUnion leafDel (n.bitsOf cv)
  if leafUnion == leafDel then return true
  if !n.allKeysIn leafUnion then
    let (g, h) ← ghOf leaf
    let _ ← appendDeleteKlong leaf depth cv
    afterDeleteChk key g h
    return false
  let stop ← climb depth
  if stop == depth then
    note "up.root-kept-empty"
    let _ ← appendDeleteKlong leaf depth cv
    return false
  note "up.climb"
  let path := (← (MonadState.get : M W)).path
  let _segment ← (path.take stop).foldlM (fun s (e : Option Nat × NodeId) => do
    pure (if (← getNode e.2).leaf then s + 1 else s)) 0
  for j in List.range (depth - stop) do
    let k := depth - j
    let x ← pathNode k
    let xn ← getNode x
    if xn.firstTime == some tt then takeBackChk x (← pathNode (k - 1)) (← klongAt k)
    else
      note "up.unlink"
      unlink x
  checkPathFree (stop + 1)
  let s ← pathNode stop
  let cs ← klongAt (stop + 1)
  let sn ← getNode s
  let (gs, hs) ← ghOf s
  if !sn.leaf then throw "check: the upward delete's stop node is no segment leaf"
  note "up.stop-at-segment-leaf"
  let _ ← appendDeleteKlong s stop cs
  afterDeleteChk key gs hs
  return false

/-- `setValue` for a delete, with the checks. -/
def setValueDelChk (segRoot : NodeId) (cv : Nat) (key : Key) : M Bool := do
  let c ← read
  let leaf ← descendLte cv c.p.fuel segRoot
  let noop ← deleteUpwardChk leaf ((← pathSize) - 1) cv key
  if !noop then
    let _ ← fresh
  pure noop

/-- `putSegs` for a delete, with the checks. -/
def putSegsDelChk (key : Key) : List Nat → NodeId → M Bool
  | [], _ => throw "corrupt: a key without segments"
  | [cv], segRoot => setValueDelChk segRoot cv key
  | cv :: rest, segRoot => do
    match ← setNode segRoot cv false with
    | none => pure true
    | some next => putSegsDelChk key rest next

/-- A delete with the checks. -/
def putKvDelChk (key : Key) : M Bool := do
  pathClear
  let root ← findRoot
  putSegsDelChk key key root

end SIS.Tree
