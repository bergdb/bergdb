/-
The tree checker, the whole run (bergdb 024-12, section 5.5): the model's
`init` and `step` (SIS/Algorithm.lean), with the tree's `exec`
(since record format 8 PE's, SIS/Tree/Pe.lean; until then SIS/Tree/Spec.lean's) for the change of every transaction, run from R(0) over a
trace's transactions; its records and D compared with Java's. The model then
has, of Java's run, only the operations of each transaction, the id of the
first node it makes, the startup pos Java chose and the first available time:
the nodes, the entries, the versions written, their references, gd and D are
the model's own. Not part of the trusted part.

The trace checker's C-S (TraceCheck.lean) runs `step` on Java's state before
each transaction, with the change that the trace gives; this check never takes
Java's state.
-/
import Check.Tree
import Check.Steps

namespace SIS.Check.Tree

open SIS SIS.Check SIS.Tree

/-- The key nodes that a trace makes without an entry (024-12, D4), each with
the record that makes it: they have the marker entry in the model's P, and so
in every version of theirs. -/
def markerNodes (p : Params) (recs : Array TRec) : Std.HashMap NodeId Nat :=
  recs.foldl (fun (m : Std.HashMap NodeId Nat) r =>
    r.new.foldl (fun (m : Std.HashMap NodeId Nat) (x, l, d) =>
      if !d && x != root && l ≤ p.keyMax && !r.adds.any (fun a => a.1 == x) then m.insert x r.idx
      else m) m) {}

/-- A record of the trace as the model's, the versions of the marker nodes with
their marker entry. -/
def toRecordM (mk : Std.HashMap NodeId Nat) (lv : List (NodeId × Nat × Bool)) (fa : Nat)
    (r : TRec) : Record BVal Nat :=
  let rec0 := toRecord lv fa r
  { rec0 with vers := rec0.vers.map (fun w =>
      match mk[w.node]? with
      | some t => { w with hist := ⟨t, marker⟩ :: w.hist }
      | none => w) }

/-- The transactions of a trace for the tree's `exec`, by record index: the
operations that changed the tree (a noop is not part of a transaction), the
first id, and for a transaction with a TOUCH line (a reclaim step) the keys
whose paths it touches: all its keys. -/
def txsOf (recs : Array TRec) (tt : TTrace) : Array Tx :=
  tt.txs.map (fun x =>
    { base := x.base.getD 0,
      ops := (x.ops.toList.filter (fun q => !q.2)).map (·.1),
      touch := if (recs.getD x.idx default).touch.isEmpty then []
        else x.ops.toList.map (·.1.key) })

/-- The whole run: the failures, each with its transaction, and the number of
records compared. -/
def wholeRun (p : Params) (tr : Trace) (tt : TTrace) : List String × Nat := Id.run do
  let recs := tr.recs
  let lv := levelMap tr
  let fas := faSeq recs
  let mk := markerNodes p recs
  let jrecs := (recs.toList.zipIdx.map (fun (r, i) => toRecordM mk lv (fas.getD i 0) r)).toArray
  let txs := txsOf recs tt
  -- R(0): Java's primordial structure, its key node with the marker.
  let c0 := changesOf (recs.getD 0 default)
  let m0 := (c0.new.filter (fun n => mk.contains n.id)).map (fun n => (n.id, marker))
  let p0 := Struct.apply (V := BVal) [] 0 { c0 with adds := c0.adds ++ m0 }
  let base : Spec BVal Nat :=
    { ptrs := bptrs, live := blive, exec := fun _ _ _ => { new := [], adds := [] }, init := p0,
      virt := true, topLevel := topLevelOf p0, rootVal := .top }
  let pol := fun (j : Nat) => (recs.getD j default).sp
  let al := algoOf base {} pol (fun j => fas.getD j 0)
  let mut db := init base
  let mut fails : List String :=
    if p0 == initStruct p then [] else ["R(0): Java's primordial structure is not the model's `initStruct`"]
  match db.S.getLast?, jrecs[0]? with
  | some m, some j => fails := fails ++ (diffRecord m j).map (fun d => s!"R(0): {d.2}")
  | _, _ => fails := fails ++ ["R(0): no record"]
  for i in [1:recs.size] do
    let r := recs.getD i default
    -- The tree's change, from the model's own P (as P@(i-1): TP19).
    let pm := SIS.Fast.nodeMap db.P
    let c := SIS.Tree.Pe.exec p (txs.getD i default) i (fun x => pm[x]?)
    let spi : Spec BVal Nat := { base with exec := fun _ _ _ => c }
    db := step spi al db i
    match db.S.getLast?, jrecs[i]? with
    | some m, some j => fails := fails ++ (diffRecord m j).map (fun d => s!"R({i}): {d.2}")
    | _, _ => fails := fails ++ [s!"R({i}): no record"]
    if !sameList db.D r.dirty then
      fails := fails ++ [s!"R({i}): D: model only {(db.D.filter (!r.dirty.contains ·)).take 8}, Java only {(r.dirty.filter (!db.D.contains ·)).take 8}"]
    if fails.length > 40 then
      return (fails, i)
  return (fails, recs.size)

end SIS.Check.Tree
