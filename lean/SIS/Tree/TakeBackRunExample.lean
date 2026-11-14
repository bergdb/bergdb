/-
The premises of the take-back's induction (TakeBackRun.lean) hold on runs
within reach (bergdb 024-12, TP4): Bool forms of (A) `ReachedFree`, (B) at
every state between operations, (C) `DeadTakenLive` and the
take-back (`TakeBackEnd`) at the last state, computed on transactions that
take nodes back (the trail names the rules that ran).
-/
import SIS.Tree.TakeBackRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The nodes reached from r in `f` rounds of live links. -/
def tbReach (N : NodeId → Option KNode) (t : Time) (r : NodeId) : Nat → List NodeId
  | 0 => [r]
  | f + 1 =>
    let s := tbReach N t r f
    s ++ ((s.flatMap (fun x => match N x with
      | some n => (n.liveAt t).map (·.2)
      | none => [])).eraseDups.filter (fun y => !s.contains y))

/-- (A) and (B) as a Bool, over the overlay's nodes and P's: (B) as
TakeBackRun.lean states it and as `TtReachedN` (TakeBackRunT.lean). -/
def tbInvB (p : Params) (P : Struct BVal) (t : Time) (B : NodeId) (w : W) : Bool :=
  let N := wNode p (viewOf P) w
  let rs := tbReach N t w.top.rootKey 40
  rs.all (fun y => !w.taken.contains y) &&
  (w.nodes.map (·.1) ++ P.map (·.1)).all (fun q => match N q with
    | some qn => (qn.liveAt t).all (fun cy => decide (cy.2 < B) || rs.contains q) &&
      (!qn.ks.contains (.time t) || rs.contains q)
    | none => true)

/-- `LastLive` as a Bool. -/
def tbLastLiveB (ks : List Klong) (del : List Nat) (i cv : Nat) : Bool :=
  !del.contains i && ks.zipIdx.all (fun kj => decide (kj.2 ≤ i) || match kj.1 with
    | .key c _ => c != cv || del.contains kj.2
    | _ => true)

/-- (C) in `DeadLive`'s form (TakeBackDead.lean) as a Bool, over the overlay's
nodes (P's name nodes below B): a klong of a kept node to a node at or above B
that is no value comes with a live one to it, and in a segment leaf is the last
live klong of its compare value. -/
def tbDeadLiveB (B : NodeId) (t : Time) (w : W) : Bool :=
  w.nodes.all (fun q => w.taken.contains q.1 || q.2.ks.zipIdx.all (fun ki => match ki.1 with
    | .key cv y => decide (y < B) || (w.vals.map (·.1)).contains y ||
        ((q.2.liveAt t).any (·.2 == y) && (!q.2.leaf || tbLastLiveB q.2.ks q.2.lastBitmap ki.2 cv))
    | _ => true))

/-- (C) as a Bool. -/
def tbDeadB (t : Time) (w : W) : Bool :=
  w.nodes.all (fun q => w.taken.contains q.1 || q.2.ks.all (fun k => match k with
    | .key _ y => !w.taken.contains y || (q.2.liveAt t).any (·.2 == y)
    | _ => true))

/-- `TakeBackEnd` as a Bool. -/
def tbEndB (w : W) : Bool :=
  w.nodes.all (fun q => w.taken.contains q.1 || q.2.ks.all (fun k => match k with
    | .key _ y => !w.taken.contains y
    | _ => true)) && !w.taken.contains w.top.rootKey

/-- The checks on transaction tx after ts: (A), (B) and `DeadLive` at every state
between operations, (C) and the take-back at the last, the nodes taken back and the
rules that ran. -/
def tbCheck (p : Params) (ts : List Tx) (tx : Tx) :
    Except String (List Bool × Bool × Bool × List NodeId × List String) := do
  let P := treeRun p ts
  let v := view (treeSpec p) P ts.length
  let some z := lastTop v | throw "no top"
  let c := ctxOf p ts
  let top ← topOf p c.view z
  let invs ← (List.range (tx.ops.length + 1)).mapM (fun k => do
    let (_, w) ← ((tx.ops.take k).mapM putKv) c (wInit tx top)
    pure (tbInvB p P (ts.length + 1) tx.base w && tbDeadLiveB tx.base (ts.length + 1) w))
  let (_, w) ← (tx.ops.mapM putKv) c (wInit tx top)
  pure (invs, tbDeadB (ts.length + 1) w, tbEndB w, w.taken, w.trail.eraseDups)

/-- The writer's tree (`TreeOK`) as a Bool: no live link of a reached node to
the root, one live link at most to every node from the reached nodes. -/
def tbTreeB (p : Params) (P : Struct BVal) (t : Time) (w : W) : Bool :=
  let N := wNode p (viewOf P) w
  let rs := tbReach N t w.top.rootKey 40
  let ys := rs.flatMap (fun x => match N x with
    | some n => (n.liveAt t).map (·.2)
    | none => [])
  (N w.top.rootKey).isSome && !ys.contains w.top.rootKey && ys.length == ys.eraseDups.length

/-- `tbCheck`'s result with the writer's tree at every state between
operations; every check true, a node taken back, and the rules given ran. -/
def tbOK (p : Params) (ts : List Tx) (tx : Tx) (rules : List String) : Bool :=
  let trees : Except String (List Bool) := do
    let P := treeRun p ts
    let v := view (treeSpec p) P ts.length
    let some z := lastTop v | throw "no top"
    let c := ctxOf p ts
    let top ← topOf p c.view z
    (List.range (tx.ops.length + 1)).mapM (fun k => do
      let (_, w) ← ((tx.ops.take k).mapM putKv) c (wInit tx top)
      pure (tbTreeB p P (ts.length + 1) w))
  match tbCheck p ts tx, trees with
  | .ok (invs, d, e, tk, tr), .ok tb =>
    invs.all id && d && e && !tk.isEmpty && rules.all (tr.contains ·) && tb.all id
  | _, _ => false

/-- Merges with node size 8: two deletes merge two leaves made by a split in
the transaction (both taken back) and collapse the space root it made (taken
back): the run of MergeSortedExamples.lean, within reach there. -/
def tbP1 : Params := ({M := 8, G := 0, H := 0} : Params).withMerges
def tbKey (j : Nat) : Key := [64*j+8]
def tbPre1 : Tx := {base := 100, ops := (List.range 5).map (fun j => .put (tbKey j) 1)}
def tbTx1 : Tx := {base := 300, ops := [.del (tbKey 3), .del (tbKey 4)]}

#guard tbOK tbP1 [tbPre1] tbTx1 ["merge.takeback", "rc.takeback.space"]

/-- Two segments, node size 6, no merges: ten keys put into a segment and
deleted in the same transaction, then every key of the run before: the upward
delete takes back nodes made by splits, root collapse takes back a segment
root and the space root. -/
def tbP2 : Params := {M := 6, G := 1, H := 2}
def tbPre2 : Tx := {base := 100, ops := (List.range 12).map (fun j => .put [j % 3, 8*j+8] 1)}
def tbTx2 : Tx := {base := 400, ops := ((List.range 10).map (fun j => .put [1, 8*j+12] 1)) ++
  ((List.range 10).map (fun j => .del [1, 8*j+12])) ++
  ((List.range 12).map (fun j => .del [j % 3, 8*j+8]))}

#guard tbOK tbP2 [tbPre2] tbTx2 ["up.takeback", "rc.takeback.segment", "rc.takeback.space"]

/-- The dead klongs of kept overlay nodes to key nodes of the transaction, at
every state between operations: `DeadLive` is not void on the second run. -/
def tbDeadCount (p : Params) (ts : List Tx) (tx : Tx) : Except String (List Nat) := do
  let P := treeRun p ts
  let v := view (treeSpec p) P ts.length
  let some z := lastTop v | throw "no top"
  let c := ctxOf p ts
  let top ← topOf p c.view z
  (List.range (tx.ops.length + 1)).mapM (fun k => do
    let (_, w) ← ((tx.ops.take k).mapM putKv) c (wInit tx top)
    pure (w.nodes.foldl (fun acc q => if w.taken.contains q.1 then acc else
      acc + (q.2.ks.filter (fun k => match k with
        | .key cv y => !(w.vals.map (·.1)).contains y && decide (tx.base ≤ y) &&
            !((q.2.liveAt (ts.length + 1)).contains (cv, y))
        | _ => false)).length) 0))

#guard (match tbDeadCount tbP2 [tbPre2] tbTx2 with
  | .ok l => l.any (fun n => decide (0 < n))
  | .error _ => false)

end SIS.Tree
