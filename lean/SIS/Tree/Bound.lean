/-
The tree model (bergdb 024-12, section 6): `Dag.dirtyNodeBound`, Java's upper
bound on the index nodes that a transaction can make dirty or create (bergdb
005-31; 023-07, section 5.4, K4), which `Db` uses before a transaction's go
point to refuse one whose dirty nodes would not fit a record. Trusted part: the
definition restates Java's count, step by step; that it is a bound is TP23
(`DirtyBoundOK`), not proved (bergdb 024-06, C3). Java's count was wrong three
times (024-01, LM2).
-/
import SIS.Tree.Props

namespace SIS.Tree

open SIS SIS.Check

/-- A node that the count walked (`Dag.Walked`): the node, the node above it on
the path (none for the space root), its depth, its size and whether it is a
segment leaf; the klongs it can get; the root collapses of its tree at most;
the keys whose segment `freshLevel` is not in it, by that segment. -/
structure Walked where
  x : NodeId
  up : Option NodeId
  depth : Nat
  size : Nat
  leaf : Bool
  klongs : Nat := 0
  collapses : Nat := 0
  fresh : List (Nat × List Key) := []
  freshLevel : Nat := 0
  deriving Repr, Inhabited

/-- The walked nodes, in the order they were first reached. -/
abbrev Walk := List Walked

def Walk.get? (ws : Walk) (x : NodeId) : Option Walked := ws.find? (fun w => w.x == x)

def Walk.modify (ws : Walk) (x : NodeId) (f : Walked → Walked) : Walk :=
  ws.map (fun w => if w.x == x then f w else w)

/-- `Dag.walked`: node x, reached from `up`, is walked. -/
def Walk.reach (ws : Walk) (x : NodeId) (n : KNode) (up : Option NodeId) : Walk :=
  if (ws.get? x).isSome then ws else
    let depth := match up.bind ws.get? with
      | some u => u.depth + 1
      | none => 0
    ws ++ [{ x := x, up := up, depth := depth, size := n.size, leaf := n.leaf }]

/-- `Dag.overflows`: how many times a node of `size` klongs, given `klongs`
more and a time klong, can overflow. -/
def overflows (m klongs size : Nat) : Nat :=
  if klongs == 0 then 0 else
    let k := klongs + 1
    let room := m - 2 - size
    if k ≤ room then 0 else 1 + (k - room - 1) / (max 2 (m / 2 - 3))

/-- The splits of a new tree's nodes, level by level: the loop
`for (ov = overflows(klongs, 0); ov > 0; ov = overflows(ov, 1)) count += ov + 1`. -/
def freshSplits (m : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, ov => if ov == 0 then 0 else ov + 1 + freshSplits m f (overflows m ov 1)

/-- `Dag.freshTreeBound`: the nodes of the new segment trees of `keys`, which
share their segments before `level` and whose segment `level` is in a new tree. -/
def freshTreeBound (m : Nat) : Nat → List Key → Nat → Nat
  | 0, _, _ => 0
  | f + 1, keys, level =>
    let r := keys.foldl (fun (acc : Nat × List (Nat × List Key)) key =>
      if key.length == level + 1 then (acc.1 + 1, acc.2) else
        match key[level]? with
        | some c =>
          if acc.2.any (fun q => q.1 == c) then
            (acc.1, acc.2.map (fun q => if q.1 == c then (c, q.2 ++ [key]) else q))
          else (acc.1 + 1, acc.2 ++ [(c, [key])])
        | none => acc) (0, [])
    let ov := overflows m r.1 0
    1 + freshSplits m (ov + 1) ov +
      (r.2.map (fun q => freshTreeBound m f q.2 (level + 1))).foldl (· + ·) 0

/-- The climb of a delete in the count: two klongs for every node from x up to
the space root, and for each segment tree on the way the number of its inner
nodes on the path, as the collapses of its root. -/
def markDelete : Nat → Walk → Option NodeId → Option NodeId → Nat → Walk
  | 0, ws, _, _, _ => ws
  | f + 1, ws, cur, below, inner =>
    match cur.bind ws.get? with
    | none => ws
    | some u =>
      let ws := ws.modify u.x (fun w => { w with klongs := w.klongs + 2 })
      if u.leaf then
        let ws := match below with
          | some b => ws.modify b (fun w => { w with collapses := max w.collapses inner })
          | none => ws
        markDelete f ws u.up (some u.x) 0
      else markDelete f ws u.up (some u.x) (inner + 1)

/-- The descent of the count in one segment tree: from node x by `searchLte` to
the segment leaf, each node walked; it ends above the leaf where no klong is at
or below the segment (as Java's loop). Returns the walk and the node reached. -/
def boundDescend (p : Params) (view : View BVal) (t : Time) (cv : Nat) :
    Nat → Walk → NodeId → Walk × NodeId
  | 0, ws, x => (ws, x)
  | f + 1, ws, x =>
    match knodeOf p view x with
    | none => (ws, x)
    | some n =>
      if n.leaf then (ws, x) else
        match n.searchLte t cv with
        | none => (ws, x)
        | some fd =>
          match knodeOf p view fd.y with
          | some ny => boundDescend p view t cv f (ws.reach fd.y ny (some x)) fd.y
          | none => (ws, x)

/-- The walk of one key in the count: the loop of `dirtyNodeBound` over the
key's segments from index i, at node x. Returns the walk and whether the key is
a delete that reached its last segment. -/
def boundKey (p : Params) (view : View BVal) (t : Time) (key : Key) (isDel : Bool) :
    List Nat → Nat → Walk → NodeId → Walk × Bool
  | [], _, ws, _ => (ws, false)
  | cv :: rest, i, ws, x =>
    let (ws, x) := boundDescend p view t cv p.fuel ws x
    match rest with
    | [] =>
      if isDel then (markDelete (ws.length + 1) ws (some x) none 0, true)
      else (ws.modify x (fun w => { w with klongs := w.klongs + 1 }), false)
    | _ :: _ =>
      match (knodeOf p view x).bind (fun n => n.searchEq t cv) with
      | none =>
        if isDel then (ws, false) else
          (ws.modify x (fun w =>
            let w := if w.fresh.isEmpty then { w with freshLevel := i } else w
            if w.fresh.any (fun q => q.1 == cv) then
              { w with fresh := w.fresh.map (fun q => if q.1 == cv then (cv, q.2 ++ [key]) else q) }
            else { w with fresh := w.fresh ++ [(cv, [key])], klongs := w.klongs + 1 }), false)
      | some fd =>
        match knodeOf p view fd.y with
        | some ny => boundKey p view t key isDel rest (i + 1) (ws.reach fd.y ny (some x)) fd.y
        | none => (ws, false)

/-- `Dag.dirtyNodeBound`: an upper bound on the key nodes that a transaction
with these operations, at a later time, can make dirty or create, from the tree
at time t: the nodes on the paths of the keys, the nodes that splits can make
(counted from the klongs each node can get and the room it has), the new
segment trees, and for a delete two klongs in every node of its path and the
collapses of the roots above it. -/
def dirtyNodeBound (p : Params) (view : View BVal) (t : Time) (ops : List Op) : Nat :=
  match rootAt view t with
  | none => 0
  | some r =>
    match knodeOf p view r with
    | none => 0
    | some rn =>
      -- The space root is walked for each key, as in Java's loop: a transaction
      -- without operations walks no node, and its bound is 0.
      let st := ops.foldl (fun (acc : Walk × Bool) op =>
        let isDel := match op with
          | .del _ => true
          | .put _ _ => false
        let res := boundKey p view t op.key isDel op.key 0 (Walk.reach acc.1 r rn none) r
        (res.1, acc.2 || res.2)) (([] : Walk), false)
      let ws := if st.2 then
          st.1.foldl (fun (ws : Walk) w => match w.up with
            | some u => ws.modify u (fun v => { v with klongs := v.klongs + w.collapses })
            | none => ws) st.1
        else st.1
      let order := (ws.mergeSort (fun a b => decide (b.depth ≤ a.depth))).map (·.x)
      (order.foldl (fun (acc : Walk × Nat) x =>
        match acc.1.get? x with
        | none => acc
        | some w =>
          let count := acc.2 + (w.fresh.map (fun q =>
            freshTreeBound p.M (p.G + 2) q.2 (w.freshLevel + 1))).foldl (· + ·) 0
          let ov := overflows p.M w.klongs w.size
          if ov == 0 then (acc.1, count) else
            match w.up with
            | some u => (acc.1.modify u (fun v => { v with klongs := v.klongs + ov + 1 }), count + ov + 1)
            | none => (acc.1, count + ov + 1 + ov)) (ws, ws.length)).2

/-- The key nodes of the tree at time t that have a node of `changed` at or
below them: the nodes that the model's `marked` marks (the access path of the
change), counted by one walk from node x. Returns the count and whether x's
subtree holds a changed node. -/
def markedBelow (p : Params) (view : View BVal) (t : Time) (changed : List NodeId) :
    Nat → NodeId → Nat × Bool
  | 0, _ => (0, false)
  | f + 1, x =>
    match knodeOf p view x with
    | none => (0, false)
    | some n =>
      let below := (n.liveAt t).foldl (fun (acc : Nat × Bool) (q : Nat × NodeId) =>
        if n.leaf && segLen q.1 != 7 then (acc.1, acc.2 || changed.contains q.2) else
          let r := markedBelow p view t changed f q.2
          (acc.1 + r.1, acc.2 || r.2)) (0, false)
      let hit := below.2 || changed.contains x
      (below.1 + (if hit then 1 else 0), hit)

/-- The key nodes that the change c at time i marks, on P with c applied. -/
def markedKeyNodes (p : Params) (after : View BVal) (i : Time) (c : Changes BVal) : Nat :=
  match rootAt after i with
  | some r => (markedBelow p after i (c.new.map (·.id) ++ c.adds.map (·.1)) p.fuel r).1
  | none => 0

/-- TP23 (bergdb 024-06, C3). `dirtyNodeBound` is a bound: the key nodes that a
transaction marks (the nodes on the access path of its change, the nodes it
makes among them) are at most Java's count on the tree before it. -/
def DirtyBoundOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ (tx : Tx) (c : Changes BVal), tx.sorted = true → tx.wf = true →
    exec? p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok c →
    markedKeyNodes p (viewOf ((treeRun p ts).apply (ts.length + 1) c)) (ts.length + 1) c ≤
      dirtyNodeBound p (viewOf (treeRun p ts)) ts.length tx.ops

/-! ## The user's limits (bergdb 024-17) -/

/-- The limits of a transaction that a user is given (bergdb 024-17, in
discussion on 2026-11-11): the most operations, and the most segments of a key
(a key of b bytes has b / 7 + 1). -/
structure Limits where
  maxOps : Nat
  maxSegs : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A transaction is within the limits. -/
def Tx.within (lim : Limits) (tx : Tx) : Bool :=
  decide (tx.ops.length ≤ lim.maxOps) &&
    tx.ops.all (fun op => decide (op.key.length ≤ lim.maxSegs))

/-- The index nodes that a transaction within the limits can make dirty or
create, from the limits and the tree's height bound alone: for each operation
its path (at most H + 1 key nodes in each of its key's segment trees), eight
times over, for the nodes walked, their splits and the splits above them, a
delete's klongs and collapses, and the new segment trees. The constant is
generous; the runs measure far less. -/
def Limits.dirtyNodes (p : Params) (lim : Limits) : Nat :=
  lim.maxOps * (8 * lim.maxSegs * (p.H + 2) + 2)

/-- TP26 (bergdb 024-17). The user's limits bound a transaction's index nodes:
`dirtyNodeBound` of a transaction within the limits is at most
`Limits.dirtyNodes`. With TP23 the key nodes that a transaction marks, and so
the bytes of its record's index part (each node at most M klongs), are bounded
by the limits, the node size and the height bound, whatever the database
holds. -/
def DirtyBoundFromLimits (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ (lim : Limits) (tx : Tx), tx.within lim = true →
    dirtyNodeBound p (viewOf (treeRun p ts)) ts.length tx.ops ≤ lim.dirtyNodes p

end SIS.Tree
