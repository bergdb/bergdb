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
  /-- A delete's path goes through it (`Walked.deleteBelow`, record format 7,
  bergdb 024-21): a merge can replace it by a node of up to c + 1 klongs. -/
  deleteBelow : Bool := false
  /-- Its dead key klongs as walked (option 2, bergdb 024-23, 2.6;
  `Walked.dead`). -/
  dead : Nat := 0
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
    ws ++ [{ x := x, up := up, depth := depth, size := n.size, leaf := n.leaf,
             dead := n.deadCount }]

/-- `Dag.roomAfterReplacement`: the room for more klongs that a node made by
rule O or by a merge has at least, less a margin of 3, and at least 2: max(2,
min(M / 2, M - h, M - c) - 3) (record format 7, bergdb 024-21 with 024-14's
thresholds; 10 at node size 30). Without merges (c = 0, h = M / 2) it is
2026.4's max(2, M / 2 - 3). -/
def Params.roomAfterReplacement (p : Params) : Nat :=
  max 2 (min (p.M / 2) (min (p.M - p.splitAbove) (p.M - p.mergeMax)) - 3)

/-- `Dag.overflows`: how many times a node of `size` klongs, given `klongs`
more and a time klong, can overflow, in a node size m with q, the room after a
replacement (`roomAfterReplacement`). `merged` (record format 7, bergdb
024-21): a delete's path goes through the node, so a merge can replace it by a
node of up to c + 1 klongs, with at most q of room. `theta` and `dead` (option
2, bergdb 024-23, 2.6): a node of `dead` dead klongs that gets more klongs than
theta - dead can be compacted, once, by a new node and a klong in its parent:
at least one overflow then. Its replacement has no fewer klongs of room than
the node would have, and later compactions in the transaction are in place. -/
def overflows (m q klongs size : Nat) (merged : Bool := false) (theta dead : Nat := 0) : Nat :=
  if klongs == 0 then 0 else
    let k := klongs + 1
    let room := if merged then min (m - 2 - size) q else m - 2 - size
    let ov := if k ≤ room then 0 else 1 + (k - room - 1) / q
    if theta != 0 && decide (theta < dead + klongs) then max ov 1 else ov

/-- The splits of a new tree's nodes, level by level: the loop
`for (ov = overflows(klongs, 0); ov > 0; ov = overflows(ov, 1)) count += ov + 1`. -/
def freshSplits (m q : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, ov => if ov == 0 then 0 else ov + 1 + freshSplits m q f (overflows m q ov 1)

/-- `Dag.freshTreeBound`: the nodes of the new segment trees of `keys`, which
share their segments before `level` and whose segment `level` is in a new tree. -/
def freshTreeBound (m q : Nat) : Nat → List Key → Nat → Nat
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
    let ov := overflows m q r.1 0
    1 + freshSplits m q (ov + 1) ov +
      (r.2.map (fun e => freshTreeBound m q f e.2 (level + 1))).foldl (· + ·) 0

/-- The climb of a delete in the count: `add` klongs for every node from x up
to the space root (two; four with the merges of record format 7, bergdb
024-21, which also mark each node `deleteBelow`), and for each segment tree on
the way the number of its inner nodes on the path, as the collapses of its
root. -/
def markDelete (add : Nat) (merges : Bool) : Nat → Walk → Option NodeId → Option NodeId → Nat → Walk
  | 0, ws, _, _, _ => ws
  | f + 1, ws, cur, below, inner =>
    match cur.bind ws.get? with
    | none => ws
    | some u =>
      let ws := ws.modify u.x (fun w => { w with klongs := w.klongs + add,
                                                 deleteBelow := w.deleteBelow || merges })
      if u.leaf then
        let ws := match below with
          | some b => ws.modify b (fun w => { w with collapses := max w.collapses inner })
          | none => ws
        markDelete add merges f ws u.up (some u.x) 0
      else markDelete add merges f ws u.up (some u.x) (inner + 1)

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
key's segments from index i, at node x. Returns the walk and, for a delete that
reached its last segment, the depth of the node it reached there. -/
def boundKey (p : Params) (view : View BVal) (t : Time) (key : Key) (isDel : Bool) :
    List Nat → Nat → Walk → NodeId → Walk × Option Nat
  | [], _, ws, _ => (ws, none)
  | cv :: rest, i, ws, x =>
    let (ws, x) := boundDescend p view t cv p.fuel ws x
    match rest with
    | [] =>
      if isDel then
        (markDelete (if p.format7 then 4 else 2) p.format7 (ws.length + 1) ws (some x) none 0,
          some ((ws.get? x).map (·.depth) |>.getD 0))
      else (ws.modify x (fun w => { w with klongs := w.klongs + 1 }), none)
    | _ :: _ =>
      match (knodeOf p view x).bind (fun n => n.searchEq t cv) with
      | none =>
        if isDel then (ws, none) else
          (ws.modify x (fun w =>
            let w := if w.fresh.isEmpty then { w with freshLevel := i } else w
            if w.fresh.any (fun q => q.1 == cv) then
              { w with fresh := w.fresh.map (fun q => if q.1 == cv then (cv, q.2 ++ [key]) else q) }
            else { w with fresh := w.fresh ++ [(cv, [key])], klongs := w.klongs + 1 }), none)
      | some fd =>
        match knodeOf p view fd.y with
        | some ny => boundKey p view t key isDel rest (i + 1) (ws.reach fd.y ny (some x)) fd.y
        | none => (ws, none)

/-- `Dag.dirtyNodeBound`: an upper bound on the key nodes that a transaction
with these operations, at a later time, can make dirty or create, from the tree
at time t: the nodes on the paths of the keys, the nodes that splits can make
(counted from the klongs each node can get and the room it has), the new
segment trees, and for a delete two klongs in every node of its path and the
collapses of the roots above it. With the merges of record format 7 (bergdb
024-21, `Params.format7`): four klongs in every node of a delete's path, room
of at most q in a node on it (`overflows`' `merged`), and four nodes for each
level of the path and two levels more. With option 2 (bergdb 024-23, 2.6): a
node that its klongs can take above theta dead klongs overflows at least once. -/
def dirtyNodeBound (p : Params) (view : View BVal) (t : Time) (ops : List Op) : Nat :=
  match rootAt view t with
  | none => 0
  | some r =>
    match knodeOf p view r with
    | none => 0
    | some rn =>
      -- The space root is walked for each key, as in Java's loop: a transaction
      -- without operations walks no node, and its bound is 0.
      let st := ops.foldl (fun (acc : Walk × Bool × Nat) op =>
        let isDel := match op with
          | .del _ => true
          | .put _ _ => false
        let res := boundKey p view t op.key isDel op.key 0 (Walk.reach acc.1 r rn none) r
        (res.1, acc.2.1 || res.2.isSome, acc.2.2 + (res.2.map (· + 1 + 2)).getD 0))
        (([] : Walk), false, 0)
      let mergeLevels := st.2.2
      let st := (st.1, st.2.1)
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
            freshTreeBound p.M p.roomAfterReplacement (p.G + 2) q.2 (w.freshLevel + 1))).foldl
              (· + ·) 0
          let ov := overflows p.M p.roomAfterReplacement w.klongs w.size w.deleteBelow p.theta w.dead
          if ov == 0 then (acc.1, count) else
            match w.up with
            | some u => (acc.1.modify u (fun v => { v with klongs := v.klongs + ov + 1 }), count + ov + 1)
            | none => (acc.1, count + ov + 1 + ov)) (ws, ws.length)).2 +
        (if p.format7 && st.2 then 4 * mergeLevels else 0)

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

/-- The limits of a transaction that a user is given (bergdb 024-17, section 6;
decided by Frans on 2026-11-11, 17:41): the most operations (L1), the most
segments of a key (L2: a key of b bytes has b / 7 + 1, so 111 bytes are 16),
and the most segments of all the keys of a transaction together (from L3, the
key bytes of a transaction: k bytes of keys in n keys are at most k / 7 + n
segments). The last binds on BergDB's own longer keys, the Pub layer's index
entries, which pass L2 (024-17, 6.2 (a)); by default it is the most that the
other two allow. -/
structure Limits where
  maxOps : Nat
  maxSegs : Nat
  maxTxSegs : Nat := maxOps * maxSegs
  deriving Repr, DecidableEq, Inhabited

/-- The limits of release 2026.5 as the Core sees them (bergdb 024-17, section
8; Java's `Db` constants, 024-24): L1 = 500 operations, and L3 = 56 KiB =
57,344 bytes of keys a transaction, so 57,344 / 7 + 500 = 8,692 segments. A
user's key has at most L2 = 111 bytes, 16 segments (`Limits.user`), but
BergDB's own keys, the Pub layer's index entries, pass it and are bounded by L3
alone, so the longest key the Core takes is L3's (024-17, 6.2 (a)). -/
def Limits.release : Limits := { maxOps := 500, maxSegs := 57344 / 7 + 1, maxTxSegs := 57344 / 7 + 500 }

/-- The limits of release 2026.5 for a transaction of a user's keys alone:
L1 and L2 (111 bytes, 16 segments); L3 does not bind (500 x 111 = 55,500 bytes,
under 57,344). -/
def Limits.user : Limits := { maxOps := 500, maxSegs := 111 / 7 + 1 }

/-- A transaction is within the limits. -/
def Tx.within (lim : Limits) (tx : Tx) : Bool :=
  decide (tx.ops.length ≤ lim.maxOps) &&
    tx.ops.all (fun op => decide (op.key.length ≤ lim.maxSegs)) &&
    decide ((tx.ops.map (·.key.length)).foldl (· + ·) 0 ≤ lim.maxTxSegs)

/-- The segments of a transaction within the limits, at most: the sum's limit
or every operation at the longest key, the smaller. -/
def Limits.segments (lim : Limits) : Nat := min lim.maxTxSegs (lim.maxOps * lim.maxSegs)

/-- The count with q (bergdb 024-17, 5.2 and 5.2a; QL8 (a)): the key nodes that
one level of an operation's path can dirty or create in record format 7. The
node itself, four for the merges, and its overflows: a node on a delete's path
gets four klongs, its overflows and one of the child below, and after a
replacement has at least q of room (`roomAfterReplacement`), so it overflows at
most x = 2 + (4 + x) / q times, x = 2 (q + 2) / (q - 1), rounded up. At q = 2
(node size 8, and the model's test sizes) one more, for the root collapses,
H / (q - 1) klongs a segment, which weigh there (024-17, 5.2a: Java's count of
one delete on a full path, 13,685 nodes at 16 segments and H = 61, is over 13 a
level). So 14 a level at node size 8, 9 at 14, 8 at 30 and 62. -/
def Params.nodesALevel (p : Params) : Nat :=
  let q := p.roomAfterReplacement
  5 + (3 * q + 2) / (q - 1) + (if q ≤ 2 then 1 else 0)

/-- The index nodes that a transaction within the limits can make dirty or
create, from the limits and the tree's height bound alone, as a sum over its
keys' segments: each segment tree on a key's path has at most H + 1 key nodes,
and the path two levels more for the merges and new roots. 2026.4's writer:
eight nodes a level of a segment (the nodes walked, their splits and the splits
above them, a delete's klongs and collapses, the new segment trees) and two an
operation. Record format 7 (bergdb 024-21, 024-22), restated with q for the
limits of 2026.5 (024-17, QL8 (a); 024-24): `nodesALevel` a level, and 14 an
operation (the merges' four nodes of the two levels more, the new roots). Until
then it was 20 a level with every operation at the longest key, which does not
cover 500 operations of 111-byte keys within a record (024-17, 5.2a). -/
def Limits.dirtyNodes (p : Params) (lim : Limits) : Nat :=
  if p.format7 then p.nodesALevel * (p.H + 2) * lim.segments + 14 * lim.maxOps
  else 8 * (p.H + 2) * lim.segments + 2 * lim.maxOps

/-- TP26 (bergdb 024-17). The user's limits bound a transaction's index nodes:
`dirtyNodeBound` of a transaction within the limits is at most
`Limits.dirtyNodes`. With TP23 the key nodes that a transaction marks, and so
the bytes of its record's index part (each node at most M klongs), are bounded
by the limits, the node size and the height bound, whatever the database
holds. Stated, not proved (bergdb 024-22, section 6); `treetest` and the
Java traces (C-T8, `treeconf.sh`) check it on every transaction, with the
transaction's own sizes as its limits. -/
def DirtyBoundFromLimits (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ (lim : Limits) (tx : Tx), tx.within lim = true →
    dirtyNodeBound p (viewOf (treeRun p ts)) ts.length tx.ops ≤ lim.dirtyNodes p

/-- The parameters of record format 7 with option 2 for node size M and
height bound H, as Java's writer has them (bergdb 024-21, 024-23). -/
def Params.java (M H : Nat) : Params := ({ M := M, G := 0, H := H } : Params).withMerges.withTheta

/-- The bytes of a key node of node size M at its largest, as
`Db.checkDirtyNodes` counts it: 32 + 16 (M + 1) + 16. -/
def nodeBytes (M : Nat) : Nat := 32 + 16 * (M + 1) + 16

/-- L8 at the limits of 2026.5 (bergdb 024-17, 5.2a and 5.3): with the count
with q, the index nodes of one transaction, each at its largest, and the two
top nodes (48 + 16 x 48 bytes at most since CRC32C, 024-25, and a got-dirty entry
of 16 each, as `Db.checkDirtyNodes` counts them) fit 15/16 of the record limit
2^31 - 9 (`Db.dirtyLimit`) at every node
size of the builder, with H the height bound 1 + log_m(2^60) of any database
(024-17, 5.2: 61, 38, 21 and 16 at node sizes 8, 14, 30 and 62; 22, m = 7's,
kept at 30 as the safe figure, 5.2a). Arithmetic
only: with TP23 and TP26 proved, and H from V1 (TP30), it makes 005-31's
refusal unreachable within the limits for a transaction without key or value
transformations, whose KVs Java counts coarsely (024-24's review, R3), so a `Bug`
(QL5) once those are counted within this bound. -/
abbrev ReleaseFits (M H : Nat) : Prop :=
  (Limits.release.dirtyNodes (Params.java M H)) * nodeBytes M + 2 * (48 + 16 * 48 + 16) ≤
    (2 ^ 31 - 9) - (2 ^ 31 - 9) / 16

theorem releaseFits8 : ReleaseFits 8 61 := by decide
theorem releaseFits14 : ReleaseFits 14 38 := by decide
theorem releaseFits30 : ReleaseFits 30 22 := by decide
theorem releaseFits62 : ReleaseFits 62 16 := by decide

/-- The count of 20 a level, every operation at the longest key, did not fit at
node size 30 and H = 22 (024-17, 5.2a: 481 operations). -/
theorem twentyALevelDoesNotFit30 :
    ¬ (500 * (20 * 16 * (22 + 2) + 14)) * 544 + 2 * (48 + 16 * 48 + 16) ≤ (2 ^ 31 - 9) - (2 ^ 31 - 9) / 16 := by
  decide

end SIS.Tree
