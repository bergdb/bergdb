/-
bergdb 030-29: `Dag.dirtyNodeBound` (java/src/bergdb/dag/Dag.java), Java's
upper bound on the index nodes that a transaction can make dirty or create,
as Java computes it, on the contract's tree. `Db.checkDirtyNodes` refuses a
transaction before its go point if this count, each node at its largest,
could take its record past the record limit (rule R1; 027-08, section 4.2;
027-03, section 8).

Each definition restates one method of Dag, or one loop of
`dirtyNodeBound`, and names it; 030-29, section 2, compares them line by
line. The inputs are Java's: the node size B (`maxNodeSize`), the tree read
at the lookup time t (`topDs.findRoot(time)` and each node's klongs at t),
and the transaction's keys with, for each, whether it is a delete
(`keys[k]`, `deletes[k]`). Java's `IdentityHashMap` of the walked nodes is a
list by node id, in the order first reached; Java's `HashMap` of a node's new
segment trees a list by segment, in the order first met. Neither order
changes the count (030-29, section 2). Java's loops have no fuel; the
recursions here have fuel that suffices on a tree whose pointers go to lower
levels (each node's level and one more), as the contract's walks do.

Everything here runs; nothing needs Mathlib.
-/
import Contract.Shape

namespace Contract.DNB

/-! ## The thresholds of node size b (Dag's static methods) -/

/-- `Dag.splitAbove`: h, 17 at node size 30 (SPLIT_ABOVE_30 * b / 30). -/
def splitAbove (b : Nat) : Nat := 17 * b / 30

/-- `Dag.minFill`: m, 8 at node size 30, at least 2 from node size 8, else 1. -/
def minFill (b : Nat) : Nat := if b < 8 then 1 else max 2 (8 * b / 30)

/-- `Dag.mergeCap`: c, 17 at node size 30. -/
def mergeCap (b : Nat) : Nat := 17 * b / 30

/-- `Dag.cutSize`: the most entries of a part of a cut list, b / 2. -/
def cutSize (b : Nat) : Nat := b / 2

/-- `Dag.theta`: the most dead klongs of a key node, 7 at node size 30, at
least 2 from node size 8, else 0 (off). -/
def theta (b : Nat) : Nat := if b < 8 then 0 else max 2 (7 * b / 30)

/-- `Dag.roomAfterReplacement`: q = max(2, min(b / 2, b - h, b - c) - 3), 10 at
node size 30. Java's int below 0 is 0 here; max with 2 gives the same. -/
def roomAfterReplacement (b : Nat) : Nat :=
  max 2 (min (b / 2) (min (b - splitAbove b) (b - mergeCap b)) - 3)

/-! ## The counts of one node -/

/-- `Dag.overflows(klongs, size, merged, dead)`: how many times a node of
`size` klongs, given `klongs` more and a time klong, can overflow; `merged`, a
delete's path goes through it, so it has at most q of room; `dead`, its dead
klongs as walked, none for a node of a new tree (Java's -1). Java's
`Math.max(0, maxNodeSize - 2 - size)` is Nat's subtraction. -/
def overflowsD (b klongs size : Nat) (merged : Bool) (dead : Option Nat) : Nat :=
  if klongs = 0 then 0 else
    let th := theta b
    let least : Nat := match dead with
      | some d => if 0 < th ∧ th < d + klongs then 1 else 0
      | none => 0
    let k := klongs + 1
    let q := roomAfterReplacement b
    let room := if merged then min (b - 2 - size) q else b - 2 - size
    if k ≤ room then least else 1 + (k - room - 1) / q

/-- `Dag.overflows(klongs, size, merged)`: the same for a node of no dead
klongs (Java passes -1). -/
def overflows (b klongs size : Nat) (merged : Bool) : Nat :=
  if klongs = 0 then 0 else overflowsD b klongs size merged none

/-- `Dag.cutPartsBound`: at least the parts that PE cuts a list of n entries
into: one if n is at most h, else at least two of at most the cut size. -/
def cutPartsBound (b n : Nat) : Nat :=
  let cap := max 1 (cutSize b)
  if n ≤ splitAbove b then 1 else max 2 ((n + cap - 1) / cap)

/-- The loop of `Dag.rootsAbove`, `for (p = parts; p > 1; ) { p = min(p - 1,
cutPartsBound(p)); count += p; }`, with fuel (p falls each time). -/
def rootsAboveLoop (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, p =>
    if p ≤ 1 then 0 else
      let p' := min (p - 1) (cutPartsBound b p)
      p' + rootsAboveLoop b f p'

/-- `Dag.rootsAbove`: the new roots that PE puts above a root cut into `parts`
new nodes. -/
def rootsAbove (b parts : Nat) : Nat := rootsAboveLoop b parts parts

/-! ## The new segment trees (`Dag.freshTreeBound`) -/

/-- The loop over one new tree's keys in `freshTreeBound`: a klong for each
key that ends at `level` (a value), and for each other key's segment `level`,
a klong the first time it is met (the pointer to the tree below) and the key
added to that tree's keys. A key shorter than that (Java: an index out of
bounds) is passed over; none reaches here. -/
def freshGroup (level : Nat) (keys : List Key) : Nat × List (Nat × List Key) :=
  keys.foldl (fun (acc : Nat × List (Nat × List Key)) key =>
    if key.length == level + 1 then (acc.1 + 1, acc.2) else
      match key[level]? with
      | some c =>
        if acc.2.any (fun q => q.1 == c) then
          (acc.1, acc.2.map (fun q => if q.1 == c then (q.1, q.2 ++ [key]) else q))
        else (acc.1 + 1, acc.2 ++ [(c, [key])])
      | none => acc) (0, [])

/-- The splits' loop of `freshTreeBound`, `for (ov = overflows(klongs, 0,
false); ov > 0; ov = overflows(ov, 1, false)) splits += ov + 1;`, from ov,
with fuel. -/
def freshSplits (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, ov => if ov = 0 then 0 else ov + 1 + freshSplits b f (overflows b ov 1 false)

/-- `Dag.freshTreeBound`: the nodes of the new segment trees of `keys`, whose
segment `level` is in a new tree: for that tree the most of the old count (its
root, the splits and a new node above each) and PE's (its list cut into parts
and the new roots above them); and the trees below. Java's loop over a stack
of trees computes the same sum (its comment: "The count is a sum, the same in
any order"); here a recursion, with fuel. -/
def freshTreeBound (b : Nat) : Nat → List Key → Nat → Nat
  | 0, _, _ => 0
  | f + 1, keys, level =>
    let r := freshGroup level keys
    let klongs := r.1
    let splits := 1 + freshSplits b (klongs + 1) (overflows b klongs 0 false)
    let parts := cutPartsBound b klongs
    max splits (parts + rootsAbove b parts) +
      (r.2.map (fun q => freshTreeBound b f q.2 (level + 1))).sum

/-! ## The walk (`Dag.Walked`, `Dag.walked`) -/

/-- The key node that pointer x names (Java's cast `(KeyNode)` of a followed
pointer), none if x names a value or nothing. -/
def getKey (s : Tree) (x : NodeId) : Option KNode :=
  match s.obj x with
  | some (.key n) => some n
  | _ => none

/-- A node that `dirtyNodeBound` walked (`Dag.Walked`): the node, the node above
it on the path (none for the space root), its depth; its size (`node.size`, its
klongs) and whether it is a segment leaf, read from the node; the klongs it can
get; the root collapses of its tree at most; whether a delete's path goes
through it; its dead klongs as walked (`deadCount`); the keys of its new
segment trees by segment (`freshKeys`, empty for Java's null) and their
segment's index (`freshLevel`). -/
structure Walked where
  x : NodeId
  up : Option NodeId
  depth : Nat
  size : Nat
  leaf : Bool
  klongs : Nat
  collapses : Nat
  deleteBelow : Bool
  dead : Nat
  fresh : List (Nat × List Key)
  freshLevel : Nat
  deriving Repr, Inhabited

/-- The walked nodes, in the order first reached. -/
abbrev Walk := List Walked

/-- The record of node x. -/
def Walk.get? (ws : Walk) (x : NodeId) : Option Walked := ws.find? (fun w => w.x == x)

/-- The record of node x changed by f. -/
def Walk.modify (ws : Walk) (x : NodeId) (f : Walked → Walked) : Walk :=
  ws.map (fun w => if w.x == x then f w else w)

/-- `Dag.walked`: node x, a key node n, reached from the node `up`, is walked:
a new record if it has none (its depth one more than up's), else as it was. -/
def Walk.reach (ws : Walk) (x : NodeId) (n : KNode) (up : Option NodeId) : Walk :=
  if (ws.get? x).isSome then ws else
    let depth := match up with
      | some u => ((ws.get? u).map (·.depth + 1)).getD 0
      | none => 0
    ws ++ [{ x := x, up := up, depth := depth, size := n.ks.length, leaf := n.leaf,
             klongs := 0, collapses := 0, deleteBelow := false, dead := deadCount n.ks,
             fresh := [], freshLevel := 0 }]

/-- `Walked.fresh(key, i)`: a key whose segment i is not in this leaf; the first
sets `freshLevel`; a segment met for the first time gets a klong, the pointer
to its new tree. -/
def Walked.addFresh (key : Key) (i : Nat) (w : Walked) : Walked :=
  let w := if w.fresh.isEmpty then { w with freshLevel := i } else w
  let c := key[i]?.getD 0
  if w.fresh.any (fun q => q.1 == c) then
    { w with fresh := w.fresh.map (fun q => if q.1 == c then (q.1, q.2 ++ [key]) else q) }
  else { w with fresh := w.fresh ++ [(c, [key])], klongs := w.klongs + 1 }

/-! ## One key's walk (the loop body of `dirtyNodeBound`) -/

/-- The inner `while (!node.isSegmentLeaf())` loop for segment c: from key
node x by `searchLte`, each node reached walked with x above it; it stops at
a segment leaf, or where `searchLte` finds no klong (Java's `break`), or at a
pointer to no key node (Java: a cast that fails; none on a sound tree). Gives
the walk and the node it stopped at. -/
def descend (s : Tree) (c : Nat) : Nat → Walk → NodeId → Walk × NodeId
  | 0, ws, x => (ws, x)
  | f + 1, ws, x =>
    match getKey s x with
    | none => (ws, x)
    | some n =>
      if n.leaf then (ws, x) else
        match searchLte n.ks (.at c) with
        | none => (ws, x)
        | some (_, y) =>
          match getKey s y with
          | some ny => descend s c f (ws.reach y ny (some x)) y
          | none => (ws, x)

/-- A delete's climb (the loop `for (u = w, below = null; u != null; below =
u, u = u.up)`): four klongs in every node from `cur` up to the space root,
each marked `deleteBelow`; at each segment leaf, the root of the tree below it
on the path (`below`) gets the inner nodes counted since the last segment leaf
as its collapses, at least. Fuel: the depth and one more. -/
def markDelete : Nat → Walk → Option NodeId → Option NodeId → Nat → Walk
  | 0, ws, _, _, _ => ws
  | f + 1, ws, cur, below, inner =>
    match cur.bind ws.get? with
    | none => ws
    | some u =>
      let ws := ws.modify u.x (fun w => { w with klongs := w.klongs + 4, deleteBelow := true })
      if u.leaf then
        let ws := match below with
          | some b => ws.modify b (fun w => { w with collapses := max w.collapses inner })
          | none => ws
        markDelete f ws u.up (some u.x) 0
      else markDelete f ws u.up (some u.x) (inner + 1)

/-- The loop over key `key`'s segments from index i at node x (walked): the
descent to the segment leaf; at the last segment, a delete's climb or a
put's klong; else `searchEq` in the leaf: a segment that is not there is a new
segment tree (a put's) and the end of the walk, else the walk goes on in the
next segment's tree. Gives the walk and, for a delete that reached its last
segment, the node reached there (whose depth Java adds to mergeLevels). -/
def walkKey (s : Tree) (key : Key) (del : Bool) : Nat → Nat → Walk → NodeId → Walk × Option NodeId
  | 0, _, ws, _ => (ws, none)
  | f + 1, i, ws, x =>
    match key[i]? with
    | none => (ws, none)
    | some c =>
      let r := descend s c (s.fuel x) ws x
      let ws := r.1
      let x := r.2
      if i + 1 = key.length then
        if del then
          (markDelete ((((ws.get? x).map (·.depth)).getD 0) + 1) ws (some x) none 0, some x)
        else (ws.modify x (fun w => { w with klongs := w.klongs + 1 }), none)
      else
        match (getKey s x).bind (fun n => searchEq n.ks c) with
        | none => if del then (ws, none) else (ws.modify x (Walked.addFresh key i), none)
        | some y =>
          match getKey s y with
          | some ny => walkKey s key del f (i + 1) (ws.reach y ny (some x)) y
          | none => (ws, none)

/-! ## `Dag.dirtyNodeBound` -/

/-- The first loop of `dirtyNodeBound`, over the keys: for each, the space root
r walked, then the key's walk. Gives the walk, `anyDelete` and `mergeLevels`
(for each delete that reached its last segment, its node's depth, one and two
more). -/
def walkAll (s : Tree) (r : NodeId) (rn : KNode) (kd : List (Key × Bool)) :
    Walk × Bool × Nat :=
  kd.foldl (fun (acc : Walk × Bool × Nat) (kdi : Key × Bool) =>
    let ws := acc.1.reach r rn none
    let res := walkKey s kdi.1 kdi.2 (kdi.1.length + 1) 0 ws r
    match res.2 with
    | some x =>
      (res.1, true, acc.2.2 + ((((res.1.get? x).map (·.depth)).getD 0) + 1 + 2))
    | none => (res.1, acc.2.1, acc.2.2)) ([], false, 0)

/-- `w.up.klongs += w.collapses` for every walked node w with a node above it
(after a delete). -/
def addCollapses (ws : Walk) : Walk :=
  ws.foldl (fun (acc : Walk) w => match w.up with
    | some u => acc.modify u (fun v => { v with klongs := v.klongs + w.collapses })
    | none => acc) ws

/-- The second loop's body for the walked node x, deepest first: its new
segment trees; if it overflows, its parts, and the klongs its parent gets: one
for each part in a parent in its tree, else (a tree's root) the new roots above
its parts, and the overflows and one in the segment leaf above. -/
def countNode (b : Nat) (acc : Walk × Nat) (x : NodeId) : Walk × Nat :=
  match acc.1.get? x with
  | none => acc
  | some w =>
    let count := acc.2 + (w.fresh.map (fun q =>
      freshTreeBound b (q.2.foldl (fun m (k : Key) => max m k.length) 0 + 1) q.2
        (w.freshLevel + 1))).sum
    let ov := overflowsD b w.klongs w.size w.deleteBelow (some w.dead)
    if ov = 0 then (acc.1, count) else
      let parts := max (ov + 1) (cutPartsBound b (w.size + w.klongs))
      let count := count + parts
      let upInner : Bool := match w.up with
        | some u => match acc.1.get? u with
          | some v => !v.leaf
          | none => false
        | none => false
      if upInner then
        (acc.1.modify (w.up.getD 0) (fun v => { v with klongs := v.klongs + parts }), count)
      else
        let count := count + max ov (rootsAbove b parts)
        match w.up with
        | some u => (acc.1.modify u (fun v => { v with klongs := v.klongs + ov + 1 }), count)
        | none => (acc.1, count)

/-- `Dag.dirtyNodeBound(time, keys, deletes, gd)`: from the tree s read at the
lookup time t, with node size b, for the keys with their delete flags `kd`:
the walked nodes, the new segment trees, each walked node's parts if it
overflows and the new roots above a tree's root, and with a delete four nodes
for each level of its path and two levels more. 0 if there is no space root at
t. Java's `deepestFirst` is the walked records sorted by depth, deepest first
(`Collections.sort`, stable); here `mergeSort`, stable too. -/
def dirtyNodeBound (b : Nat) (s0 : Tree) (t : Time) (kd : List (Key × Bool)) : Nat :=
  let s := s0.at t
  match s.root with
  | none => 0
  | some r =>
    match getKey s r with
    | none => 0
    | some rn =>
      let st := walkAll s r rn kd
      let anyDelete := st.2.1
      let mergeLevels := st.2.2
      let count := st.1.length
      let ws := if anyDelete then addCollapses st.1 else st.1
      let order := (ws.mergeSort (fun (a b : Walked) => decide (b.depth ≤ a.depth))).map (fun (w : Walked) => w.x)
      let res := order.foldl (countNode b) (ws, count)
      res.2 + (if anyDelete then 4 * mergeLevels else 0)

/-- Java's arguments from a transaction's operations, when none has a key or
value transformation (`Db.checkDirtyNodes`): each key, and true for a delete. -/
def opsKd (ops : List Op) : List (Key × Bool) :=
  ops.map (fun op => match op with
    | .put k _ => (k, false)
    | .del k => (k, true))

/-! ## What PE makes dirty -/

/-- The key nodes a transaction of PE writes (each once, `pe_step`): the
writes that are key nodes, not values. -/
def keyWrites (ws : List (NodeId × Obj)) : Nat :=
  (ws.filter (fun w => match w.2 with
    | .key _ => true
    | .val _ => false)).length

end Contract.DNB
