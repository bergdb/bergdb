/-
bergdb 030-29: Java's count (`DNB.dirtyNodeBound`) as one recursion over the
tree, the shape of PE's plan, and what PE's writes are counted by.

`sbPlan` is the count of `Dag.dirtyNodeBound` for the node x of the tree and
the operations whose walks pass x, computed bottom-up: the walked nodes, the
klongs each gets (a put's one in its leaf, a new segment's one, four of every
delete on every node of its path, the parts of an overflowing child, a
tree root's overflows and one and its collapses in the segment leaf above),
each node's overflows and parts, the new roots above an overflowing tree
root, the new segment trees, and the deletes' four nodes a level and two levels
more (here four on every node of a delete's path and eight at its end).
The proof that Java's walk computes it (TREE gives each node one parent) is
`dirtyNodeBound_eq_sb` (DnbWalk.lean); that PE writes at most it, in DnbPe.

The routing of the operations among an inner node's children is PE's
(`route`), which is Java's `searchLte` on a node whose first live klong is the
empty key; a segment leaf's operations are taken compare value by compare
value (`touched`), as PE's `applyGroups` takes them.
-/
import Contract.Proof.DnbDefs

namespace Contract.PE

open DNB

/-- A delete. -/
def opDel : Op → Bool
  | .del _ => true
  | .put _ _ => false

/-- What the count gives for a walked node: its subtree's count (`cnt`), the
klongs its parent gets (`up`), the deletes through it that reached their last
segment (`nd`), the inner nodes on their paths from it down to the next
segment leaf, at most (`ci`), the klongs it gets (`K`), its overflows (`ov`)
and its parts (0 if it does not overflow). -/
structure SR where
  cnt : Nat
  up : Nat
  nd : Nat
  ci : Nat
  K : Nat
  ov : Nat
  parts : Nat
  deriving Inhabited, Repr

/-- The count of a walked key node n from what it gets: K klongs, nd deletes
through it, ci, and the count below it. A tree's root (`isRoot`: the space
root or a node a segment leaf points to) that overflows gets the new roots
above its parts, and gives the leaf above its overflows and one and its
collapses; any other node gives its parent its parts. -/
def sbNode (b : Nat) (n : KNode) (isRoot : Bool) (K nd ci below : Nat) : SR :=
  let ov := overflowsD b K n.ks.length (decide (0 < nd)) (some (deadCount n.ks))
  let parts := if ov = 0 then 0 else max (ov + 1) (cutPartsBound b (n.ks.length + K))
  let rootT := if isRoot = true ∧ ov ≠ 0 then max ov (rootsAbove b parts) else 0
  { cnt := 1 + 4 * nd + below + parts + rootT,
    up := (if isRoot = true ∧ 0 < nd then ci else 0) +
      (if ov = 0 then 0 else if isRoot = true then ov + 1 else parts),
    nd := nd, ci := ci, K := K, ov := ov, parts := parts }

/-- The keys of a list of operations. -/
def opKeys (ops : List Op) : List Key := ops.map (·.key)

/-- `freshTreeBound` of a new segment's keys, with the fuel `countNode` gives
it. -/
def ftbOf (b : Nat) (keys : List Key) (level : Nat) : Nat :=
  freshTreeBound b (keys.foldl (fun m (k : Key) => max m k.length) 0 + 1) keys level

/-- One compare value's group of a segment leaf: its klongs, its count, its
deletes. A key that ends here: a put one klong, a delete one at nd and eight
nodes; keys that go on: the next segment's tree if the leaf has the compare
value (its count, the klongs it gives the leaf, its deletes), else the new
tree of the puts (a klong and `freshTreeBound`). -/
def sbGroup (b : Nat) (g : Nat) (lv : List (Nat × NodeId)) (grp : List Op)
    (child : NodeId → List Op → SR) (cv : Nat) : Nat × Nat × Nat :=
  let endP := (grp.filter (fun op => endsAt g op && !opDel op)).length
  let endD := (grp.filter (fun op => endsAt g op && opDel op)).length
  let subs := grp.filter (fun op => !endsAt g op)
  let subP := subs.filter (fun op => !opDel op)
  if subs.isEmpty then (endP, 8 * endD, endD) else
    match lv.lookup cv with
    | some y =>
      let r := child y subs
      (endP + r.up, 8 * endD + r.cnt, endD + r.nd)
    | none =>
      if subP.isEmpty then (endP, 8 * endD, endD)
      else (endP + 1, 8 * endD + ftbOf b (opKeys subP) (g + 1), endD)

/-- The count for key node x of segment g with the operations whose walks
pass it (`isRoot`: x is a tree's root). A segment leaf: its groups. An inner
node: each child with operations (PE's `route`), one height down. Fuel: at
least the node's level and one. -/
def sbPlan (b : Nat) (s : Tree) : Nat → NodeId → Nat → List Op → Bool → SR
  | 0, _, _, _, _ => default
  | f + 1, x, g, ops, isRoot =>
    match DNB.getKey s x with
    | none => default
    | some n =>
      let lv := live n.ks
      if n.leaf then
        let rs := (touched g ops).map (fun cv =>
          sbGroup b g lv (ops.filter (fun op => segAt g op == cv))
            (fun y subs => sbPlan b s f y (g + 1) subs true) cv)
        let nd := (rs.map (·.2.2)).sum
        sbNode b n isRoot (4 * nd + (rs.map (·.1)).sum) nd 0 (rs.map (·.2.1)).sum
      else
        let rs := ((lv.zip (route (segAt g) lv ops)).filter (fun e => !e.2.isEmpty)).map
          (fun e => sbPlan b s f e.1.2 g e.2 false)
        let nd := (rs.map (·.nd)).sum
        let ci := if nd = 0 then 0 else 1 + ((rs.filter (fun r => 0 < r.nd)).map (·.ci)).foldl max 0
        sbNode b n isRoot (4 * nd + (rs.map (·.up)).sum) nd ci (rs.map (·.cnt)).sum

/-- The count for a transaction: from the space root, 0 without operations. -/
def sbTop (b : Nat) (s : Tree) (ops : List Op) : Nat :=
  match s.root with
  | none => 0
  | some r =>
    if ops.isEmpty then 0 else (sbPlan b s (s.fuel r) r 0 ops true).cnt

/-! ## What PE writes -/

/-- The key nodes written so far. -/
def kw (acc : Acc) : Nat := DNB.keyWrites acc.ws

/-- The key nodes emit writes for a decision. -/
def dcost : Dec → Nat
  | .same => 0
  | .append => 1
  | .parts k => k

mutual

/-- The key nodes emit writes for a planned virtual node: its decision's and
its children's (a planned leaf's entries are untouched payloads, none). -/
def vcost : VN → Nat
  | .old _ => 0
  | .node _ _ _ _ es _ dec => dcost dec + vcostL es

/-- `vcost` of a list of entries. -/
def vcostL : List (Nat × VN) → Nat
  | [] => 0
  | (_, v) :: r => vcost v + vcostL r

end

end Contract.PE
