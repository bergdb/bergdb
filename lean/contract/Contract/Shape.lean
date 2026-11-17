/-
The contract package (bergdb 030-04, section 7.4 (c)): the writer's own
rules, which no reader needs. They are not in the contract. They are cost
properties (how full, how deep, how many dead klongs) and the leftmost rule
that a put relies on; the trace checker computes them on Java's tree after
every traced transaction and reports them apart from the contract.

* LeftmostOK (LE-b): an inner node's smallest live klong is the empty key's,
  compare value 0.
* RootsOK (what root collapse leaves): an inner root of a segment tree has
  two live klongs at least.
* FillOK (the fill that the merges keep): a key node that is not the root of
  its segment tree has at least m live klongs (`Dag.minFill`; on from m = 2).
* DeadOK: a key node holds at most theta dead key klongs (`Dag.theta`; on
  from theta = 1).
* BalancedOK: a key node is a segment leaf exactly at height 0 of its
  segment tree, and an inner node's children are one level below it.
-/
import Contract.Statement

namespace Contract

/-- The parameters of the writer's rules, from the trace's TREE line: H, the
largest height of a key node in its segment tree; m; theta. -/
structure ShapeParams where
  H : Nat
  minFill : Nat
  theta : Nat
  deriving Repr, Inhabited

/-- The dead key klongs of a node (`Dag.deadCount`): a key klong that the last
bitmap deletes, or that a later key klong of the same compare value follows. -/
def deadCount (ks : List Klong) : Nat :=
  let del := lastBitmap ks
  (ks.zipIdx.filter (fun (k, i) => match k with
    | .key c _ => del.contains i || (ks.drop (i + 1)).any (fun k' => match k' with
        | .key c' _ => c' == c
        | _ => false)
    | _ => false)).length

/-- The faults of the writer's rules from key node x, by name. -/
def shapeWalk (q : ShapeParams) (s : Tree) : Nat → NodeId → Bool → List String
  | 0, _, _ => ["fuel"]
  | f + 1, x, isRoot =>
    match s.obj x with
    | some (.key n) =>
      let lv := live n.ks
      (if !n.leaf && !lv.isEmpty && (lv.head?.map (·.1)) != some 0 then ["LeftmostOK"] else []) ++
      (if !n.leaf && isRoot && lv.length < 2 then ["RootsOK"] else []) ++
      (if decide (2 ≤ q.minFill) && !isRoot && lv.length < q.minFill then ["FillOK"] else []) ++
      (if q.theta != 0 && decide (q.theta < deadCount n.ks) then ["DeadOK"] else []) ++
      (if n.leaf != ((n.level - 1) % (q.H + 1) == 0) then ["BalancedOK"] else []) ++
      lv.flatMap (fun (c, y) =>
        if n.leaf then (if isLong c then shapeWalk q s f y true else [])
        else
          (match s.obj y with
           | some (.key m) => if m.level + 1 != n.level then ["BalancedOK"] else []
           | _ => []) ++ shapeWalk q s f y false)
    | _ => []

/-- The faults of the writer's rules in a tree. -/
def shapeFaults (q : ShapeParams) (s : Tree) : List String :=
  match s.root with
  | some r => shapeWalk q s (s.fuel r) r true
  | none => []

end Contract
