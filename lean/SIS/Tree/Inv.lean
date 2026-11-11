/-
The tree model (bergdb 024-12, section 6): the invariants of BergDB's key tree,
as functions that can be computed on a structure P (the tree checker runs them
on Java's structure after every transaction, C-T6) and, in SIS/Tree/Props.lean,
as statements. Trusted part: these definitions say what a sound tree is.

A tree is looked at at a time t: the nodes reachable from the space root at t
through the klongs live at t.
-/
import SIS.Tree.Spec

namespace SIS.Tree

open SIS SIS.Check

/-- The live klongs of a key node at time t: for each compare value with a klong
at t that the bitmap at t does not delete, the pointee of the last such klong;
in increasing order of the compare values (what every search at t sees). -/
def KNode.liveAt (n : KNode) (t : Time) : List (Nat × NodeId) :=
  let pre : KNode := { leaf := n.leaf, ks := prefixAt n.ks t }
  (pre.lastVersionGivenDel t (n.delAt t)).ks.filterMap (fun k => match k with
    | .key c y => some (c, y)
    | _ => none)

/-- The compare value of key klong b of a list of klongs. -/
def cvAt (ks : List Klong) (b : Nat) : Option Nat :=
  match (ks[b]? : Option Klong) with
  | some (.key c _) => some c
  | _ => none

/-- The klongs of a node are well formed: the times of its time klongs increase
strictly; a key klong or a bitmap comes after a time klong; a bitmap's bits are
in increasing order; it holds the bits of the bitmap before it and at least one
more, only bits of key klongs before it, and for each compare value of a new
bit the bits of all klongs of it before the bitmap (Java's `Dag.bitsOf`: a delete sets the bits of every klong of
its compare value). -/
def klongsWf (ks : List Klong) : Bool :=
  let r := ks.zipIdx.foldl (fun (acc : Bool × Option Time × List Nat) (k, i) =>
    match k with
    | .time t => (acc.1 && (match acc.2.1 with
        | some t0 => decide (t0 < t)
        | none => true), some t, acc.2.2)
    | .key _ _ => (acc.1 && acc.2.1.isSome, acc.2.1, acc.2.2)
    | .del bits =>
      let newCvs := (bits.filter (fun b => !acc.2.2.contains b)).filterMap (cvAt ks)
      (acc.1 && acc.2.1.isSome && acc.2.2.all (fun b => bits.contains b) &&
        decide (acc.2.2.length < bits.length) &&
        (bits.zip (bits.drop 1)).all (fun q => decide (q.1 < q.2)) &&
        bits.all (fun b => decide (b < i) && (cvAt ks b).isSome) &&
        (List.range i).all (fun j => match cvAt ks j with
          | some c => !newCvs.contains c || bits.contains j
          | none => true), acc.2.1, bits)) (true, none, [])
  r.1

/-- What a walk of the tree at a time found wrong, as texts. -/
abbrev Faults := List String

/-- The walk of one segment tree at time t, from node x: `lo` and `hi` bound the
compare values that the klongs above x allow below it (`hi` none: no bound);
`isRoot`: x is the root of its segment tree; `space`: of the first segment's.
Checks, for every key node reached (the names are those of SIS/Tree/Props.lean):

* `SizeOK`: at most M klongs; `klongsWf`; klongs and history correspond
  (`entriesOf`, `klongsOf`);
* `PointersOK`: every node that a klong names, live or not, is a node of P;
* `NonEmptyOK` (what UP leaves): a live klong, but in a space root that is a
  segment leaf;
* `LeftmostOK` (LE-b): an inner node's smallest live compare value is the
  empty key's, 0;
* `RootsOK` (what RC leaves): an inner root has two live klongs at least;
* `FillOK` (V1 of bergdb 024-11, the bound BU1; with merges on): a key node
  that is not the root of its segment tree has at least m live klongs;
* `RangeOK` (the order): a segment leaf's live compare values are at or above
  `lo` and below `hi`; an inner node's, but the empty key's, above `lo` and
  below `hi`;
* `KindsOK`: an inner node's children are key nodes one height below it in its
  segment; a segment leaf's klong of a long segment names a key node of the
  next segment, any other a value.
-/
def walk (p : Params) (view : View BVal) (t : Time) :
    Nat → NodeId → Nat → Option Nat → Bool → Bool → Faults
  | 0, x, _, _, _, _ => [s!"the walk at {t} went below the height bound at node {x}"]
  | f + 1, x, lo, hi, isRoot, space =>
    match view x with
    | none => [s!"key node {x} is not in P"]
    | some nd =>
      if nd.isData then [s!"node {x} is a value, a key node was expected"] else
        let n : KNode := { leaf := p.heightOf nd.level == 0, ks := klongsOf nd.hist }
        let live := n.liveAt t
        let g := p.segOf nd.level
        let h := p.heightOf nd.level
        let own : Faults :=
          (if n.size > p.M then [s!"SizeOK: key node {x} has {n.size} klongs"] else []) ++
          (if !klongsWf n.ks then [s!"klongsWf: key node {x}"] else []) ++
          (if entriesOf n.ks != nd.hist then [s!"key node {x}: its klongs do not give its history"] else []) ++
          (n.ks.filterMap (fun k => match k with
            | .key _ y => if (view y).isNone then some s!"PointersOK: key node {x} names {y}, no node of P" else none
            | _ => none)) ++
          (if live.isEmpty && !(space && isRoot && n.leaf) then
            [s!"NonEmptyOK: key node {x} has no live klong at {t}"] else []) ++
          (if !n.leaf && !live.isEmpty && (live.head?.map (·.1)) != some 0 then
            [s!"LeftmostOK: inner node {x} has no live klong of the empty key at {t}"] else []) ++
          (if !n.leaf && isRoot && live.length < 2 then
            [s!"RootsOK: inner root {x} has {live.length} live klongs at {t}"] else []) ++
          (if p.merges && !isRoot && live.length < p.mergeBelow then
            [s!"FillOK: key node {x}, not a root, has {live.length} live klongs at {t}, fewer than m = {p.mergeBelow}"] else []) ++
          (live.filterMap (fun (c, _) =>
            let low := if n.leaf then decide (lo ≤ c) else (c == 0 || decide (lo < c))
            let high := match hi with
              | some b => decide (c < b)
              | none => true
            if low && high then none
            else some s!"RangeOK: key node {x} has the live compare value {c} outside [{lo}, {hi})"))
        -- The children, each with the range its klong and the next one give it.
        let his : List (Option Nat) := (live.drop 1).map (fun q => some q.1) ++ [hi]
        let below : Faults := (live.zip his).flatMap (fun ((c, y), hi') =>
          if n.leaf then
            if segLen c == 7 then
              match view y with
              | some ny =>
                if ny.isData then [s!"KindsOK: segment leaf {x}: the long segment {c} names a value"]
                else if p.segOf ny.level != g + 1 then
                  [s!"KindsOK: segment leaf {x}: {y} is not in the next segment"]
                else walk p view t f y 0 none true false
              | none => []
            else
              match view y with
              | some ny => if ny.isData then [] else [s!"KindsOK: segment leaf {x}: the short segment {c} names a key node"]
              | none => []
          else
            match view y with
            | some ny =>
              if ny.isData then [s!"KindsOK: inner node {x} names a value"]
              else if p.segOf ny.level != g || p.heightOf ny.level + 1 != h then
                [s!"KindsOK: inner node {x} at height {h}: child {y} at height {p.heightOf ny.level}, segment {p.segOf ny.level}"]
              else walk p view t f y (if c == 0 then lo else c) hi' false space
            | none => [])
        own ++ below

/-- The invariants of the tree of P at time t, computed: the faults found; none
for a sound tree. -/
def faultsAt (p : Params) (view : View BVal) (t : Time) : Faults :=
  match rootAt view t with
  | none => [s!"no space root at {t}"]
  | some r => walk p view t p.fuel r 0 none true true

/-- The key nodes reachable at time t, with their klongs live then, in the
walk's order (for counts and the statements about costs). -/
def nodesAt (p : Params) (view : View BVal) (t : Time) : Nat → NodeId → List NodeId
  | 0, _ => []
  | f + 1, x =>
    match knodeOf p view x with
    | none => []
    | some n =>
      x :: (n.liveAt t).flatMap (fun (c, y) =>
        if n.leaf && segLen c != 7 then [] else nodesAt p view t f y)

end SIS.Tree
