/-
The contract package (bergdb 030-04): BergDB's key tree as Java has it, for
the writer's contract and the theorem on gets and scans.

A tree is a heap of nodes by id, and the top: the space root from each time
on. A key node is its klongs, exactly as Java's `KeyNode` has them. This file
holds the definitions that the invariants (Statement.lean) and the readers
(Read.lean) are about. Everything here runs; nothing needs Mathlib.

Copied from the old model (lean/SIS/Tree/Node.lean, bergdb 024-12) and
adapted: `Klong`, `lastBitmap`, `prefixAt`, `segLen`, and the searches. Each
names the Java method it restates (java/src/bergdb/dag).
-/

namespace Contract

abbrev NodeId := Nat
abbrev Time := Nat

/-- A key as Java's Dag gets it (`Keys.toSegments`): the compare values of its
segments. -/
abbrev Key := List Nat

/-! ## Klongs and nodes -/

/-- A klong of a key node (`Klong`): a time klong; a key klong, with its
compare value c and the node y that its pointer names; a delete bitmap, the
indexes of the klongs it deletes. -/
inductive Klong where
  | time (t : Time)
  | key (c : Nat) (y : NodeId)
  | del (bits : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A key node (`KeyNode`): its level (as the trace's NEW line gives it; a
pointer goes to a lower level), whether it is a segment leaf, and its klongs. -/
structure KNode where
  level : Nat
  leaf : Bool
  ks : List Klong
  deriving DecidableEq, Repr, Inhabited

/-- A node of the heap: a key node, or a value (its hash, as in the trace). -/
inductive Obj where
  | key (n : KNode)
  | val (h : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The tree: the nodes by id, and the top, the space root from each time on
(the root's entries and the top nodes' root pointers, without the skip
pointers: `TopDs.findRoot` gives the last one at or before a time). -/
structure Tree where
  obj : NodeId → Option Obj
  roots : List (Time × NodeId)

/-! ## A tree at a time -/

/-- The klongs of a node as they were at time t: those before the first time
klong after t (`KeyNode.toPreviousState`; every reader's loop ends there). -/
def prefixAt (ks : List Klong) (t : Time) : List Klong :=
  ks.takeWhile (fun k => match k with
    | .time x => decide (x ≤ t)
    | _ => true)

/-- A node as it was at time t. -/
def Obj.at (t : Time) : Obj → Obj
  | .key n => .key { n with ks := prefixAt n.ks t }
  | .val h => .val h

/-- The tree as a reader at time t sees it: every node cut at t, and the
space roots of the times at or before t. -/
def Tree.at (s : Tree) (t : Time) : Tree :=
  { obj := fun x => (s.obj x).map (Obj.at t),
    roots := s.roots.filter (fun r => decide (r.1 ≤ t)) }

/-- The space root: the last one (`TopDs.findRoot`). -/
def Tree.root (s : Tree) : Option NodeId := s.roots.getLast?.map (·.2)

/-- The value of node y, if it is a value. -/
def Tree.val (s : Tree) (y : NodeId) : Option Nat :=
  match s.obj y with
  | some (.val h) => some h
  | _ => none

/-- The fuel of a walk from key node x: its level and one more. A pointer
goes to a lower level, so no walk of a sound tree runs out. -/
def Tree.fuel (s : Tree) (x : NodeId) : Nat :=
  match s.obj x with
  | some (.key n) => n.level + 1
  | _ => 0

/-! ## The live klongs of a node -/

/-- The last bitmap of a list of klongs, none set if it has none
(`KeyNode.getDeleteBitmapAtTime` on the klongs at that time). -/
def lastBitmap (ks : List Klong) : List Nat :=
  ks.foldl (fun d k => match k with
    | .del b => b
    | _ => d) []

/-- Sets the pointee of compare value c in a list in increasing order of the
compare values. -/
def insertCv (c : Nat) (y : NodeId) : List (Nat × NodeId) → List (Nat × NodeId)
  | [] => [(c, y)]
  | (c', y') :: r =>
    if c < c' then (c, y) :: (c', y') :: r
    else if c = c' then (c, y) :: r
    else (c', y') :: insertCv c y r

/-- The live klongs given the bitmap `del`. -/
def liveWith (del : List Nat) (ks : List (Klong × Nat)) : List (Nat × NodeId) :=
  ks.foldl (fun m (k, i) => match k with
    | .key c y => if del.contains i then m else insertCv c y m
    | _ => m) []

/-- The live klongs of a node: for each compare value with a key klong that the
last bitmap does not delete, the pointee of the last such klong; in increasing
order of the compare values. This is what a node holds: its children, or, in
a segment leaf, its key segments. -/
def live (ks : List Klong) : List (Nat × NodeId) := liveWith (lastBitmap ks) ks.zipIdx

/-- `Klong.getLength`: the number of key bytes of a segment, from its compare
value. -/
def segLen (c : Nat) : Nat := (c / 8) % 8

/-- A segment of 7 bytes: the key goes on in the next segment's tree. Any
other segment is a key's last (`Keys.toSegments`). -/
def isLong (c : Nat) : Bool := segLen c == 7

/-! ## The searches (`KeyNode.searchEq` and four others) -/

/-- What a search is asked for: a compare value, or one of Java's two
sentinels, -1 (`lo`, below every compare value) and `Long.MAX_VALUE` (`hi`,
above every one: a compare value is below 2^62, `Klong.getCompareValue`). -/
inductive Pos where
  | lo
  | at (c : Nat)
  | hi
  deriving DecidableEq, Repr, Inhabited

/-- Compare value c is below position p. -/
def Pos.above (p : Pos) (c : Nat) : Bool :=
  match p with
  | .lo => false
  | .at d => decide (c < d)
  | .hi => true

/-- Compare value c is above position p. -/
def Pos.below (p : Pos) (c : Nat) : Bool :=
  match p with
  | .lo => true
  | .at d => decide (d < c)
  | .hi => false

/-- Compare value c is at position p. -/
def Pos.is (p : Pos) (c : Nat) : Bool :=
  match p with
  | .at d => c == d
  | _ => false

/-- `KeyNode.searchEq`: Java's loop, with the bitmaps in their order: a key
klong of c is the match; a bitmap that deletes the match leaves none. The
state: the bitmap so far, and the match's index and pointee. -/
def searchEq (ks : List Klong) (c : Nat) : Option NodeId :=
  (ks.zipIdx.foldl
    (fun (acc : List Nat × Option (Nat × NodeId)) (k, i) =>
      if acc.1.contains i then acc else
        match k with
        | .time _ => acc
        | .key c' y => if c' == c then (acc.1, some (i, y)) else acc
        | .del b => (b, match acc.2 with
          | some f => if b.contains f.1 then none else some f
          | none => none))
    ([], none)).2.map (·.2)

/-- The common loop of the four other searches: over the klongs that the last
bitmap does not delete, a key klong replaces the best so far when `better`
says so. Gives the compare value found and its pointee. -/
def searchBy (ks : List Klong) (better : Nat → Option Nat → Bool) : Option (Nat × NodeId) :=
  let del := lastBitmap ks
  ks.zipIdx.foldl (fun (best : Option (Nat × NodeId)) (k, i) =>
    if del.contains i then best else
      match k with
      | .key c y => if better c (best.map (·.1)) then some (c, y) else best
      | _ => best) none

/-- True if there is no best yet, or r holds for it. -/
def bestOr (best : Option Nat) (r : Nat → Bool) : Bool :=
  match best with
  | none => true
  | some b => r b

/-- `KeyNode.searchLte`: the largest live compare value at or below p; of
klongs with one compare value, the last. -/
def searchLte (ks : List Klong) (p : Pos) : Option (Nat × NodeId) :=
  searchBy ks (fun c best => bestOr best (fun b => decide (b ≤ c)) && !p.below c)

/-- `KeyNode.searchLt`. -/
def searchLt (ks : List Klong) (p : Pos) : Option (Nat × NodeId) :=
  searchBy ks (fun c best => bestOr best (fun b => decide (b ≤ c)) && p.above c)

/-- `KeyNode.searchGt`: the smallest live compare value above p; of klongs
with one compare value, the last. -/
def searchGt (ks : List Klong) (p : Pos) : Option (Nat × NodeId) :=
  searchBy ks (fun c best => bestOr best (fun b => decide (c ≤ b)) && p.below c)

/-- `KeyNode.searchGte`. -/
def searchGte (ks : List Klong) (p : Pos) : Option (Nat × NodeId) :=
  searchBy ks (fun c best => bestOr best (fun b => decide (c ≤ b)) && !p.above c)

end Contract
