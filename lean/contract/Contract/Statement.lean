/-
The contract package (bergdb 030-04, section 7.4 (a)): the invariants of
BergDB's key tree and the writer's contract, in English and in Lean, side by
side. This is the file to read and to trust, with Tree.lean (what a tree is)
and Read.lean (the readers). The theorems that follow from it are stated in
Theorems.lean.

Everything here but `Frame`, `Contract`, `Start` and `Meets` is a function
that runs: the trace checker (ContractCheck.lean) runs these same
definitions on Java's tree before and after every traced transaction.
Nothing here needs Mathlib.

In short:

* The invariants (`invOk`) say what a sound tree is at one time. They speak
  only of the nodes that a reader reaches from the space root.
* The contents (`contents`) are the keys and values that the tree holds,
  read off the tree in order, without any search.
* The contract (`Contract`) says what must hold when a transaction ends:
  (1) the invariants at the new time; (2) the contents are the old contents
  with the transaction's operations applied; (3) nothing that existed before
  was changed, only extended at the new time, and only nodes of D were
  touched or made.
-/
import Contract.Read

namespace Contract

/-- The parameters of the invariants: the node size M (`Dag.maxNodeSize`). -/
structure Params where
  M : Nat
  deriving Repr, Inhabited

/-! ## 1. The invariants of one node

English. The klongs of a key node are well formed:

* W1. The first klong is a time klong, and the times of the time klongs
  increase strictly.
* W2. A bitmap deletes only key klongs that stand before it.
* W3. A bitmap holds every bit of the bitmap before it (bitmaps are
  cumulative, as Java's).
* W4. A bitmap that deletes a key klong deletes every earlier key klong of
  the same compare value (`Dag.bitsOf`: a delete sets the bits of every klong
  of its compare value).

And: the node has at most M klongs (SizeOK), and every key klong, live or
dead, names a node that exists (PointersOK). -/

/-- Klong j is a key klong; its compare value. -/
def cvAt (ks : List Klong) (j : Nat) : Option Nat :=
  match ks[j]? with
  | some (.key c _) => some c
  | _ => none

/-- W1. -/
def timesOk (ks : List Klong) : Bool :=
  (match ks with
   | .time _ :: _ => true
   | [] => true
   | _ => false) &&
  (ks.foldl (fun (acc : Bool × Option Time) k => match k with
    | .time t => (acc.1 && (match acc.2 with
        | some t0 => decide (t0 < t)
        | none => true), some t)
    | _ => acc) (true, none)).1

/-- W2, W3 and W4, for the bitmap `bits` at index i, with `before` the bitmap
before it (none set if there is none). -/
def bitmapOk (ks : List Klong) (i : Nat) (before bits : List Nat) : Bool :=
  bits.all (fun j => decide (j < i) && (cvAt ks j).isSome) &&
  before.all (fun j => bits.contains j) &&
  bits.all (fun j => (List.range j).all (fun j' =>
    cvAt ks j' != cvAt ks j || bits.contains j'))

/-- One step of the check of the bitmaps, at klong k with index i. The state:
no fault so far, and the bitmap before. -/
def bmStep (ks : List Klong) (acc : Bool × List Nat) (k : Klong) (i : Nat) : Bool × List Nat :=
  match k with
  | .del bits => (acc.1 && bitmapOk ks i acc.2 bits, bits)
  | _ => acc

/-- W2, W3 and W4 for every bitmap. -/
def bitmapsOk (ks : List Klong) : Bool :=
  (ks.zipIdx.foldl (fun acc ki => bmStep ks acc ki.1 ki.2) (true, [])).1

/-- The klongs of a node are well formed: W1 to W4. -/
def klongsWf (ks : List Klong) : Bool := timesOk ks && bitmapsOk ks

/-- The invariants of one key node: SizeOK, well-formed klongs, PointersOK. -/
def nodeOk (p : Params) (s : Tree) (n : KNode) : Bool :=
  decide (n.ks.length ≤ p.M) && klongsWf n.ks &&
  n.ks.all (fun k => match k with
    | .key _ y => (s.obj y).isSome
    | _ => true)

/-! ## 2. The invariants of the tree

English. Walk the tree from the space root through the live klongs. Each key
node is reached with a range [lo, hi) of compare values (hi may be absent: no
upper bound). The root of a segment tree has the range [0, none).

* The node meets the invariants of one node (section 1).
* KindsOK. In an inner node, every live klong names a key node. In a segment
  leaf, a live klong of a long segment (7 bytes) names a key node, the root
  of the next segment's tree; any other live klong names a value. A key node
  named by a live klong has a lower level than the node that names it.
* NonEmptyOK. Every key node reached has a live klong; only the space root
  may be without one, and only if it is a segment leaf.
* RangeOK, the key order. Every live compare value of the node is below hi.
  In a segment leaf it is also at or above lo. In an inner node, the child of
  the live klong with compare value c has the range from max(lo, c) to the
  next live klong's compare value, or to hi for the last one.

Not here, because no reader needs them (section 7.4 (c) of 030-04): the fill
that the merges keep, the rule that an inner root has two live klongs, the
leftmost rule (an inner node's smallest live klong is the empty key's), the
bound on dead klongs, and that a tree is balanced. They are the writer's own
rules, computed as `shapeFaults` in Shape.lean and tested on the traces. -/

/-- The upper bound of the child of a live klong: the next live klong's
compare value, or the node's own bound. -/
def nextHi (rest : List (Nat × NodeId)) (hi : Option Nat) : Option Nat :=
  match rest with
  | (c, _) :: _ => some c
  | [] => hi

/-- c is below the bound hi. -/
def belowHi (c : Nat) : Option Nat → Bool
  | none => true
  | some h => decide (c < h)

/-- KindsOK, NonEmptyOK and RangeOK for the live klong (c, y) of key node n
with the range [lo, hi), `rest` the live klongs after it, and `sub` the walk
of a key node below. -/
def kidOk (s : Tree) (n : KNode) (lo : Nat) (hi : Option Nat)
    (sub : NodeId → Nat → Option Nat → Bool) (c : Nat) (y : NodeId)
    (rest : List (Nat × NodeId)) : Bool :=
  belowHi c hi &&
  (if n.leaf then
    decide (lo ≤ c) &&
    (if isLong c then
      match s.obj y with
      | some (.key m) => decide (m.level < n.level) && !(live m.ks).isEmpty && sub y 0 none
      | _ => false
    else
      match s.obj y with
      | some (.val _) => true
      | _ => false)
  else
    match s.obj y with
    | some (.key m) =>
      decide (m.level < n.level) && !(live m.ks).isEmpty &&
        sub y (max lo c) (nextHi rest hi)
    | _ => false)

/-- `kidOk` for each live klong of a node. -/
def kidsOk (s : Tree) (n : KNode) (lo : Nat) (hi : Option Nat)
    (sub : NodeId → Nat → Option Nat → Bool) : List (Nat × NodeId) → Bool
  | [] => true
  | (c, y) :: rest => kidOk s n lo hi sub c y rest && kidsOk s n lo hi sub rest

/-- The walk of the tree from key node x with the range [lo, hi): true if
every node reached meets the invariants. The fuel is the node's level and one
more; a walk that runs out fails. -/
def walk (p : Params) (s : Tree) : Nat → NodeId → Nat → Option Nat → Bool
  | 0, _, _, _ => false
  | f + 1, x, lo, hi =>
    match s.obj x with
    | some (.key n) =>
      nodeOk p s n && kidsOk s n lo hi (fun y lo' hi' => walk p s f y lo' hi') (live n.ks)
    | _ => false

/-- The invariants of a tree: there is a space root, it is a key node, it has
a live klong unless it is a segment leaf, and the walk from it finds no
fault. A tree at time t meets the invariants if `invOk p (s.at t)`. -/
def invOk (p : Params) (s : Tree) : Bool :=
  match s.root with
  | some r =>
    match s.obj r with
    | some (.key n) => (n.leaf || !(live n.ks).isEmpty) && walk p s (n.level + 1) r 0 none
    | _ => false
  | none => false

/-! ## 3. The contents of a tree

English. The keys and values that a tree holds, in the tree's order, read off
the tree alone: no search of a reader is used. From a key node, its live
klongs in order; an inner node's klong gives what its child holds; a segment
leaf's klong of a short segment c gives the key [c] with the value it names;
a segment leaf's klong of a long segment c gives every key of the next
segment's tree with c put in front. -/

/-- What the live klong (c, y) of a key node holds, `sub` giving what a key
node below holds. -/
def klongList (s : Tree) (leaf : Bool) (sub : NodeId → List (Key × Nat)) (c : Nat)
    (y : NodeId) : List (Key × Nat) :=
  if leaf then
    if isLong c then (sub y).map (fun kv => (c :: kv.1, kv.2))
    else
      match s.obj y with
      | some (.val h) => [([c], h)]
      | _ => []
  else sub y

/-- What key node x holds. -/
def listAt (s : Tree) : Nat → NodeId → List (Key × Nat)
  | 0, _ => []
  | f + 1, x =>
    match s.obj x with
    | some (.key n) =>
      (live n.ks).flatMap (fun cy => klongList s n.leaf (fun y => listAt s f y) cy.1 cy.2)
    | _ => []

/-- The contents of a tree: what its space root holds. The contents at time t
are `contents (s.at t)`. -/
def contents (s : Tree) : List (Key × Nat) :=
  match s.root with
  | some r => listAt s (s.fuel r) r
  | none => []

/-! ## 4. The plain map

English. The reference: a list of keys with their values, in key order. A
put sets the key's value; a delete removes the key, and changes nothing if
the key is not there. -/

/-- An operation of a transaction, as the Dag gets it (`Db.putKvs`; the
trace's OP lines): a put of a key and a value (its hash), or a delete. -/
inductive Op where
  | put (key : Key) (h : Nat)
  | del (key : Key)
  deriving DecidableEq, Repr, Inhabited

/-- A put in the plain map. -/
def mapPut (k : Key) (v : Nat) : List (Key × Nat) → List (Key × Nat)
  | [] => [(k, v)]
  | (k', v') :: r =>
    if keyLt k k' then (k, v) :: (k', v') :: r
    else if k = k' then (k, v) :: r
    else (k', v') :: mapPut k v r

/-- A delete in the plain map. -/
def mapDel (k : Key) (m : List (Key × Nat)) : List (Key × Nat) :=
  m.filter (fun kv => kv.1 != k)

/-- A transaction's operations applied to the plain map, in their order. -/
def applyOps (ops : List Op) (m : List (Key × Nat)) : List (Key × Nat) :=
  ops.foldl (fun m op => match op with
    | .put k v => mapPut k v m
    | .del k => mapDel k m) m

/-- The plain map after the transactions txs, from the empty map. -/
def refMap (txs : List (List Op)) : List (Key × Nat) :=
  txs.foldl (fun m ops => applyOps ops m) []

/-- A get in the plain map. -/
def refGet (m : List (Key × Nat)) (k : Key) : Option Nat := m.lookup k

/-- A key is in the range a scan asks for. -/
def inRange (req : ScanReq) (k : Key) : Bool :=
  (match req.start with
    | none => true
    | some s =>
      if req.forward then (if req.inclusive then !keyLt k s else keyLt s k)
      else (if req.inclusive then !keyLt s k else keyLt k s)) &&
  (match req.endKey with
    | none => true
    | some e => if req.endInclusive then !keyLt e k else keyLt k e)

/-- A scan in the plain map: the keys and values in the range, in key order
forward, in reverse order backward, the first `limit`. -/
def refScan (m : List (Key × Nat)) (req : ScanReq) (limit : Nat) : List (Key × Nat) :=
  let kvs := m.filter (fun kv => inRange req kv.1)
  (if req.forward then kvs else kvs.reverse).take limit

/-- A key as `Keys.toSegments` makes it: at least one segment, every segment
but the last long, the last one not. -/
def keyWf : Key → Bool
  | [] => false
  | [c] => !isLong c
  | c :: rest => isLong c && keyWf rest

/-- A scan's request as the API allows it: keys as `Keys.toSegments` makes
them, an end key only forward. -/
def ScanReq.wf (req : ScanReq) : Bool :=
  (match req.start with
    | some k => keyWf k
    | none => true) &&
  (match req.endKey with
    | some e => keyWf e && req.forward
    | none => true)

/-! ## 5. The contract

English. A transaction with the operations `ops` is run by the writer at time
i on the tree s, and the writer accepts it. It ends in the tree s' and names
D, the nodes it marked dirty. The writer's contract:

1. s' at time i meets the invariants.
2. The contents of s' at time i are the contents of s at time i - 1 with the
   operations applied: each key put has its new value, each key deleted is
   gone, every other key is as it was.
3. The frame. Every node of s is a node of s', of the same kind. A value is
   unchanged. A key node keeps its level, whether it is a segment leaf, and
   all its klongs; klongs may be added after them, and then the first one
   added is a time klong of time i. A node that is not in D is unchanged. A
   key node of s' that is no node of s is in D. The space roots of s are
   those of s', in order; the ones added have the time i.

Clause 1 and 2 are computed (`contractOk`). Clause 3 is a statement about
every node of s (`Frame`); the trace checker computes it over the nodes of
its heap, and Check.lean proves that its computation gives `Frame`.

Earlier times are in clause 3: a reader at an earlier time reads each node up
to its first time klong after that time, so it sees what it saw.

A transaction that the writer refuses changes nothing and is no step of a
history; the contract speaks of the accepted ones. -/

/-- Clauses 1 and 2 of the contract, computed. -/
def contractOk (p : Params) (i : Time) (s : Tree) (ops : List Op) (s' : Tree) : Bool :=
  invOk p (s'.at i) && contents (s'.at i) == applyOps ops (contents (s.at (i - 1)))

/-- A node o of before the transaction at time i, and the same node o' after
it: the same kind; a value unchanged; a key node with its level, its kind and
its klongs kept, and klongs added only after a time klong of i. -/
def Ext (i : Time) : Obj → Obj → Prop
  | .val h, .val h' => h' = h
  | .key n, .key n' =>
    n'.level = n.level ∧ n'.leaf = n.leaf ∧
      (n'.ks = n.ks ∨ ∃ more, n'.ks = n.ks ++ Klong.time i :: more)
  | _, _ => False

/-- Clause 3 of the contract, the frame. -/
def Frame (i : Time) (s : Tree) (D : List NodeId) (s' : Tree) : Prop :=
  (∀ x o, s.obj x = some o → ∃ o', s'.obj x = some o' ∧ Ext i o o' ∧ (x ∉ D → o' = o)) ∧
  (∀ x n, s'.obj x = some (.key n) → s.obj x = none → x ∈ D) ∧
  (∃ new, s'.roots = s.roots ++ new ∧ ∀ r ∈ new, r.1 = i)

/-- The writer's contract for one transaction: at time i, from the tree s,
the operations `ops` end in the tree s' with the dirty nodes D. -/
def Contract (p : Params) (i : Time) (s : Tree) (ops : List Op) (D : List NodeId)
    (s' : Tree) : Prop :=
  contractOk p i s ops s' = true ∧ Frame i s D s'

/-- A tree to start from: at time 0 it meets the invariants and is empty. -/
def Start (p : Params) (s : Tree) : Prop :=
  invOk p (s.at 0) = true ∧ contents (s.at 0) = []

/-- A history that meets the contract: from a start tree, the transactions
txs in order, the j-th at time j, each meeting the writer's contract, end in
the tree s. -/
inductive Meets (p : Params) : List (List Op) → Tree → Prop where
  | start (s : Tree) : Start p s → Meets p [] s
  | step (txs : List (List Op)) (s : Tree) (ops : List Op) (D : List NodeId) (s' : Tree) :
      Meets p txs s → Contract p (txs.length + 1) s ops D s' → Meets p (txs ++ [ops]) s'

end Contract
