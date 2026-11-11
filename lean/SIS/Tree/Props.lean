/-
The tree model (bergdb 024-12, section 6): the stated properties of BergDB's
key tree. Each is a definition of type `Prop`, named and documented, with its
proof left for later (bergdb 024-06: C1, C2, C3 and E): in this model every
theorem is proved in full, with nothing assumed, so a statement without a proof
is not written as a theorem. The item
lists them as TP1 to TP22 with what each means and how hard its proof looks.

The tree checker computes the invariants (`faultsAt`) on Java's structure
after every transaction, and the reads against a reference; SIS/Tree/Small.lean
runs them on small cases. That is evidence, not proof.
-/
import SIS.Tree.Inv
import SIS.Assumptions
import SIS.Phys
import SIS.Reclaim

namespace SIS.Tree

open SIS SIS.Check

/-! ## Runs -/

/-- P as the function that the tree's readers and its `exec` take. -/
def viewOf (P : Struct BVal) : View BVal := fun x => P.get? x

/-- The structure after the transactions ts, from the primordial one: each
transaction's `exec` on P@(i-1), applied. `SIS.run (treeSpec p)` computes the
same P whatever the algorithm's choices (`RunPSame`). -/
def treeRun (p : Params) (ts : List Tx) : Struct BVal :=
  ts.zipIdx.foldl (fun P (q : Tx × Nat) =>
    P.apply (q.2 + 1) (exec p q.1 (q.2 + 1) (view (treeSpec p) P q.2))) (initStruct p)

/-- An `Except` is a value. -/
def isOk {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/-- A run within the model's reach: every transaction has its keys strictly
increasing (one operation a key) and as `Keys.toSegments` makes them; no step of
the writer ends in an error (a `Bug`, a `corrupt` structure, or the level bounds
G and H); and each transaction's first id is above every id of the structure
before it (Java: a record's position is above every earlier one; 024-12, D8). -/
def Within (p : Params) (ts : List Tx) : Prop :=
  (∀ tx ∈ ts, tx.sorted = true ∧ tx.wf = true) ∧
  ∀ j (h : j < ts.length),
    (∀ q ∈ treeRun p (ts.take j), q.1 < ts[j].base) ∧
      isOk (exec? p ts[j] (j + 1) (view (treeSpec p) (treeRun p (ts.take j)) j)) = true

/-- The key node x of P, as klongs; none for a value, a top node or the root. -/
def keyNodeAt (p : Params) (P : Struct BVal) (x : NodeId) : Option KNode :=
  match P.get? x with
  | some nd =>
    if !nd.isData && decide (nd.level ≤ p.keyMax) then
      some { leaf := p.heightOf nd.level == 0, ks := klongsOf nd.hist }
    else none
  | none => none

/-- The key nodes reachable at time t, through the klongs live then. -/
def keyNodesAt (p : Params) (P : Struct BVal) (t : Time) : List NodeId :=
  match rootAt (viewOf P) t with
  | some r => nodesAt p (viewOf P) t p.fuel r
  | none => []

/-! ## The reference: a multiversion map -/

/-- The value of a key at time t in the run ts: that of its last operation in
T(1) to T(t), a put's value, none after a delete or without an operation. -/
def refGet (ts : List Tx) (t : Time) (key : Key) : Option Nat :=
  ((ts.take t).flatMap (·.ops)).foldl (fun v op =>
    if op.key == key then (match op with
      | .put _ h => some h
      | .del _ => none) else v) none

/-- The keys with a value at time t, in key order, each with its value. -/
def refKvs (ts : List Tx) (t : Time) : List (Key × Nat) :=
  let keys := (((ts.take t).flatMap (·.ops)).map (·.key)).eraseDups
  (keys.filterMap (fun k => (refGet ts t k).map (fun h => (k, h)))).mergeSort
    (fun a b => !keyLt b.1 a.1)

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

/-- What a scan with a limit gives, by the reference: the KVs at t in the range,
in key order forward, in reverse order backward, the first `limit`. -/
def refScan (ts : List Tx) (t : Time) (req : ScanReq) (limit : Nat) : List (Key × Nat) :=
  let kvs := (refKvs ts t).filter (fun q => inRange req q.1)
  (if req.forward then kvs else kvs.reverse).take limit

/-- A scan's request as the API allows it: keys as `Keys.toSegments` makes
them, an end key only forward. -/
def ScanReq.wf (req : ScanReq) : Bool :=
  (match req.start with
    | some s => keyWf s
    | none => true) &&
  (match req.endKey with
    | some e => keyWf e && req.forward
    | none => true)

/-! ## TP1 to TP8: the invariants of the tree -/

/-- TP1. Klongs and histories correspond: the entries of well-formed klongs
give the klongs back (D3, D4: the marker makes it one to one). With it,
`Tree.exec` reads from P exactly the nodes Java has. -/
def KlongsRoundTrip : Prop :=
  ∀ ks : List Klong, klongsWf ks = true → klongsOf (entriesOf ks) = ks

/-- TP2. The leftmost rule (LE-b, since 2026.4): at time t, the smallest live
klong of every reachable inner node is the empty key's. Every put relies on it
(`Dag.checkFound`). -/
def LeftmostOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∀ x ∈ keyNodesAt p P t, ∀ n, keyNodeAt p P x = some n → n.leaf = false →
    ((n.liveAt t).head?.map (·.1)) = some 0

/-- TP3. What UP leaves: at time t, every reachable key node but the space root
has a live klong. A deleted key keeps no node of its own. -/
def NonEmptyOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∀ x ∈ keyNodesAt p P t, ∀ n, keyNodeAt p P x = some n →
    rootAt (viewOf P) t ≠ some x → n.liveAt t ≠ []

/-- TP4. Pointers to written nodes: every node that an entry of a node of P
names, live or dead, is a node of P. A node that a transaction took back is
named by no klong (fault 12 of 023-08 broke this). -/
def PointersOK (P : Struct BVal) : Prop :=
  ∀ q ∈ P, ∀ e ∈ q.2.hist, ∀ y ∈ bptrs e.val, (P.get? y).isSome = true

/-- TP5. A key node has at most M klongs. -/
def SizeOK (p : Params) (P : Struct BVal) : Prop :=
  ∀ x n, keyNodeAt p P x = some n → n.size ≤ p.M

/-- TP6. All the invariants at time t, as the walk computes them (`walk`):
TP2, TP3 and TP5 for the nodes reachable at t, and with them the order
(`RangeOK`: every live compare value within the bounds that the klongs above
give its node, so a search by `searchLte` finds the node of every key), what
root collapse leaves (`RootsOK`: an inner root has two live klongs), the kinds
of the children (`KindsOK`), well-formed klongs, and pointers to nodes of P. -/
def InvOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  faultsAt p (viewOf P) t = []

/-- TP7. The invariants hold after every run within reach, at every time: the
B-tree proof, with time splits and segments. -/
def InvPreserved (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ t ≤ ts.length, InvOK p (treeRun p ts) t ∧ PointersOK (treeRun p ts)

/-- TP8. No `Bug`: for a run whose steps so far had no error, a transaction
with one operation a key, well-formed keys and a fresh base ends in no error
but the level bounds. Java's `Bug` throws of the delete path are unreachable. -/
def NoBug (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ tx : Tx, tx.sorted = true → tx.wf = true →
    (∀ q ∈ treeRun p ts, q.1 < tx.base) →
    ∀ e, exec? p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .error e →
      e.startsWith "bounds:" = true

/-! ## TP9 to TP12: the multiversion map (bergdb 024-06, C2) -/

/-- TP9. A search in a node is a lookup in its live klongs: `searchEq` at t
finds the klong of c that is live at t, if there is one. (The five other
searches have the same form.) -/
def SearchEqSpec : Prop :=
  ∀ (n : KNode) (t : Time) (c : Nat), klongsWf n.ks = true →
    (n.searchEq t c).map (·.y) = (n.liveAt t).lookup c

/-- TP10. BergDB is a multiversion map: a get at time t gives the value of the
key's last put at or before t, none if a delete came after it. -/
def GetOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ t ≤ ts.length, ∀ key, keyWf key = true →
    get p (viewOf (treeRun p ts)) t key = refGet ts t key

/-- TP11. A scan at time t gives the KVs of the map at t in its range, in key
order, forward or backward, with the end key (SE). -/
def ScanOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ t ≤ ts.length, ∀ (req : ScanReq) (limit : Nat), req.wf = true →
    (scan p (viewOf (treeRun p ts)) t req limit).map (fun kv => (kv.key, kv.h)) =
      refScan ts t req limit

/-- TP12. A delete of a key without a value changes nothing: no node, no entry
(a noop is not stored, and a rerun must give the same ids). -/
def NoopOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ (key : Key) (b : NodeId), keyWf key = true →
    refGet ts ts.length key = none →
    exec? p { base := b, ops := [.del key] } (ts.length + 1)
        (view (treeSpec p) (treeRun p ts) ts.length) = .ok { new := [], adds := [] }

/-! ## TP13 to TP19: the assumptions of the existing model (bergdb 024-06, C1) -/

/-- TP13. The structure's own assumptions: `SpecOK`, with `VirtInit`. -/
def SpecOKTree (p : Params) : Prop := SpecOK (treeSpec p)

/-- TP14. `RunOK`: every transaction of a run within reach meets A2 to A5, the
data node rules, fresh ids, and `VirtStep` (R1 to R4, dead top nodes), and its
touch the three touch rules. With it T1, T2 and T13 hold for BergDB's tree. -/
def RunOKTree (p : Params) : Prop :=
  ∀ (al : Algo BVal Tx) ts, Within p ts → RunOK (treeSpec p) al ts

/-- TP15. `PhysRunOK`: a node's new live children are pointees of its new
entries, and no child moves between current nodes (024-06, 4.4, point 1: argued
before the delete path existed, checked nowhere). With TP14, lazy reading. -/
def PhysRunOKTree (p : Params) : Prop :=
  ∀ (al : Algo BVal Tx) ts, Within p ts → PhysRunOK (treeSpec p) al ts

/-- TP16. `EvictRunOK`: TREE and A6' after every transaction, A-COPY for every
change. With TP14 and TP15, the theorems with handles. -/
def EvictRunOKTree (p : Params) : Prop :=
  ∀ (al : Algo BVal Tx) ts, Within p ts → EvictRunOK (treeSpec p) al ts

/-- TP17. `ExecRootOK`: a transaction sees the root only through its live
children (`topOfView` reads the root's last entry). For T8 and T12. -/
def ExecRootOKTree (p : Params) : Prop := ExecRootOK (treeSpec p)

/-- TP18. `VirtLiveOK`: the root's live children are those of its last entry
(a property of `blive`). -/
def VirtLiveOKTree (p : Params) : Prop := VirtLiveOK (treeSpec p)

/-- TP19. `exec` reads only nodes reachable at i-1 (it starts at the root and
follows live klongs), so P itself serves for P@(i-1): what the tree checker
gives it. And `treeRun` is the P of the model's `run`. -/
def ExecReadsReachable (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ tx : Tx,
    exec p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      exec p tx (ts.length + 1) (viewOf (treeRun p ts))

def RunPSame (p : Params) : Prop :=
  ∀ (al : Algo BVal Tx) ts, (run (treeSpec p) al ts).P = treeRun p ts

/-! ## TP20 to TP22: the costs (bergdb 024-04, aims 2 and 3; 024-06, C3 and E) -/

/-- TP20. An operation's work is bounded by its path: a transaction makes at
most, for each operation, a value, and three nodes for each level of the
longest path (two halves and a root), and one top node. A first statement of
aim 2 for the tree: the nodes made are proportional to the operations. -/
def MadeBound (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ (tx : Tx) (c : Changes BVal),
    exec? p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok c →
    c.new.length ≤ tx.ops.length * (3 * p.fuel + 1) + 1

/-- TP21. A deleted KV keeps no node (aim 3, first statement for the tree): at
every time, the key nodes reachable number at most one and, for each key with a
value then, the longest path. True at once after the delete, by UP (TP3). -/
def DeletedNoNode (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ t ≤ ts.length,
    (keyNodesAt p (treeRun p ts) t).length ≤ 1 + (refKvs ts t).length * p.fuel

/-- TP22. The klongs reachable at a time are at most M for each node of TP21:
storage in the tree is proportional to the KVs stored, with the constant M
times the longest path. What a deleted KV still costs is its dead klongs in
nodes that live keys keep, within this bound, until the node is split. -/
def KlongBound (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ t ≤ ts.length,
    ((keyNodesAt p (treeRun p ts) t).filterMap (keyNodeAt p (treeRun p ts))).foldl
        (fun s n => s + n.size) 0 ≤ p.M * (1 + (refKvs ts t).length * p.fuel)

/-- Not a property of release 2026.4's tree, and not to prove: no dead klong in
a reachable node. False since a leaf with a live key keeps its deleted keys'
klongs (024-05, ST4); the statement that compaction would have to make true
"eventually". Kept here so that the aim has a form. -/
def NoDeadKlongsAim (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ x ∈ keyNodesAt p (treeRun p ts) ts.length,
    ∀ n, keyNodeAt p (treeRun p ts) x = some n →
      (n.ks.filter (fun k => match k with
        | .key _ _ => true
        | _ => false)).length = (n.liveAt ts.length).length

end SIS.Tree
