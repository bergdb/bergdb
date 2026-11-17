/-
The contract package (bergdb 030-07): the bridge from the writer's contract to
the abstract model (self-indexed streams, lean/SIS: Basic.lean to
Assumptions.lean, Phys.lean). This is the file to read and to trust for the
bridge, with Statement.lean; the theorems that follow are in
BridgeTheorems.lean.

The abstract model knows nothing of klongs. It has nodes with entries, each
entry stamped with a time, and it takes each transaction's change as given:
the nodes made and the entries added. Its theorems (recovery, restarts, lazy
reading, eviction with handles, reclaim's cut) hold for any structure whose
changes meet its assumptions. Here:

* Section 1, the map. A key node's klongs as the model's entries
  (`entriesOf`), as Java's trace writes them (bergdb 027-02, section 1).
* Section 2, a history with what the bridge needs (`BHist`): after each
  transaction the tree, and the transaction's change in the model's terms
  (the trace's NEW, ADD and TOUCH lines). The model's instance for a history
  (`BHist.spec`) is the trace checker's own (`SIS.Check.bspec`, lean/Check).
* Section 3, the clauses that the contract lacks for the model (bergdb 030-06,
  findings 3 to 5). The ones about key nodes and values are in the contract's
  words, on the tree, and computed (`bridgeOk`). The ones about the root and
  the top nodes, which the contract's tree does not have, and the touch, TREE,
  A6' and A-COPY are in the model's words, on the model's structure of the
  history (`BHist.P`), each named.
* Section 4, a history that meets the contract and the bridge's clauses
  (`MeetsBridge`, and `MeetsEvict` for eviction).

The definitions here import the abstract model's definitions (lean/SIS, the
old package, by a Lake dependency) and none of its proofs of the tree
(SIS/Tree). They do not need Mathlib.
-/
import SIS.Assumptions
import SIS.Phys
import Check.Trace
import Contract.Statement

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal bptrs blive bspec)

/-! ## 1. The klongs as entries

English. The model's entries of a key node are its klongs but the time
klongs, in order (bergdb 027-02, section 1; `TraceExport.keyEntries`):

* a key klong with compare value c and pointee y is the entry `K c y`;
* a bitmap is the entry `D c1 ... cn`: the compare values of the key klongs
  that it deletes and the bitmap before it does not, in increasing order (it
  deletes every key entry before it with one of these compare values);
* a time klong is no entry; the entries after it, up to the next time klong,
  have its time.

A value with hash h is a data node with the one entry `V h`. -/

/-- The compare values of the new bits of the bitmap `bits`, in increasing
order: `pre` are the klongs before it, `before` the bitmap before it. -/
def newCvs (pre : List Klong) (before bits : List Nat) : List Nat :=
  (((bits.filter (fun j => !before.contains j)).filterMap (cvAt pre)).eraseDups).mergeSort
    (fun a b => decide (a ≤ b))

/-- The entries of the klongs `ks` that stand after the klongs `pre`, whose
last time klong has time t and whose last bitmap is `before`. -/
def entriesFrom (pre : List Klong) (t : Nat) (before : List Nat) : List Klong → History BVal
  | [] => []
  | .time t' :: r => entriesFrom (pre ++ [.time t']) t' before r
  | .key c y :: r => ⟨t, .key c y⟩ :: entriesFrom (pre ++ [.key c y]) t before r
  | .del bits :: r =>
    ⟨t, .del (newCvs pre before bits)⟩ :: entriesFrom (pre ++ [.del bits]) t bits r

/-- The entries of a key node's klongs. -/
def entriesOf (ks : List Klong) : History BVal := entriesFrom [] 0 [] ks

/-- The level of a node in the model: a key node's level; 0 for a value. -/
def lvl : Obj → Nat
  | .key n => n.level
  | .val _ => 0

/-- The model's structure P holds the tree s: every key node of s is an index
node of P with its level and the entries of its klongs; every value of s is a
data node of P on level 0 with its one entry. (The nodes of P that are no
nodes of s are the root and the top nodes.) -/
def Rep (P : Struct BVal) (s : Tree) : Prop :=
  ∀ x o, s.obj x = some o →
    match o with
    | .key n => P.get? x = some { level := n.level, isData := false, hist := entriesOf n.ks }
    | .val v => ∃ t, P.get? x = some { level := 0, isData := true, hist := [⟨t, .data v⟩] }

/-! ## 2. A history

English. A history is a start tree and, for each transaction in order, its
operations, the dirty nodes D and the tree when it ends, as in `Meets`, and
its change in the model's terms: the nodes it made, with their levels and
kinds (the trace's NEW lines), the entries it added (the ADD lines), and the
nodes its touch visited (the TOUCH line of a step of reclaim). The start has
the change that makes the primordial structure (the trace's TX 0).

The model's instance for a history is the trace checker's: the transactions
are the numbers 1, 2, ..., and transaction j's change is the history's. -/

/-- One transaction of a history. -/
structure BTx where
  /-- Its operations (the OP lines). -/
  ops : List Op
  /-- The dirty nodes when it ends, before its record is written. -/
  D : List NodeId
  /-- The tree when it ends. -/
  s : Tree
  /-- Its change in the model's terms (the NEW, ADD and TOUCH lines). -/
  c : Changes BVal

/-- A history: the start tree, the change that makes the primordial structure,
and the transactions. -/
structure BHist where
  s0 : Tree
  c0 : Changes BVal
  txs : List BTx

/-- The tree after the first j transactions. -/
def BHist.tree (h : BHist) : Nat → Tree
  | 0 => h.s0
  | j + 1 =>
    match h.txs[j]? with
    | some tx => tx.s
    | none => h.s0

/-- The changes by transaction number, the start's first (the trace checker's
`chs`). -/
def BHist.chs (h : BHist) : Array (Changes BVal) := (h.c0 :: h.txs.map (·.c)).toArray

/-- The model's primordial structure (the trace checker's `p0`). -/
def BHist.p0 (h : BHist) : Struct BVal := Struct.apply [] 0 h.c0

/-- The model's instance for the history: the trace checker's, with a virtual
root (`SIS.Check.bspec`): its entries are `BVal`, its pointers `bptrs`, its
live children `blive`, and the change of transaction j is the history's. -/
def BHist.spec (h : BHist) : Spec BVal Nat := bspec h.chs h.p0 true

/-- The model's transactions of the history: 1, 2, ..., n. -/
def BHist.ts (h : BHist) : List Nat := List.range' 1 h.txs.length

/-- The model's structure after the first j transactions: each change applied
at its time (`BridgeTheorems.lean`, `run_P`: it is the P of the model's
run). -/
def BHist.P (h : BHist) : Nat → Struct BVal
  | 0 => h.p0
  | j + 1 =>
    match h.txs[j]? with
    | some tx => (h.P j).apply (j + 1) tx.c
    | none => h.P j

/-! ## 3. The clauses

### 3.1 The start

English. The start is Java's primordial structure (the trace's TX 0): the
root, node 0; one key node r, a segment leaf with one time klong of time 0
and nothing else; one top node z, which names r. The tree has r alone, and r
is its space root from time 0. The levels: r above 0, z above r, the root
above z. -/

/-- The start of a history. -/
def StartB (h : BHist) : Prop :=
  ∃ r z lr lz l0, r ≠ 0 ∧ z ≠ 0 ∧ z ≠ r ∧ 0 < lr ∧ lr < lz ∧ lz < l0 ∧ lz ≤ 2 ^ 62 ∧
    h.c0.new = [⟨0, l0, false⟩, ⟨r, lr, false⟩, ⟨z, lz, false⟩] ∧
    h.c0.adds = [(0, .top z), (z, .rootKey r)] ∧
    h.s0.obj r = some (.key { level := lr, leaf := true, ks := [.time 0] }) ∧
    (∀ x, x ≠ r → h.s0.obj x = none) ∧ h.s0.roots = [(0, r)]

/-! ### 3.2 The nodes made, and the entries added (the map, as a clause)

English. For the transaction at time i from the tree s to the tree s', with
the change c:

* N. The nodes that c makes have distinct ids, and none is a node of s. A
  node made that is a key node of s' has the key node's level and is an index
  node; one that is a value of s' has level 0 and is a data node; one that is
  no node of s' is a top node: an index node on the top nodes' level or above.
  And every node of s' that is no node of s is made by c (`Made`).
* K. The entries that c adds to a node of s' are, in order, the entries of
  the klongs that the node got: for a key node of s, the entries of its klongs
  in s' after those of its klongs in s; for a key node made, the entries of
  its klongs; for a value made, its one entry; for a value of s, none. -/

/-- Clause N, computed. -/
def newsOk (topLevel : Nat) (s s' : Tree) (c : Changes BVal) : Bool :=
  decide (c.new.map (·.id)).Nodup &&
  c.new.all (fun nn => (s.obj nn.id).isNone &&
    match s'.obj nn.id with
    | some (.key n) => nn.level == n.level && !nn.isData
    | some (.val _) => nn.level == 0 && nn.isData
    | none => decide (topLevel ≤ nn.level) && !nn.isData)

/-- Clause N, the rest: every node of s' that is no node of s is made by c. -/
def Made (s s' : Tree) (c : Changes BVal) : Prop :=
  ∀ x, s.obj x = none → (s'.obj x).isSome = true → x ∈ c.new.map (·.id)

/-- The entry values that node x got, from the tree s to the tree s'. -/
def newVals (s s' : Tree) (x : NodeId) : List BVal :=
  match s'.obj x with
  | some (.key n') =>
    ((entriesOf n'.ks).drop (match s.obj x with
      | some (.key n) => (entriesOf n.ks).length
      | _ => 0)).map (·.val)
  | some (.val v) => if (s.obj x).isSome then [] else [.data v]
  | none => []

/-- Clause K, computed: for every node of s' that c gives an entry, that is in
D, or that c makes. (The other nodes of s' are unchanged, by the frame.) -/
def addsOk (s s' : Tree) (D : List NodeId) (c : Changes BVal) : Bool :=
  (c.adds.map (·.1) ++ D ++ c.new.map (·.id)).all (fun x =>
    (s'.obj x).isNone || (c.adds.filter (fun a => a.1 == x)).map (·.2) == newVals s s' x)

/-! ### 3.3 The key nodes of D

English. For every key node of s' that is in D (the frame puts every key node
changed or made there):

* F4. If it is a node of s, it is unchanged, or it got a time klong of i and
  after it at least one klong, none of them a time klong. If it is made, its
  klongs are a time klong of i and after it klongs that are no time klongs.
  So every klong added or made by the transaction has the time i.
* W. Its klongs are well formed (W1 to W4 of Statement.lean), and W5: for
  every compare value of a new bit of a bitmap, the bitmap deletes every key
  klong before it of that compare value (`Dag.bitsOf`: a delete sets the bits
  of every klong of its compare value). W4 asks this of the klongs before the
  new bit only; the map needs it of all the klongs before the bitmap
  (`W5.lean`: an example).
* A4. Every key klong of it, live or dead, names a node of s' on a lower
  level (a value has level 0). -/

/-- A time klong. -/
def Klong.isTime : Klong → Bool
  | .time _ => true
  | _ => false

/-- F4 for a key node made: a time klong of i, then no time klong. -/
def madeKs (i : Nat) : List Klong → Bool
  | .time t :: more => t == i && more.all (fun k => !k.isTime)
  | _ => false

/-- F4 for a key node of before with the klongs ks, now ks'. -/
def extKs4 (i : Nat) (ks ks' : List Klong) : Bool :=
  ks' == ks ||
    (ks.isPrefixOf ks' && madeKs i (ks'.drop ks.length) && decide (ks.length + 1 < ks'.length))

/-- W5 for the bitmap `bits` at index i, with `before` the bitmap before it. -/
def bmFull (ks : List Klong) (i : Nat) (before bits : List Nat) : Bool :=
  bits.all (fun j => before.contains j ||
    (List.range i).all (fun j' => cvAt ks j' != cvAt ks j || bits.contains j'))

/-- One step of the check of W5, as `bmStep`. -/
def fullStep (ks : List Klong) (acc : Bool × List Nat) (k : Klong) (i : Nat) : Bool × List Nat :=
  match k with
  | .del bits => (acc.1 && bmFull ks i acc.2 bits, bits)
  | _ => acc

/-- W5 for every bitmap. -/
def fullOk (ks : List Klong) : Bool :=
  (ks.zipIdx.foldl (fun acc ki => fullStep ks acc ki.1 ki.2) (true, [])).1

/-- A4 for key node n of the tree s. -/
def ptrsLow (s : Tree) (n : KNode) : Bool :=
  n.ks.all (fun k => match k with
    | .key _ y =>
      match s.obj y with
      | some o => decide (lvl o < n.level)
      | none => false
    | _ => true)

/-- F4, W and A4 for the key nodes of D, computed. -/
def localOk (i : Nat) (s s' : Tree) (D : List NodeId) : Bool :=
  D.all (fun x => match s'.obj x with
    | some (.key n') =>
      (match s.obj x with
        | some (.key n) => extKs4 i n.ks n'.ks
        | some (.val _) => false
        | none => madeKs i n'.ks) &&
      klongsWf n'.ks && fullOk n'.ks && ptrsLow s' n'
    | _ => true)

/-! ### 3.4 What is reached

English. The nodes reached: from the space root through the live klongs, key
nodes and values (`nodesAt`: the walk of `contents`).

* A2. An entry is added only to a node that s' reaches at time i. (An entry
  of a node that is no node of s' is the root's, node 0, or a made node's:
  the top's clause speaks of it.)
* A3. Every node made, key node or value, is reached by s' at time i.
* A5. Every node that s' reaches at time i was reached by s at time i - 1, or
  is made by the transaction: no node comes back. -/

/-- The nodes reached from key node x, x first; a value is reached from the
segment leaf that names it. -/
def nodesFrom (s : Tree) : Nat → NodeId → List NodeId
  | 0, _ => []
  | f + 1, x =>
    match s.obj x with
    | some (.key n) =>
      x :: (live n.ks).flatMap (fun cy =>
        match s.obj cy.2 with
        | some (.val _) => [cy.2]
        | _ => nodesFrom s f cy.2)
    | _ => []

/-- The nodes that the tree reaches. At time t: `nodesAt (s.at t)`. -/
def nodesAt (s : Tree) : List NodeId :=
  match s.root with
  | some r => nodesFrom s (s.fuel r) r
  | none => []

/-- Clause A2, computed, `now` the nodes that s' reaches at time i. -/
def currentOk (s' : Tree) (c : Changes BVal) (now : List NodeId) : Bool :=
  c.adds.all (fun a => match s'.obj a.1 with
    | some _ => now.contains a.1
    | none => a.1 == 0 || c.new.any (fun nn => nn.id == a.1))

/-- Clause A3, computed. -/
def madeOk (s' : Tree) (c : Changes BVal) (now : List NodeId) : Bool :=
  c.new.all (fun nn => (s'.obj nn.id).isNone || now.contains nn.id)

/-- Clause A5, computed, `before` the nodes that s reaches at time i - 1. -/
def noResOk (c : Changes BVal) (before now : List NodeId) : Bool :=
  now.all (fun y => before.contains y || c.new.any (fun nn => nn.id == y))

/-- The computed clauses of the bridge for one transaction: N, K, F4, W, A4,
A2, A3 and A5. `topLevel` is the level of the primordial top node. -/
def bridgeOk (topLevel : Nat) (i : Nat) (s s' : Tree) (D : List NodeId) (c : Changes BVal) :
    Bool :=
  newsOk topLevel s s' c && addsOk s s' D c && localOk i s s' D &&
  currentOk (s'.at i) c (nodesAt (s'.at i)) && madeOk (s'.at i) c (nodesAt (s'.at i)) &&
  noResOk c (nodesAt (s.at (i - 1))) (nodesAt (s'.at i))

/-! ### 3.5 The top (for bergdb 030-08)

English. The contract's tree has no top nodes: its top is the space root from
each time on. The model has the root, node 0, and under it the top nodes,
each with its root pointer to a key node and its skip pointers to older top
nodes. Until 030-08 puts the top nodes in the contract's tree, what the model
assumes of them is taken as it stands, on the model's structure P before the
transaction and P' after it:

* R1 to R4 and the dead top nodes (`VirtStep`): at most one top node made a
  transaction; a top node gets entries only when made; the root gets the
  entry for it, and no other; the top node made reaches every older one by
  skip pointers; a top node that a top node names is not reachable.
* For the nodes that are no nodes of the tree (the root and the top nodes),
  the model's assumptions on one transaction: the ids made are new; entries
  are added only to nodes reachable at i; such a node is no data node; its
  pointers go to lower levels; a node made is reachable at i; none comes
  back.
* The link: at time i the root's one live child is a top node, on a lower
  level, and its one live child is the space root of s', a key node on a lower
  level. The root and that top node are no nodes of s'. -/

/-- The link of the model's top to the tree's space root, at time i. -/
def TopLink (sp : Spec BVal Nat) (P : Struct BVal) (i : Nat) (s : Tree) : Prop :=
  ∃ n0 z nz y n, P.get? SIS.root = some n0 ∧ sp.live (n0.hist.upTo i) = [z] ∧
    P.get? z = some nz ∧ nz.level < n0.level ∧ sp.live (nz.hist.upTo i) = [y] ∧
    s.root = some y ∧ s.obj y = some (.key n) ∧ n.level < nz.level ∧
    s.obj SIS.root = none ∧ s.obj z = none

/-- The top's clauses for the transaction at time i with the change c, from
the tree s and the model's structure P to the tree s'. A premise named for
bergdb 030-08. -/
structure TopOK (sp : Spec BVal Nat) (P : Struct BVal) (i : Nat) (s s' : Tree)
    (c : Changes BVal) : Prop where
  virt : SIS.VirtStep sp P i c
  fresh : ∀ nn ∈ c.new, s.obj nn.id = none → P.get? nn.id = none
  current : ∀ a ∈ c.adds, s'.obj a.1 = none → SIS.reachable sp (P.apply i c) i a.1 = true
  dataFixed : ∀ a ∈ c.adds, s'.obj a.1 = none → ∀ n, P.get? a.1 = some n → n.isData = false
  levels : ∀ a ∈ c.adds, s'.obj a.1 = none → ∀ y ∈ sp.ptrs a.2, ∃ n m,
    (P.apply i c).get? a.1 = some n ∧ (P.apply i c).get? y = some m ∧ m.level < n.level
  newReachable : ∀ nn ∈ c.new, s'.obj nn.id = none →
    SIS.reachable sp (P.apply i c) i nn.id = true
  noRes : ∀ y, s'.obj y = none → SIS.reachable sp (P.apply i c) i y = true →
    SIS.reachable sp P (i - 1) y = true ∨ y ∈ c.new.map (·.id)
  link : TopLink sp (P.apply i c) i s'

/-! ### 3.6 The touch

English. A step of reclaim touches nodes without changing them
(`Db.touchPaths`; the trace's TOUCH line). The model's three rules, as they
stand, on the model's structure P before the transaction: a touched node is an
index node; it is reachable at time i - 1; and a node reachable at i - 1 with
a touched node below it is touched too, or is the root. A transaction without
a touch meets them. -/

/-- The touch rules for the change c at time i on the model's structure P. -/
structure TouchOK (sp : Spec BVal Nat) (P : Struct BVal) (i : Nat) (c : Changes BVal) :
    Prop where
  index : ∀ x ∈ c.touch, SIS.isIndex P x = true
  reach : ∀ x ∈ c.touch, SIS.reachable sp P (i - 1) x = true
  up : ∀ x ∈ c.touch, ∀ p np, SIS.reachable sp P (i - 1) p = true → P.get? p = some np →
    x ∈ SIS.reachFrom sp P (i - 1) p np → p ∈ c.touch ∨ p = SIS.root

/-! ## 4. A history that meets the contract and the bridge

English. `MeetsBridge`: the start is Java's primordial structure, and every
transaction, the j-th at time j, meets the writer's contract (Statement.lean,
section 5), the computed clauses of sections 3.2 to 3.4, `Made`, the top's
clauses and the touch rules.

`MeetsEvict` adds what the model assumes for eviction (`EvictRunOK`), as it
stands, on the model's structure: TREE after every transaction (every node
reachable but the root is the live child of exactly one reachable node; for
bergdb 030-08), A6' after every transaction (`adoptAt`: a pointer of a
reachable node that is not live names a data node, a node not reachable, or a
node below it), and A-COPY for every change (`CopyStep`: the pointer of a new
entry names a node made, a node of the writer's paths, or a pointee of one). -/

/-- The level of the top nodes of a history: the model's (`topLevelOf`). -/
def BHist.topLevel (h : BHist) : Nat := h.spec.topLevel

/-- A history that meets the contract and the bridge's clauses. -/
structure MeetsBridge (p : Params) (h : BHist) : Prop where
  start : StartB h
  step : ∀ j (hj : j < h.txs.length),
    Contract p (j + 1) (h.tree j) h.txs[j].ops h.txs[j].D (h.tree (j + 1)) ∧
    bridgeOk h.topLevel (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].D h.txs[j].c = true ∧
    Made (h.tree j) (h.tree (j + 1)) h.txs[j].c ∧
    TopOK h.spec (h.P j) (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].c ∧
    TouchOK h.spec (h.P j) (j + 1) h.txs[j].c

/-- What eviction needs besides: TREE and A6' after every transaction, A-COPY
for every change. -/
structure MeetsEvict (h : BHist) : Prop where
  tree : ∀ j ≤ h.txs.length, SIS.treeAt h.spec (h.P j) j
  adopt : ∀ j ≤ h.txs.length, SIS.adoptAt h.spec (h.P j) j
  copy : ∀ j (hj : j < h.txs.length), SIS.CopyStep h.spec (h.P j) (j + 1) h.txs[j].c

end Contract
