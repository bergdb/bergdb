/-
bergdb 030-21: PE, "plan, then emit" (026-23, section 1.2; the trial 026-24),
BergDB's writer as total functions on the contract's tree. Everything here
runs; nothing needs Mathlib.

The trial's program (`Pe/Plan.lean` on the branch `026-24-pe-trial`) ran on
today's model writer's state and was `partial`. This one reads the
contract's tree before the transaction (`Tree`) and gives the nodes it
writes, each once, the space roots and the top after it (`peTx`). Each
recursion has fuel; a run that runs out, or meets a tree that is not one of
PE's, refuses the transaction (none), as the trial threw an error. The
rules are the trial's (026-24, section 2.1), with three changes of form that
change no tree, only the ids that new nodes get (bergdb 030-21, section 2):

* a segment's tree is planned and emitted before the segment leaf above it
  is planned (`planTree`), so that the leaf gets the id of the next
  segment's root;
* a new node is a pointer of none in the decisions, not the trial's sentinel
  id 2^63.

The mechanism, for a transaction's operations at time i:

* plan, one recursion over the tree, lists only, from the space root. A key
  node touched by an operation becomes a virtual node (`VN.node`): its base
  (the node of the tree before, or none), its segment g and height h, its
  entries (compare value and child: an untouched node or value, `VN.old`, or
  a virtual node below), and its decision (`Dec`).
  - A segment leaf: its live list with the operations applied, by compare
    value in the order of their first operation (`applyGroups`): a put of a
    key that ends here sets a new value, a delete removes the entry; the
    operations of keys with more segments go to the next segment's tree
    (`planTree`), whose new root, or none, is the entry.
  - An inner node: the operations are divided among its children by its live
    list (`route`); plan runs on each child that got some (`planKids`); then
    `rebalance`: an empty child is dropped, a changed child with fewer than m
    entries is joined with a neighbour (M1: the left one if it exists and the
    two hold at most c, or there is no right one; else the right one; an
    untouched neighbour is opened, a planned one gives its entries before
    any cut), the joined list of two inner nodes rebalanced one level down;
    the first entry gets the empty key.
  - The decision (`decideNode`): `same` (the list is the base's live list),
    `append` (the base gets a time klong of i, a bitmap if a compare value
    left, and a key klong for each entry new or repointed, if it has room
    and stays within theta), or `parts k`: k new nodes, one if the list has
    at most h entries (c for a joined list) or the base is full by its dead
    klongs only, else ceil(n / cap) parts as even as possible. The list
    a decision counts is the node's final list F: its entries with each
    child's parts (`ents`), as emit will write them.
  - A root is settled alone (`settleRoot`): nothing left, the tree is empty
    (the space root: an empty segment leaf); an inner root with one entry,
    its child is the root; a root of k parts, a new root above.
* emit, after a segment's plan: bottom-up, each virtual node once, by its
  decision: nothing, klongs appended, or its final list cut into k new
  nodes with fresh ids (the parent gets an entry for each). Then the
  space root, if it changed, gets a new top node (`newTopNode`).
-/
import Contract.Top
import Contract.Shape

namespace Contract.PE

/-! ## Parameters -/

/-- The writer's parameters (record format 7's, from the trace's TREE line):
the node size M; the level bounds, segments 0 to G and heights 0 to H; m, a
changed child with fewer live klongs is joined with a neighbour (merges are
on from m = 2); c, the most entries of a joined node; h, a list of more
entries is cut; theta, the most dead klongs of a node (0: no bound); cap, the
most entries of a part of a cut list (the trial's mode pe: h). -/
structure Cfg where
  M : Nat
  G : Nat
  H : Nat
  m : Nat
  c : Nat
  h : Nat
  theta : Nat
  cap : Nat
  deriving Repr, Inhabited, DecidableEq

/-- The contract's parameters. -/
def Cfg.params (cf : Cfg) : Params := ⟨cf.M⟩

/-- Merges are on (`Params.merges`). -/
def Cfg.merges (cf : Cfg) : Bool := decide (2 ≤ cf.m)

/-- The level of a key node of segment g at height h (`Params.keyLevel`). -/
def Cfg.lev (cf : Cfg) (g h : Nat) : Nat := 1 + (cf.G - g) * (cf.H + 1) + h

/-- The segment of a key node, from its level (`Params.segOf`). -/
def Cfg.segOf (cf : Cfg) (l : Nat) : Nat := cf.G - (l - 1) / (cf.H + 1)

/-- The height of a key node, from its level (`Params.heightOf`). -/
def Cfg.htOf (cf : Cfg) (l : Nat) : Nat := (l - 1) % (cf.H + 1)

/-! ## Keys and operations -/

/-- The key of an operation. -/
def _root_.Contract.Op.key : Op → Key
  | .put k _ => k
  | .del k => k

/-- The operation's compare value at segment g. -/
def segAt (g : Nat) (op : Op) : Nat := (op.key[g]?).getD 0

/-- The operation's key ends at segment g. -/
def endsAt (g : Nat) (op : Op) : Bool := op.key.length == g + 1

/-- A key the tree can hold: as `Keys.toSegments` makes it, of at most G + 1
segments (the level bound G). -/
def keyOk (cf : Cfg) (k : Key) : Bool := keyWf k && decide (k.length ≤ cf.G + 1)

/-- The operations the writer accepts: keys the tree can hold. -/
def opsOk (cf : Cfg) (ops : List Op) : Bool := ops.all (fun op => keyOk cf op.key)

/-- The operations without the deletes of keys the tree cannot hold, which
change nothing (Java's Dag finds no such key). -/
def dropNoops (cf : Cfg) (ops : List Op) : List Op :=
  ops.filter (fun op => match op with
    | .del k => keyOk cf k
    | .put _ _ => true)

/-! ## Lists of entries -/

/-- The first entry of a list gets compare value c. -/
def renameHead {α : Type} (c : Nat) : List (Nat × α) → List (Nat × α)
  | [] => []
  | (_, y) :: r => (c, y) :: r

/-- The first compare value of a list, 0 if it is empty. -/
def headCv {α : Type} (l : List (Nat × α)) : Nat := (l.head?.map (·.1)).getD 0

/-- Sets the entry of compare value c in a list in compare order. -/
def setEntry {α : Type} (c : Nat) (v : α) : List (Nat × α) → List (Nat × α)
  | [] => [(c, v)]
  | (c', v') :: r =>
    if c < c' then (c, v) :: (c', v') :: r
    else if c = c' then (c, v) :: r
    else (c', v') :: setEntry c v r

/-- Removes the entry of compare value c. -/
def removeEntry {α : Type} (c : Nat) (es : List (Nat × α)) : List (Nat × α) :=
  es.filter (fun e => e.1 != c)

/-- The operations of each child, by the node's live list: the first child
every operation below the second compare value, each other child those from
its compare value to the next one's (the trial's division in `plan`). -/
def route {α β : Type} (cv : α → Nat) : List (Nat × β) → List α → List (List α)
  | [], _ => []
  | [_], ops => [ops]
  | _ :: (c', y) :: r, ops =>
    ops.filter (fun o => decide (cv o < c')) ::
      route cv ((c', y) :: r) (ops.filter (fun o => decide (c' ≤ cv o)))

/-- The sizes of k parts of n entries, as even as possible: the larger ones
first (`ceilFirst`, a merge's two nodes) or last (a space split's halves). -/
def partSizes (n k : Nat) (ceilFirst : Bool) : List Nat :=
  let b := n / k
  let e := n % k
  (List.range k).map (fun j =>
    if ceilFirst then (if j < e then b + 1 else b) else (if k - e ≤ j then b + 1 else b))

/-- A list cut into pieces of the given sizes. -/
def cutList {β : Type} (l : List β) : List Nat → List (List β)
  | [] => []
  | s :: r => l.take s :: cutList (l.drop s) r

/-- The parts of a list of n entries made new, of at most cap entries: one if
n is at most cap, else ceil(n / cap). -/
def nParts (cap n : Nat) : Nat :=
  let cap := max cap 1
  if n ≤ cap then 1 else (n + cap - 1) / cap

/-- The parts of a list of n entries that does not fit its base: one if n is
at most h, else at least two, of at most cap entries. -/
def cutParts (cf : Cfg) (n : Nat) : Nat :=
  if n ≤ cf.h then 1 else max 2 (nParts cf.cap n)

/-! ## The klongs that emit writes -/

/-- The compare values of a live list lb that a list F leaves out. -/
def removedCvs {β : Type} (lb : List (Nat × NodeId)) (F : List (Nat × β)) : List Nat :=
  (lb.filter (fun q => !(F.any (fun e => e.1 == q.1)))).map (·.1)

/-- The entries of F that are new or repointed against lb. -/
def addedOf (lb F : List (Nat × NodeId)) : List (Nat × NodeId) :=
  F.filter (fun e => lb.lookup e.1 != some e.2)

/-- The indexes of the key klongs of ks whose compare value is in R. -/
def bitsIn (ks : List Klong) (R : List Nat) : List Nat :=
  ks.zipIdx.filterMap (fun ki => match ki.1 with
    | .key c _ => if R.contains c then some ki.2 else none
    | _ => none)

/-- The bitmap that emit writes: the last bitmap and the bits of every klong of
the compare values removed. -/
def emitBits (ks : List Klong) (R : List Nat) : List Nat := lastBitmap ks ++ bitsIn ks R

/-- The head of emit's klongs for a base: a time klong of i, and a bitmap if a
compare value is removed. -/
def emitHead (i : Time) (ks : List Klong) (R : List Nat) : List Klong :=
  if R.isEmpty then [.time i] else [.time i, .del (emitBits ks R)]

/-- The key klongs of a list of entries. -/
def keysOf (A : List (Nat × NodeId)) : List Klong := A.map (fun e => .key e.1 e.2)

/-- emit's klongs for a base with klongs ks that is to hold F at time i. -/
def emitKs (i : Time) (ks : List Klong) (F : List (Nat × NodeId)) : List Klong :=
  emitHead i ks (removedCvs (live ks) F) ++ keysOf (addedOf (live ks) F)

/-- emit's klongs for a new node that is to hold F at time i. -/
def newKs (i : Time) (F : List (Nat × NodeId)) : List Klong := .time i :: keysOf F

/-! ## The virtual tree -/

/-- What emit does with a virtual node: nothing (its list is its base's live
list), klongs appended to its base, or k new nodes (cut by its parent when k
is 2 or more). -/
inductive Dec where
  | same
  | append
  | parts (k : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A planned subtree: an untouched node or value of the tree before, by id
(or a value made by the transaction); or a virtual key node with its base, its
segment g and height h (a segment leaf at height 0), whether it is a joined
list, its entries (each child before its cut), its final list F (the
entries with each child's parts, a new node's pointer none), and its
decision. -/
inductive VN where
  | old (y : NodeId)
  | node (base : Option NodeId) (g h : Nat) (join : Bool) (es : List (Nat × VN))
      (F : List (Nat × Option NodeId)) (dec : Dec)
  deriving Inhabited

/-- The entries a parent gets for a list F cut into k parts: the first keeps
the parent's compare value cv, each other one its first compare value; all
new. -/
def partEnts (cv : Nat) (F : List (Nat × Option NodeId)) (k : Nat) (join : Bool) :
    List (Nat × Option NodeId) :=
  match cutList F (partSizes F.length k join) with
  | [] => [(cv, none)]
  | _ :: rest => (cv, none) :: rest.map (fun part => (headCv part, none))

/-- The entries a parent gets for its child (cv, v): one, or one for each part
(the trial's `VN.ents`). -/
def ents (cv : Nat) : VN → List (Nat × Option NodeId)
  | .old y => [(cv, some y)]
  | .node base _ _ join _ F dec =>
    match dec, base with
    | .parts k, _ => if 2 ≤ k then partEnts cv F k join else [(cv, none)]
    | _, some b => [(cv, some b)]
    | _, none => [(cv, none)]

/-- The number of entries of a virtual node (its final list's length). -/
def VN.size : VN → Nat
  | .old _ => 0
  | .node _ _ _ _ _ F _ => F.length

/-- A virtual node that holds nothing. -/
def VN.isEmpty : VN → Bool
  | .old _ => false
  | .node _ _ _ _ _ F _ => F.isEmpty

/-- A virtual node that changed (its decision is not `same`). -/
def VN.changed : VN → Bool
  | .old _ => false
  | .node _ _ _ _ _ _ dec => dec != .same

/-- Key node x of the tree. -/
def getKey (s : Tree) (x : NodeId) : Option KNode :=
  match s.obj x with
  | some (.key n) => some n
  | _ => none

/-! ## The decision of a virtual node -/

/-- An entry of F counts as added against the live list lb: new, or a pointer
that lb does not have for its compare value. -/
def isAdded (lb : List (Nat × NodeId)) (e : Nat × Option NodeId) : Bool :=
  match e.2 with
  | none => true
  | some y => lb.lookup e.1 != some y

/-- The klongs that emit appends to base ks to reach F, with id 0 for a new
node: their count and their dead klongs do not depend on the ids. -/
def appendKsO (i : Time) (ks : List Klong) (F : List (Nat × Option NodeId)) : List Klong :=
  emitHead i ks (removedCvs (live ks) F) ++
    (F.filter (isAdded (live ks))).map (fun e => .key e.1 (e.2.getD 0))

/-- More than theta dead klongs (`deadOver`). -/
def deadOver (cf : Cfg) (ks : List Klong) : Bool := cf.theta != 0 && decide (cf.theta < deadCount ks)

/-- Emit's decision for a virtual node with base n (or none) and final list F
(the trial's `decideNode`). -/
def decideNode (cf : Cfg) (i : Time) (base : Option KNode) (join : Bool)
    (F : List (Nat × Option NodeId)) : Dec :=
  match base with
  | some n =>
    if (live n.ks).map (fun q => (q.1, some q.2)) == F then .same
    else
      let ks := appendKsO i n.ks F
      if n.ks.length + ks.length ≤ cf.M then
        if deadOver cf (n.ks ++ ks) then
          (if F.length + 1 ≤ cf.M then .parts 1 else .parts (cutParts cf F.length))
        else .append
      else .parts (cutParts cf F.length)
  | none => .parts (if join then nParts cf.c F.length else cutParts cf F.length)

/-- A virtual node from its entries (an inner node's first entry gets the
empty key): its final list and its decision. A new node outside the level
bounds is refused. -/
def mkNode (cf : Cfg) (i : Time) (s : Tree) (base : Option NodeId) (g h : Nat) (join : Bool)
    (es0 : List (Nat × VN)) : Option VN :=
  let es := if h == 0 then es0 else renameHead 0 es0
  let F0 := es.flatMap (fun e => ents e.1 e.2)
  let F := if h == 0 then F0 else renameHead 0 F0
  match base with
  | some b =>
    match getKey s b with
    | some n => some (.node (some b) g h join es F (decideNode cf i (some n) join F))
    | none => none
  | none =>
    if cf.G < g || cf.H < h then none
    else some (.node none g h join es F (decideNode cf i none join F))

/-! ## Rebalance -/

/-- The entries of a child for a join: an untouched node opened, each of its
live klongs an untouched child. -/
def openEs (s : Tree) : VN → Option (List (Nat × VN))
  | .old y =>
    match getKey s y with
    | some n => some ((live n.ks).map (fun q => (q.1, VN.old q.2)))
    | none => none
  | .node _ _ _ _ es _ _ => some es

/-- The live count of a child, for M1. -/
def cntOf (s : Tree) : VN → Nat
  | .old y => match getKey s y with
    | some n => (live n.ks).length
    | none => 0
  | v => v.size

/-- The first changed child with fewer than m entries. -/
def findSmall (cf : Cfg) (es : List (Nat × VN)) : Option Nat :=
  (es.zipIdx.find? (fun p => p.1.2.changed && decide (p.1.2.size < cf.m))).map (·.2)

/-- One join of rebalance at the children's height h (the trial's loop body):
the small child at ix with a neighbour by M1, the joined list of two inner
nodes rebalanced one level down by `down`. -/
def joinAt (cf : Cfg) (i : Time) (s : Tree) (g h : Nat)
    (down : List (Nat × VN) → Option (List (Nat × VN))) (es : List (Nat × VN)) (ix : Nat) :
    Option (List (Nat × VN)) :=
  let useLeft : Bool := match es[ix]? with
    | none => false
    | some x =>
      if ix == 0 then false
      else match es[ix - 1]?, es[ix + 1]? with
        | some _, none => true
        | some l, some _ => decide (cntOf s l.2 + x.2.size ≤ cf.c)
        | none, _ => false
  let il := if useLeft then ix - 1 else ix
  match es[il]?, es[il + 1]? with
  | some l, some r =>
    match openEs s l.2, openEs s r.2 with
    | some esL, some esR =>
      let J := esL ++ (if h == 0 then esR else renameHead r.1 esR)
      let J' := if h == 0 then some J else down J
      match J' with
      | some J' =>
        match mkNode cf i s none g h true J' with
        | some v => some (es.take il ++ [(l.1, v)] ++ es.drop (il + 2))
        | none => none
      | none => none
    | _, _ => none
  | _, _ => none

/-- The trial's loop of joins, n rounds at most. -/
def joinLoop (cf : Cfg) (i : Time) (s : Tree) (g h : Nat)
    (down : List (Nat × VN) → Option (List (Nat × VN))) : Nat → List (Nat × VN) →
    Option (List (Nat × VN))
  | 0, es => some es
  | n + 1, es =>
    if es.length < 2 then some es
    else
      match findSmall cf es with
      | none => some es
      | some ix =>
        match joinAt cf i s g h down es ix with
        | some es' => joinLoop cf i s g h down n es'
        | none => none

/-- The children of an inner node, at height h, rebalanced: an empty child is
dropped; while a changed child holds fewer than m entries and has a
neighbour, it is joined with one (M1); a joined list of two inner nodes is
rebalanced one level down. -/
def rebalance (cf : Cfg) (i : Time) (s : Tree) : Nat → Nat → Nat → List (Nat × VN) →
    Option (List (Nat × VN))
  | 0, _, _, _ => none
  | f + 1, g, h, es0 =>
    let es := es0.filter (fun e => !e.2.isEmpty)
    if !cf.merges then some es
    else joinLoop cf i s g h (fun J => rebalance cf i s f g (h - 1) J) (es.length + 1) es

/-! ## Emit -/

/-- The nodes written so far, the latest first, and the next fresh id. -/
structure Acc where
  ws : List (NodeId × Obj)
  next : NodeId
  deriving Inhabited

/-- A fresh id. -/
def Acc.fresh (a : Acc) : NodeId × Acc := (a.next, { a with next := a.next + 1 })

/-- Node x written. -/
def Acc.write (a : Acc) (x : NodeId) (o : Obj) : Acc := { a with ws := (x, o) :: a.ws }

/-- New nodes of segment g at height h for the parts of a list, each with a
fresh id (an inner part's first entry gets the empty key): the entries the
parent gets, each part's first compare value (the first part's 0). -/
def newParts (cf : Cfg) (i : Time) (g h : Nat) : List (List (Nat × NodeId)) → Acc →
    List (Nat × NodeId) × Acc
  | [], acc => ([], acc)
  | P :: Ps, acc =>
    let (z, acc) := acc.fresh
    let acc := acc.write z (.key ⟨cf.lev g h, h == 0, newKs i (if h == 0 then P else renameHead 0 P)⟩)
    let (E, acc) := newParts cf i g h Ps acc
    ((headCv P, z) :: E, acc)

mutual

/-- emit: the virtual node written, after its children, by its decision: its
base kept, klongs appended to its base, or its final list cut into k new
nodes. Gives the entries its parent gets: one a node, the first with compare
value 0 (the parent puts its own). -/
def emit (cf : Cfg) (i : Time) (s : Tree) : VN → Acc → Option (List (Nat × NodeId) × Acc)
  | .old y, acc => some ([(0, y)], acc)
  | .node base g h join es _ dec, acc =>
    match emitKids cf i s es acc with
    | none => none
    | some (F0, acc) =>
      let F := if h == 0 then F0 else renameHead 0 F0
      match dec, base with
      | .same, some b => some ([(0, b)], acc)
      | .append, some b =>
        match getKey s b with
        | some n => some ([(0, b)], acc.write b (.key { n with ks := n.ks ++ emitKs i n.ks F }))
        | none => none
      | .parts k, _ => some (newParts cf i g h (cutList F (partSizes F.length k join)) acc)
      | _, none => none

/-- emit on a list of entries: each child's entries, the first with the
child's compare value. -/
def emitKids (cf : Cfg) (i : Time) (s : Tree) : List (Nat × VN) → Acc →
    Option (List (Nat × NodeId) × Acc)
  | [], acc => some ([], acc)
  | (c, v) :: rest, acc =>
    match emit cf i s v acc with
    | none => none
    | some (E, acc) =>
      match emitKids cf i s rest acc with
      | none => none
      | some (F, acc) => some (renameHead c E ++ F, acc)

end

/-! ## Settle a root -/

/-- A root settled alone. For the space root (`space`), nothing left is an
empty segment leaf, not no tree (`some none`). -/
def settleRoot (cf : Cfg) (i : Time) (s : Tree) : Nat → Nat → VN → Bool → Option (Option VN)
  | 0, _, _, _ => none
  | f + 1, g, v, space =>
    match v with
    | .old y =>
      match getKey s y with
      | some n =>
        match live n.ks with
        | [(_, z)] => if n.leaf then some (some v) else settleRoot cf i s f g (.old z) space
        | _ => some (some v)
      | none => none
    | .node _ _ h _ es F dec =>
      if F.isEmpty then
        if !space then some none
        else if h == 0 then some (some v)
        else (mkNode cf i s none g 0 false []).map some
      else if h != 0 && F.length == 1 then
        match es with
        | [(_, ch)] => settleRoot cf i s f g ch space
        | _ => none
      else
        match dec with
        | .parts k =>
          if 2 ≤ k then
            match mkNode cf i s none g (h + 1) false [(0, v)] with
            | some r => settleRoot cf i s f g r space
            | none => none
          else some (some v)
        | _ => some (some v)

/-! ## Plan -/

mutual

/-- plan(x, ops) for key node x of the tree before, of segment g at height h. -/
def plan (cf : Cfg) (i : Time) (s : Tree) : Nat → NodeId → Nat → Nat → List Op → Acc →
    Option (VN × Acc)
  | 0, _, _, _, _, _ => none
  | f + 1, x, g, h, ops, acc =>
    match getKey s x with
    | none => none
    | some n =>
      if h == 0 then
        match applyGroups cf i s f g (live n.ks) ((ops.map (segAt g)).eraseDups) ops acc with
        | none => none
        | some (es, acc) =>
          match mkNode cf i s (some x) g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
          | some v => some (v, acc)
          | none => none
      else
        let lv := live n.ks
        match planKids cf i s f g h lv (route (segAt g) lv ops) acc with
        | none => none
        | some (es, acc) =>
          match rebalance cf i s (f + 1) g (h - 1) es with
          | none => none
          | some es2 =>
            match mkNode cf i s (some x) g h false es2 with
            | some v => some (v, acc)
            | none => none

/-- The children of an inner node at height h, each with its operations:
untouched if it has none, else planned one height down. -/
def planKids (cf : Cfg) (i : Time) (s : Tree) : Nat → Nat → Nat → List (Nat × NodeId) →
    List (List Op) → Acc → Option (List (Nat × VN) × Acc)
  | 0, _, _, _, _, _ => none
  | _ + 1, _, _, [], _, acc => some ([], acc)
  | f + 1, g, h, (c, y) :: rest, o :: os, acc =>
    if o.isEmpty then
      match planKids cf i s f g h rest os acc with
      | some (es, acc) => some ((c, VN.old y) :: es, acc)
      | none => none
    else
      match plan cf i s f y g (h - 1) o acc with
      | none => none
      | some (v, acc) =>
        match planKids cf i s f g h rest os acc with
        | some (es, acc) => some ((c, v) :: es, acc)
        | none => none
  | _ + 1, _, _, _ :: _, [], _ => none

/-- A segment leaf's entries with the operations applied, compare value by
compare value: a put of a key that ends here sets a new value, a delete
removes the entry; the operations of keys with more segments go to the next
segment's tree, whose new root, or none, is the entry. -/
def applyGroups (cf : Cfg) (i : Time) (s : Tree) : Nat → Nat → List (Nat × NodeId) →
    List Nat → List Op → Acc → Option (List (Nat × NodeId) × Acc)
  | 0, _, _, _, _, _ => none
  | _ + 1, _, es, [], _, acc => some (es, acc)
  | f + 1, g, es, cv :: cvs, ops, acc =>
    let grp := ops.filter (fun op => segAt g op == cv)
    let (es, acc) := (grp.filter (endsAt g)).foldl (fun (q : List (Nat × NodeId) × Acc) op =>
      match op with
      | .put _ hv =>
        let (y, a) := q.2.fresh
        (setEntry cv y q.1, a.write y (.val hv))
      | .del _ => (removeEntry cv q.1, q.2)) (es, acc)
    let subs := grp.filter (fun op => !endsAt g op)
    if subs.isEmpty then applyGroups cf i s f g es cvs ops acc
    else
      match planTree cf i s f (es.lookup cv) (g + 1) subs acc with
      | none => none
      | some (some y, acc) => applyGroups cf i s f g (setEntry cv y es) cvs ops acc
      | some (none, acc) => applyGroups cf i s f g (removeEntry cv es) cvs ops acc

/-- The tree of segment g with the operations, from its root (none: no tree
yet): planned, its root settled, emitted. Gives its new root, or none if it
is empty. -/
def planTree (cf : Cfg) (i : Time) (s : Tree) : Nat → Option NodeId → Nat → List Op → Acc →
    Option (Option NodeId × Acc)
  | 0, _, _, _, _ => none
  | f + 1, root, g, ops, acc =>
    let planned : Option (VN × Acc) :=
      match root with
      | some r =>
        match getKey s r with
        | some n => plan cf i s f r g (cf.htOf n.level) ops acc
        | none => none
      | none =>
        match applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc with
        | some (es, acc) =>
          (mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2)))).map (·, acc)
        | none => none
    match planned with
    | none => none
    | some (v, acc) =>
      match settleRoot cf i s f g v false with
      | none => none
      | some none => some (none, acc)
      | some (some v) =>
        match emit cf i s v acc with
        | some ([(_, y)], acc) => some (some y, acc)
        | _ => none

end

/-! ## The top -/

/-- `TopNode.height`: the number of skip pointers of the top node with
ordinal o. -/
def topHeight (o : Nat) : Nat := if o == 0 then 0 else Nat.log2 o + 1

/-- The new top node of a transaction at time i whose space root is r
(`TopDs.newSuperRoot`): its ordinal is the top's length (the start top node
has ordinal 0, each new one the next); a skip pointer at each set bit j of
the ordinal: the super root's skip pointer of index j, or the super root;
each with its target's root time. -/
def newTopNode (tp : Top) (i : Time) (r : NodeId) : TopNode :=
  match tp.getLast? with
  | none => ⟨i, r, []⟩
  | some (w, nw) =>
    let o := tp.length
    let skips := (List.range (topHeight o)).filterMap (fun j =>
      if o.testBit j then
        match nw.skips.find? (fun q => q.1 == j) with
        | some q => some q
        | none => some (j, w, nw.time)
      else none)
    ⟨i, r, skips⟩

/-! ## The transaction -/

/-- What a transaction writes: the nodes, the latest first (each once); the
space roots and the top after it; the next fresh id. -/
structure Out where
  ws : List (NodeId × Obj)
  roots : List (Time × NodeId)
  top : Top
  next : NodeId

/-- The tree after the writes ws, with the space roots `roots`: a node
written, else as before. -/
def applyWs (s : Tree) (ws : List (NodeId × Obj)) (roots : List (Time × NodeId)) : Tree :=
  { obj := fun x => match ws.lookup x with
      | some o => some o
      | none => s.obj x,
    roots := roots }

/-- The tree after the transaction. -/
def Out.tree (s : Tree) (o : Out) : Tree := applyWs s o.ws o.roots

/-- The dirty nodes: the nodes written. -/
def Out.D (o : Out) : List NodeId := o.ws.map (·.1)

/-- The fuel of the writer's recursions: far more than any tree within the
level bounds and any transaction needs. -/
def fuel : Nat := 2 ^ 40

/-- PE's transaction at time i on the tree s with the top tp, the next fresh
id `next`, and the operations ops0: the deletes of keys the tree cannot hold
dropped; plan from the space root, settle it, emit, and a new top node if the
space root changed. None: refused (a put of a key that is not well formed or
has more than G + 1 segments, a node outside the level bounds, or a tree
that is not one of PE's). -/
def peTx (cf : Cfg) (i : Time) (s : Tree) (tp : Top) (next : NodeId) (ops0 : List Op) :
    Option Out :=
  let ops := dropNoops cf ops0
  if !opsOk cf ops then none else
  match s.root with
  | none => none
  | some r =>
    match getKey s r with
    | none => none
    | some n =>
      match plan cf i s fuel r 0 (cf.htOf n.level) ops ⟨[], next⟩ with
      | none => none
      | some (v, acc) =>
        match settleRoot cf i s fuel 0 v true with
        | some (some rv) =>
          match emit cf i s rv acc with
          | some ([(_, r')], acc) =>
            if r' == r then some ⟨acc.ws, s.roots, tp, acc.next⟩
            else
              let (z, acc) := acc.fresh
              some ⟨acc.ws, s.roots ++ [(i, r')], tp ++ [(z, newTopNode tp i r')], acc.next⟩
          | _ => none
        | _ => none

/-! ## The start -/

/-- The start: the empty tree, an empty segment leaf of segment 0 at height 0
(id 1) as the space root of time 0, named by the start top node (id 2); the
next fresh id 3. -/
def startTree (cf : Cfg) : Tree :=
  { obj := fun x => if x == 1 then some (.key ⟨cf.lev 0 0, true, [.time 0]⟩) else none,
    roots := [(0, 1)] }

def startTop : Top := [(2, ⟨0, 1, []⟩)]

def startNext : NodeId := 3

end Contract.PE
