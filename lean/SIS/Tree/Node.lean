/-
The tree model (bergdb 024-12): a key node as its klongs, and what Java's
`KeyNode` computes on them. Trusted part: definitions that the statements of
SIS/Tree/Props.lean are about, and that the trace checker runs against Java
(Check/Tree.lean).

Each definition names the Java method it restates (java/src/bergdb/dag), case by
case; where Java's loop has an order, the fold has the same. Design: bergdb
024-12, section 2 (D1 to D8).
-/
import SIS.Tree.Val

namespace SIS.Tree

open SIS SIS.Check

/-! ## Parameters and levels (024-12, D5) -/

/-- The parameters of a tree: the node size M (`Dag.maxNodeSize`: 8, 14, 30 or
62), and the bounds of the levels: G, the largest segment index of a key node,
and H, the largest height of a key node in its segment tree. A run stays
within G and H, or its levels are not those of A4. -/
structure Params where
  M : Nat
  G : Nat
  H : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The largest level of a key node. -/
def Params.keyMax (p : Params) : Nat := 1 + p.G * (p.H + 1) + p.H

/-- The level of a key node in segment g at height h (0 for a segment leaf), as
`TraceExport.levelOf` gives it. -/
def Params.keyLevel (p : Params) (g h : Nat) : Nat := 1 + (p.G - g) * (p.H + 1) + h

/-- The height of a key node, from its level. -/
def Params.heightOf (p : Params) (level : Nat) : Nat := (level - 1) % (p.H + 1)

/-- The segment of a key node, from its level. -/
def Params.segOf (p : Params) (level : Nat) : Nat := p.G - (level - 1) / (p.H + 1)

/-- The level of the top node with ordinal o (`TopNode.topNodeId`). -/
def Params.topLevel (p : Params) (o : Nat) : Nat := p.keyMax + 1 + o

/-- The ordinal of a top node, from its level. -/
def Params.ordOf (p : Params) (level : Nat) : Nat := level - p.keyMax - 1

/-- The level of the root: above every top node (ordinals are below 2^48). -/
def Params.rootLevel (p : Params) : Nat := p.keyMax + 2 + (2 ^ 48 - 1)

/-! ## Klongs (024-12, D2) -/

/-- A klong of a key node (`Klong`): a time klong; a key klong, with its compare
value c and the node y that its pointer names; a delete bitmap, the indexes of
the klongs it deletes, ascending. -/
inductive Klong where
  | time (t : Time)
  | key (c : Nat) (y : NodeId)
  | del (bits : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A key node (`KeyNode`): whether it is a segment leaf, and its klongs. -/
structure KNode where
  leaf : Bool
  ks : List Klong
  deriving DecidableEq, Repr, Inhabited

/-- The union of two bitmaps. -/
def bitsUnion (a b : List Nat) : List Nat :=
  ((a ++ b).eraseDups).mergeSort (fun x y => decide (x ≤ y))

/-- `KeyNode.size`: the number of klongs, time klongs and bitmaps included. -/
def KNode.size (n : KNode) : Nat := n.ks.length

/-- The last bitmap of a list of klongs, none set if it has none
(`KeyNode.getLastDeleteBitmap`, `Dag.lastBitmap`). -/
def lastBitmapOf (ks : List Klong) : List Nat :=
  ks.foldl (fun d k => match k with
    | .del b => b
    | _ => d) []

def KNode.lastBitmap (n : KNode) : List Nat := lastBitmapOf n.ks

/-- The time of the last time klong (`Dag.lastTime`). -/
def KNode.lastTime (n : KNode) : Option Time :=
  n.ks.foldl (fun t k => match k with
    | .time x => some x
    | _ => t) none

/-- The time of the first time klong (`KeyNode.getFirstTime`). -/
def KNode.firstTime (n : KNode) : Option Time :=
  n.ks.findSome? (fun k => match k with
    | .time x => some x
    | _ => none)

/-- The index of the last time klong. -/
def KNode.lastTimeIndex (n : KNode) : Option Nat :=
  n.ks.zipIdx.foldl (fun t (k, i) => match k with
    | .time _ => some i
    | _ => t) none

/-- The bits of every key klong with compare value c (`Dag.bitsOf`). -/
def KNode.bitsOf (n : KNode) (c : Nat) : List Nat :=
  n.ks.zipIdx.filterMap (fun (k, i) => match k with
    | .key c' _ => if c' == c then some i else none
    | _ => none)

/-- Every key klong is deleted by `del` (`Dag.allKeysIn`). -/
def KNode.allKeysIn (n : KNode) (del : List Nat) : Bool :=
  n.ks.zipIdx.all (fun (k, i) => match k with
    | .key _ _ => del.contains i
    | _ => true)

/-- The smallest live compare value at the latest time (`Dag.smallestLive`). -/
def KNode.smallestLive (n : KNode) : Option Nat :=
  let del := n.lastBitmap
  n.ks.zipIdx.foldl (fun best (k, i) => match k with
    | .key c _ =>
      if del.contains i then best else
        match best with
        | none => some c
        | some b => if c < b then some c else some b
    | _ => best) none

/-- The index of the latest klong of the node's only live compare value; none
if it has no live klong, or two live compare values (`Dag.onlyLiveKlong`). -/
def KNode.onlyLiveKlong (n : KNode) : Option Nat :=
  let del := n.lastBitmap
  let r := n.ks.zipIdx.foldl (fun (acc : Option (Option (Nat × Nat))) (k, i) =>
    match acc with
    | none => none
    | some cur =>
      match k with
      | .key c _ =>
        if del.contains i then acc else
          match cur with
          | some (_, cv) => if c != cv then none else some (some (i, c))
          | none => some (some (i, c))
      | _ => acc) (some none)
  match r with
  | some (some (i, _)) => some i
  | _ => none

/-- The index of the live klong with compare value c that points to y: the last
klong of c, if it is not deleted and names y (`Dag.linkIndex`). -/
def KNode.linkIndex (n : KNode) (y : NodeId) (c : Nat) : Option Nat :=
  let del := n.lastBitmap
  match n.ks.zipIdx.reverse.find? (fun (k, _) => match k with
    | .key c' _ => c' == c
    | _ => false) with
  | some (.key _ y', i) => if !del.contains i && y' == y then some i else none
  | _ => none

/-- The node as it was at time t: the klongs before the first time klong after t
(`KeyNode.toPreviousState`; the readers' loops end there too). -/
def prefixAt (ks : List Klong) (t : Time) : List Klong :=
  ks.takeWhile (fun k => match k with
    | .time x => decide (x ≤ t)
    | _ => true)

def KNode.toPrev (n : KNode) (t : Time) : KNode := { n with ks := prefixAt n.ks t }

/-- Adds a klong at time t, with a time klong before it if t is after the node's
last time (`KeyNode.addKlong`, `addDeleteKlong`, `addKlongCopyPointer`). -/
def KNode.add (n : KNode) (t : Time) (k : Klong) : KNode :=
  match n.lastTime with
  | some lt => if lt < t then { n with ks := n.ks ++ [.time t, k] } else { n with ks := n.ks ++ [k] }
  | none => { n with ks := n.ks ++ [.time t, k] }

/-- Sets klong i. -/
def KNode.setAt (n : KNode) (i : Nat) (k : Klong) : KNode := { n with ks := n.ks.set i k }

/-- The node that pointer i names, if klong i is a key klong. -/
def KNode.ptr? (n : KNode) (i : Nat) : Option NodeId :=
  match n.ks[i]? with
  | some (.key _ y) => some y
  | _ => none

/-- The compare value of klong i, if it is a key klong. -/
def KNode.cv? (n : KNode) (i : Nat) : Option Nat :=
  match n.ks[i]? with
  | some (.key c _) => some c
  | _ => none

/-- Points key klong i to y (`KeyNode.repointKlong`, `copyPointer`). -/
def KNode.repoint (n : KNode) (i : Nat) (y : NodeId) : KNode :=
  match n.ks[i]? with
  | some (.key c _) => n.setAt i (.key c y)
  | _ => n

/-- `KeyNode.replaceKlong`: the first key klong with compare value c at time t
gets the pointer y; none if there is no such klong. A bitmap met before it is an
error, as in Java (the method is for last versions, which have none). -/
def replaceKlong (ks : List Klong) (t : Time) (c : Nat) (y : NodeId) :
    Except String (Option (List Klong)) :=
  go [] ks none
where
  go (pre rest : List Klong) (cur : Option Time) : Except String (Option (List Klong)) :=
    match rest with
    | [] => .ok none
    | .time x :: r => go (pre ++ [.time x]) r (some x)
    | .key c' y' :: r =>
      if c' == c && cur == some t then .ok (some (pre ++ .key c y :: r))
      else go (pre ++ [.key c' y']) r cur
    | .del _ :: _ => .error "replaceKlong: a key node with delete klongs"

/-- Sets the pointer for compare value c in a list ordered by first appearance. -/
def setCv (m : List (Nat × NodeId)) (c : Nat) (y : NodeId) : List (Nat × NodeId) :=
  if m.any (fun p => p.1 == c) then m.map (fun p => if p.1 == c then (c, y) else p)
  else m ++ [(c, y)]

/-- The last version at time t given the bitmap `del`: a time klong of t, then
one key klong for each compare value with a klong that `del` does not delete,
with the pointer of the last such klong, in increasing order of the compare
values (`KeyNode.lastVersionGivenDel`). -/
def KNode.lastVersionGivenDel (n : KNode) (t : Time) (del : List Nat) : KNode :=
  let m := n.ks.zipIdx.foldl (fun m (k, i) => match k with
    | .key c y => if del.contains i then m else setCv m c y
    | _ => m) []
  let s := m.mergeSort (fun a b => decide (a.1 ≤ b.1))
  { leaf := n.leaf, ks := .time t :: s.map (fun p => .key p.1 p.2) }

/-- `KeyNode.lastVersion`. -/
def KNode.lastVersion (n : KNode) (t : Time) : KNode := n.lastVersionGivenDel t n.lastBitmap

/-- The two halves of a space split (`KeyNode.firstAndSecond`): the last version
`last` (a time klong and sorted key klongs) cut after its first
(size - 1) / 2 + 1 klongs; the klongs `ins` appended to the second half if the
first of them is at or above the second half's first compare value, else to the
first half. An inner node's second half gets the empty key (compare value 0) for
its first klong, and a klong to insert with that klong's compare value too
(LE-b). Returns the halves and the second half's first compare value, which the
parent gets. -/
def halves (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    KNode × KNode × Nat :=
  let body := last.ks.drop 1
  let sizeOfFirst := (last.size - 1) / 2 + 1
  let f := body.take (sizeOfFirst - 1)
  let s := body.drop (sizeOfFirst - 1)
  let sc := match s.head? with
    | some (.key c _) => c
    | _ => 0
  let toSecond := match ins.head? with
    | some (c, _) => decide (sc ≤ c)
    | none => false
  let s := if leaf then s else match s with
    | .key _ y :: r => .key 0 y :: r
    | s => s
  let insK := ins.map (fun (c, y) =>
    if !leaf && toSecond && c == sc then Klong.key 0 y else Klong.key c y)
  if toSecond then (⟨leaf, .time t :: f⟩, ⟨leaf, .time t :: s ++ insK⟩, sc)
  else (⟨leaf, .time t :: f ++ insK⟩, ⟨leaf, .time t :: s⟩, sc)

/-- `Klong.getLength`: the number of key bytes of a segment, from its compare
value (the three bits above its lowest three). A segment of 7 bytes continues in
the next segment's tree; a key's last segment is shorter (`Keys.toSegments`). -/
def segLen (c : Nat) : Nat := (c / 8) % 8

/-! ## The searches (`KeyNode.searchEq` and the five others) -/

/-- What a search found: the klong's compare value, its index, the time of the
time klong before it, and the node its pointer names. -/
structure Found where
  c : Nat
  idx : Nat
  time : Time
  y : NodeId
  deriving DecidableEq, Repr, Inhabited

/-- The bitmap at time t: the last one before the first time klong after t
(`KeyNode.getDeleteBitmapAtTime`). -/
def KNode.delAt (n : KNode) (t : Time) : List Nat := lastBitmapOf (prefixAt n.ks t)

/-- `KeyNode.searchEq`: Java's loop, with the bitmaps in their order: a key klong
of c is the match; a bitmap that deletes the match leaves none. -/
def KNode.searchEq (n : KNode) (t : Time) (c : Nat) : Option Found :=
  ((prefixAt n.ks t).zipIdx.foldl
    (fun (acc : Option Time × List Nat × Option Found) (k, i) =>
      if acc.2.1.contains i then acc else
        match k with
        | .time x => (some x, acc.2.1, acc.2.2)
        | .key c' y => if c' == c then (acc.1, acc.2.1, some ⟨c, i, acc.1.getD 0, y⟩) else acc
        | .del b => (acc.1, b, match acc.2.2 with
          | some f => if b.contains f.idx then none else some f
          | none => none))
    (none, [], none)).2.2

/-- The common loop of the five other searches: over the klongs at time t that
the bitmap at t does not delete, a key klong replaces the best so far when
`better` says so. -/
def KNode.searchBy (n : KNode) (t : Time) (better : Nat → Option Nat → Bool) : Option Found :=
  let pre := prefixAt n.ks t
  let del := lastBitmapOf pre
  (pre.zipIdx.foldl (fun (acc : Option Time × Option Found) (k, i) =>
    if del.contains i then acc else
      match k with
      | .time x => (some x, acc.2)
      | .key c y =>
        if better c (acc.2.map (·.c)) then (acc.1, some ⟨c, i, acc.1.getD 0, y⟩) else acc
      | .del _ => acc) (none, none)).2

/-- True if there is no best yet, or r holds for it. -/
def bestOr (best : Option Nat) (r : Nat → Bool) : Bool :=
  match best with
  | none => true
  | some b => r b

/-- `KeyNode.searchLte`: the largest live compare value at or below `target`;
of klongs with one compare value, the last. A target is an integer: Java passes
-1 and `Long.MAX_VALUE` for "before every key" and "after every key". -/
def KNode.searchLte (n : KNode) (t : Time) (target : Int) : Option Found :=
  n.searchBy t (fun c best => bestOr best (fun b => decide (b ≤ c)) && decide ((c : Int) ≤ target))

/-- `KeyNode.searchLt`. -/
def KNode.searchLt (n : KNode) (t : Time) (target : Int) : Option Found :=
  n.searchBy t (fun c best => bestOr best (fun b => decide (b ≤ c)) && decide ((c : Int) < target))

/-- `KeyNode.searchGt`: the smallest live compare value above `target`. -/
def KNode.searchGt (n : KNode) (t : Time) (target : Int) : Option Found :=
  n.searchBy t (fun c best => bestOr best (fun b => decide (c ≤ b)) && decide (target < (c : Int)))

/-- `KeyNode.searchGte`. -/
def KNode.searchGte (n : KNode) (t : Time) (target : Int) : Option Found :=
  n.searchBy t (fun c best => bestOr best (fun b => decide (c ≤ b)) && decide (target ≤ (c : Int)))

/-- `KeyNode.searchFirst`: the smallest live compare value; Java's test is
strict, so of klongs with one compare value it keeps the first. -/
def KNode.searchFirst (n : KNode) (t : Time) : Option Found :=
  n.searchBy t (fun c best => bestOr best (fun b => decide (c < b)))

/-! ## Klongs and histories (024-12, D3 and D4) -/

/-- The marker entry (024-12, D4): a delete entry without compare values, at
time t, stands for a time klong of t that no klong follows before the next time
klong or the node's end. Java makes such a klong for its primordial key node
(`KeyNode.nodeWithTime`) and for a space root that a delete emptied by a time
split (an empty last version). The exporter writes no entry for it, so a trace's
P lacks it; the tree checker adds it for a key node made without entries
(Check/Tree.lean, `applyRec`). With it, klongs and histories correspond one to
one. A bitmap of Java's always has a new bit, so no bitmap gives the marker. -/
def marker : BVal := .del []

/-- The klongs of a key node of P, from its history: a time klong before each
run of entries of one time; a key entry is a key klong; a delete entry `D cs` is
a bitmap with the bits of the bitmap before it and of every key klong before it
whose compare value is in cs; the marker is its time klong alone. -/
def klongsOf (h : History BVal) : List Klong :=
  (h.foldl (fun (acc : List Klong × Option Time × List Nat) e =>
    let ks := if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]
    match e.val with
    | .key c y => (ks ++ [.key c y], some e.time, acc.2.2)
    | .del [] => (ks, some e.time, acc.2.2)
    | .del cs =>
      let more := ks.zipIdx.filterMap (fun (k, i) => match k with
        | .key c _ => if cs.contains c then some i else none
        | _ => none)
      let bits := bitsUnion acc.2.2 more
      (ks ++ [.del bits], some e.time, bits)
    | _ => (ks, some e.time, acc.2.2)) ([], none, [])).1

/-- The entries of a key node, from its klongs: `TraceExport.keyEntries`, and
the marker for a time klong that no klong follows. A bitmap's entry names the
compare values of its new bits, ascending. The state of the fold: the entries
so far, the time, the bitmap before, and whether the time klong has got an
entry. -/
def entriesOf (ks : List Klong) : History BVal :=
  let r := ks.foldl (fun (acc : History BVal × Time × List Nat × Bool) k =>
    match k with
    | .time t =>
      (if acc.2.2.2 then acc.1 else acc.1 ++ [⟨acc.2.1, marker⟩], t, acc.2.2.1, false)
    | .key c y => (acc.1 ++ [⟨acc.2.1, .key c y⟩], acc.2.1, acc.2.2.1, true)
    | .del bits =>
      let new := bits.filter (fun b => !acc.2.2.1.contains b)
      let cs := (new.filterMap (fun b => match (ks[b]? : Option Klong) with
        | some (.key c _) => some c
        | _ => none)).eraseDups.mergeSort (fun x y => decide (x ≤ y))
      (acc.1 ++ [⟨acc.2.1, .del cs⟩], acc.2.1, bits, true)) ([], 0, [], true)
  if r.2.2.2 then r.1 else r.1 ++ [⟨r.2.1, marker⟩]

end SIS.Tree
