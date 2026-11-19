/-
The tree model's writer since record format 8 (bergdb 026-25): PE, "plan, then
emit" (026-23, section 1.2; the trial 026-24; the proof 030-21), Java's
`Dag.putKvs` (java/src/bergdb/dag/PeWriter.java). The tree checker
(Check/Tree.lean, Check/TreeRun.lean) runs it against Java's traces: node for
node, with the ids.

A copy of lean/contract's `Contract.PE` (Contract/PeWriter.lean, the writer
that 030-21 proves to meet the writer's contract), on the model's P instead of
the contract's tree. The package `contract` imports this one, so this one
cannot import it; 026-25's `pecmp` (items/026-release-2026-6/25-pe-java/)
runs both on the traces and finds the same trees, ids renamed. The rules are
PeWriter.lean's, word for word; what differs is not a rule:

* the ids are Java's: a fresh id is the next vpos (`Db.setIdOfNode`, the next
  id two on), from the transaction's first id, and a delete that deletes gets
  one too, for its delete node (`ValueNode.createDelete`), where PeWriter.lean
  gives none; the order of the fresh ids is PeWriter.lean's;
* a bitmap is kept as its bits in increasing order without repeats, as Java's
  `long` and the trace's KN lines have it (`bitsUnion`); PeWriter.lean's list
  may repeat a bit;
* the parameters are the trace's (`Params`: M, G, H, m, c, h, theta) and the
  cut size, `cutSize`, M / 2 (Java's `Dag.cutSize`; 026-24, section 2.6);
* the result is the model's writer state `W` (Exec.lean), so that the checks
  of `Tree.exec` run on it unchanged: its key nodes, the values, the nodes
  made, the top node; each operation's noop flag, a delete of a key with no
  value at i - 1 (`get`).

The mechanism is PeWriter.lean's header; each definition here names the one it
copies.
-/
import SIS.Tree.Spec

namespace SIS.Tree.Pe

open SIS SIS.Check SIS.Tree

/-! ## Parameters -/

/-- PeWriter.lean's `Cfg`. -/
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

/-- The cut size: the most entries of a part of a list that is cut, M / 2
(Java's `Dag.cutSize`; 026-24, section 2.6, the trial's recommendation). -/
def cutSize (M : Nat) : Nat := M / 2

/-- The writer's parameters from the trace's (`Params`), and the cut size. -/
def Cfg.of (p : Params) : Cfg :=
  { M := p.M, G := p.G, H := p.H, m := p.mergeBelow, c := p.mergeMax, h := p.splitAbove,
    theta := p.theta, cap := cutSize p.M }

def Cfg.merges (cf : Cfg) : Bool := decide (2 ≤ cf.m)

def Cfg.lev (cf : Cfg) (g h : Nat) : Nat := 1 + (cf.G - g) * (cf.H + 1) + h

def Cfg.htOf (cf : Cfg) (l : Nat) : Nat := (l - 1) % (cf.H + 1)

/-! ## The tree before: key nodes by id -/

/-- A key node of P@(i-1) as PeWriter.lean's `KNode`: its level, whether it is
a segment leaf, its klongs. -/
structure PNode where
  level : Nat
  leaf : Bool
  ks : List Klong
  deriving DecidableEq, Repr, Inhabited

/-- A node written: a key node, or a value (its hash). -/
inductive Obj where
  | key (n : PNode)
  | val (h : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The key nodes of P@(i-1), as the writer reads them. -/
abbrev Look := NodeId → Option PNode

/-- Key node x of P@(i-1), from its history (`klongsOf`). -/
def lookOf (p : Params) (view : View BVal) : Look := fun x =>
  match view x with
  | some nd =>
    if nd.isData || p.keyMax < nd.level || nd.level == 0 then none
    else some ⟨nd.level, p.heightOf nd.level == 0, klongsOf nd.hist⟩
  | none => none

/-! ## The contract's live klongs and dead count (Contract/Tree.lean, Shape.lean) -/

def insertCv (c : Nat) (y : NodeId) : List (Nat × NodeId) → List (Nat × NodeId)
  | [] => [(c, y)]
  | (c', y') :: r =>
    if c < c' then (c, y) :: (c', y') :: r
    else if c = c' then (c, y) :: r
    else (c', y') :: insertCv c y r

def liveWith (del : List Nat) (ks : List (Klong × Nat)) : List (Nat × NodeId) :=
  ks.foldl (fun m (k, i) => match k with
    | .key c y => if del.contains i then m else insertCv c y m
    | _ => m) []

/-- Contract's `live`. -/
def live (ks : List Klong) : List (Nat × NodeId) := liveWith (lastBitmapOf ks) ks.zipIdx

/-- Contract's `deadCount`. -/
def deadCount (ks : List Klong) : Nat :=
  let del := lastBitmapOf ks
  (ks.zipIdx.filter (fun (k, i) => match k with
    | .key c _ => del.contains i || (ks.drop (i + 1)).any (fun k' => match k' with
        | .key c' _ => c' == c
        | _ => false)
    | _ => false)).length

/-! ## Keys and operations -/

def segAt (g : Nat) (op : Op) : Nat := (op.key[g]?).getD 0

def endsAt (g : Nat) (op : Op) : Bool := op.key.length == g + 1

def keyOk (cf : Cfg) (k : Key) : Bool := keyWf k && decide (k.length ≤ cf.G + 1)

def opsOk (cf : Cfg) (ops : List Op) : Bool := ops.all (fun op => keyOk cf op.key)

def dropNoops (cf : Cfg) (ops : List Op) : List Op :=
  ops.filter (fun op => match op with
    | .del k => keyOk cf k
    | .put _ _ => true)

/-! ## Lists of entries -/

def renameHead {α : Type} (c : Nat) : List (Nat × α) → List (Nat × α)
  | [] => []
  | (_, y) :: r => (c, y) :: r

def headCv {α : Type} (l : List (Nat × α)) : Nat := (l.head?.map (·.1)).getD 0

def setEntry {α : Type} (c : Nat) (v : α) : List (Nat × α) → List (Nat × α)
  | [] => [(c, v)]
  | (c', v') :: r =>
    if c < c' then (c, v) :: (c', v') :: r
    else if c = c' then (c, v) :: r
    else (c', v') :: setEntry c v r

def removeEntry {α : Type} (c : Nat) (es : List (Nat × α)) : List (Nat × α) :=
  es.filter (fun e => e.1 != c)

def route {α β : Type} (cv : α → Nat) : List (Nat × β) → List α → List (List α)
  | [], _ => []
  | [_], ops => [ops]
  | _ :: (c', y) :: r, ops =>
    ops.filter (fun o => decide (cv o < c')) ::
      route cv ((c', y) :: r) (ops.filter (fun o => decide (c' ≤ cv o)))

def partSizes (n k : Nat) (ceilFirst : Bool) : List Nat :=
  let b := n / k
  let e := n % k
  (List.range k).map (fun j =>
    if ceilFirst then (if j < e then b + 1 else b) else (if k - e ≤ j then b + 1 else b))

def cutList {β : Type} (l : List β) : List Nat → List (List β)
  | [] => []
  | s :: r => l.take s :: cutList (l.drop s) r

def nParts (cap n : Nat) : Nat :=
  let cap := max cap 1
  if n ≤ cap then 1 else (n + cap - 1) / cap

def cutParts (cf : Cfg) (n : Nat) : Nat :=
  if n ≤ cf.h then 1 else max 2 (nParts cf.cap n)

/-! ## The klongs that emit writes -/

def removedCvs {β : Type} (lb : List (Nat × NodeId)) (F : List (Nat × β)) : List Nat :=
  (lb.filter (fun q => !(F.any (fun e => e.1 == q.1)))).map (·.1)

def addedOf (lb F : List (Nat × NodeId)) : List (Nat × NodeId) :=
  F.filter (fun e => lb.lookup e.1 != some e.2)

def bitsIn (ks : List Klong) (R : List Nat) : List Nat :=
  ks.zipIdx.filterMap (fun ki => match ki.1 with
    | .key c _ => if R.contains c then some ki.2 else none
    | _ => none)

/-- PeWriter.lean's `emitBits`, its bits in increasing order without repeats
(`bitsUnion`), as Java's bitmap. -/
def emitBits (ks : List Klong) (R : List Nat) : List Nat := bitsUnion (lastBitmapOf ks) (bitsIn ks R)

def emitHead (i : Time) (ks : List Klong) (R : List Nat) : List Klong :=
  if R.isEmpty then [.time i] else [.time i, .del (emitBits ks R)]

def keysOf (A : List (Nat × NodeId)) : List Klong := A.map (fun e => .key e.1 e.2)

def emitKs (i : Time) (ks : List Klong) (F : List (Nat × NodeId)) : List Klong :=
  emitHead i ks (removedCvs (live ks) F) ++ keysOf (addedOf (live ks) F)

def newKs (i : Time) (F : List (Nat × NodeId)) : List Klong := .time i :: keysOf F

/-! ## The virtual tree -/

inductive Dec where
  | same
  | append
  | parts (k : Nat)
  deriving DecidableEq, Repr, Inhabited

inductive VN where
  | old (y : NodeId)
  | node (base : Option NodeId) (g h : Nat) (join : Bool) (es : List (Nat × VN))
      (F : List (Nat × Option NodeId)) (dec : Dec)
  deriving Inhabited

def partEnts (cv : Nat) (F : List (Nat × Option NodeId)) (k : Nat) (join : Bool) :
    List (Nat × Option NodeId) :=
  match cutList F (partSizes F.length k join) with
  | [] => [(cv, none)]
  | _ :: rest => (cv, none) :: rest.map (fun part => (headCv part, none))

def ents (cv : Nat) : VN → List (Nat × Option NodeId)
  | .old y => [(cv, some y)]
  | .node base _ _ join _ F dec =>
    match dec, base with
    | .parts k, _ => if 2 ≤ k then partEnts cv F k join else [(cv, none)]
    | _, some b => [(cv, some b)]
    | _, none => [(cv, none)]

def VN.size : VN → Nat
  | .old _ => 0
  | .node _ _ _ _ _ F _ => F.length

def VN.isEmpty : VN → Bool
  | .old _ => false
  | .node _ _ _ _ _ F _ => F.isEmpty

def VN.changed : VN → Bool
  | .old _ => false
  | .node _ _ _ _ _ _ dec => dec != .same

def getKey (s : Look) (x : NodeId) : Option PNode := s x

/-! ## The decision of a virtual node -/

def isAdded (lb : List (Nat × NodeId)) (e : Nat × Option NodeId) : Bool :=
  match e.2 with
  | none => true
  | some y => lb.lookup e.1 != some y

def appendKsO (i : Time) (ks : List Klong) (F : List (Nat × Option NodeId)) : List Klong :=
  emitHead i ks (removedCvs (live ks) F) ++
    (F.filter (isAdded (live ks))).map (fun e => .key e.1 (e.2.getD 0))

def deadOver (cf : Cfg) (ks : List Klong) : Bool := cf.theta != 0 && decide (cf.theta < deadCount ks)

def decideNode (cf : Cfg) (i : Time) (base : Option PNode) (join : Bool)
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

def mkNode (cf : Cfg) (i : Time) (s : Look) (base : Option NodeId) (g h : Nat) (join : Bool)
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

def openEs (s : Look) : VN → Option (List (Nat × VN))
  | .old y =>
    match getKey s y with
    | some n => some ((live n.ks).map (fun q => (q.1, VN.old q.2)))
    | none => none
  | .node _ _ _ _ es _ _ => some es

def cntOf (s : Look) : VN → Nat
  | .old y => match getKey s y with
    | some n => (live n.ks).length
    | none => 0
  | v => v.size

def findSmall (cf : Cfg) (es : List (Nat × VN)) : Option Nat :=
  (es.zipIdx.find? (fun p => p.1.2.changed && decide (p.1.2.size < cf.m))).map (·.2)

def joinAt (cf : Cfg) (i : Time) (s : Look) (g h : Nat)
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

def joinLoop (cf : Cfg) (i : Time) (s : Look) (g h : Nat)
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

def rebalance (cf : Cfg) (i : Time) (s : Look) : Nat → Nat → Nat → List (Nat × VN) →
    Option (List (Nat × VN))
  | 0, _, _, _ => none
  | f + 1, g, h, es0 =>
    let es := es0.filter (fun e => !e.2.isEmpty)
    if !cf.merges then some es
    else joinLoop cf i s g h (fun J => rebalance cf i s f g (h - 1) J) (es.length + 1) es

/-! ## Emit -/

/-- The nodes written so far, the latest first, and the next fresh id; and
which rules ran, for the checker's counts (`W.trail`; no rule reads it). -/
structure Acc where
  ws : List (NodeId × Obj)
  next : NodeId
  trail : List String := []
  deriving Inhabited

/-- A fresh id: Java's next vpos (`Db.setIdOfNode`; Exec.lean's `fresh`). -/
def Acc.fresh (a : Acc) : NodeId × Acc := (a.next, { a with next := a.next + 2 })

def Acc.write (a : Acc) (x : NodeId) (o : Obj) : Acc := { a with ws := (x, o) :: a.ws }

def Acc.note (a : Acc) (s : String) : Acc := { a with trail := s :: a.trail }

def newParts (cf : Cfg) (i : Time) (g h : Nat) : List (List (Nat × NodeId)) → Acc →
    List (Nat × NodeId) × Acc
  | [], acc => ([], acc)
  | P :: Ps, acc =>
    let (z, acc) := acc.fresh
    let acc := acc.write z (.key ⟨cf.lev g h, h == 0, newKs i (if h == 0 then P else renameHead 0 P)⟩)
    let (E, acc) := newParts cf i g h Ps acc
    ((headCv P, z) :: E, acc)

mutual

def emit (cf : Cfg) (i : Time) (s : Look) : VN → Acc → Option (List (Nat × NodeId) × Acc)
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
        | some n => some ([(0, b)], (acc.write b (.key { n with ks := n.ks ++ emitKs i n.ks F })).note "pe.append")
        | none => none
      | .parts k, _ =>
        let acc := acc.note (if base.isSome then (if 2 ≤ k then "pe.cut" else "pe.replace")
          else if join then "pe.join" else "pe.new")
        some (newParts cf i g h (cutList F (partSizes F.length k join)) acc)
      | _, none => none

def emitKids (cf : Cfg) (i : Time) (s : Look) : List (Nat × VN) → Acc →
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

def settleRoot (cf : Cfg) (i : Time) (s : Look) : Nat → Nat → VN → Bool → Option (Option VN)
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

def plan (cf : Cfg) (i : Time) (s : Look) : Nat → NodeId → Nat → Nat → List Op → Acc →
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

def planKids (cf : Cfg) (i : Time) (s : Look) : Nat → Nat → Nat → List (Nat × NodeId) →
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

/-- PeWriter.lean's `applyGroups`, and a delete that deletes (the compare value
is in the list) gets a fresh id, for Java's delete node. -/
def applyGroups (cf : Cfg) (i : Time) (s : Look) : Nat → Nat → List (Nat × NodeId) →
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
      | .del _ =>
        if (q.1.lookup cv).isSome then (removeEntry cv q.1, q.2.fresh.2) else q) (es, acc)
    let subs := grp.filter (fun op => !endsAt g op)
    if subs.isEmpty then applyGroups cf i s f g es cvs ops acc
    else
      match planTree cf i s f (es.lookup cv) (g + 1) subs acc with
      | none => none
      | some (some y, acc) => applyGroups cf i s f g (setEntry cv y es) cvs ops acc
      | some (none, acc) => applyGroups cf i s f g (removeEntry cv es) cvs ops acc

def planTree (cf : Cfg) (i : Time) (s : Look) : Nat → Option NodeId → Nat → List Op → Acc →
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

/-! ## The transaction -/

/-- What PE's transaction writes: the nodes, the latest first, each once; the
new space root, if it changed; the next id; the trail. -/
structure Out where
  ws : List (NodeId × Obj)
  root : Option NodeId
  next : NodeId
  trail : List String

def fuel : Nat := 2 ^ 40

/-- PeWriter.lean's `peTx` up to the top: from the space root r of P@(i-1), the
writes, and the new space root if it is not r; the top node is the caller's. -/
def peTx (cf : Cfg) (i : Time) (s : Look) (r : NodeId) (next : NodeId) (ops0 : List Op) :
    Option Out :=
  let ops := dropNoops cf ops0
  if !opsOk cf ops then none else
  match getKey s r with
  | none => none
  | some n =>
    match plan cf i s fuel r 0 (cf.htOf n.level) ops ⟨[], next, []⟩ with
    | none => none
    | some (v, acc) =>
      match settleRoot cf i s fuel 0 v true with
      | some (some rv) =>
        match emit cf i s rv acc with
        | some ([(_, r')], acc) =>
          some ⟨acc.ws, if r' == r then none else some r', acc.next, acc.trail⟩
        | _ => none
      | _ => none

/-! ## The model's writer state -/

/-- The writer state `W` (Exec.lean) of PE's run of transaction i with the
operations `ops` from the first id `base` on P@(i-1) (`view`), so that the tree
checker's checks of `runOps` run unchanged: for each operation whether it is a
noop (a delete of a key with no value at i - 1); the key nodes written, each with
its klongs after the transaction; the nodes made, by id; the values; the top
node, a new one (`Exec.newSuperRoot`'s rules) if the space root changed. -/
def runOps (p : Params) (base : NodeId) (ops : List Op) (i : Time) (view : View BVal) :
    Except String (List Bool × W) :=
  let noops := ops.map (fun op => match op with
    | .del k => (get p view (i - 1) k).isNone
    | .put _ _ => false)
  match lastTop view with
  | none => .error "corrupt: the root has no top node"
  | some z =>
    match topOf p (rootless view) z with
    | .error e => .error e
    | .ok top =>
      let s := lookOf p view
      let cf := Cfg.of p
      match peTx cf i s top.rootKey base ops with
      | none => .error s!"pe: the writer refused transaction {i} (a key the tree cannot hold, a node outside G = {p.G} and H = {p.H}, or a tree that is not one of PE's)"
      | some o =>
        let ws := o.ws.reverse
        let keys := ws.filterMap (fun (x, ob) => match ob with
          | .key n => some (x, n)
          | _ => none)
        let nodes := keys.map (fun (x, n) => (x, (⟨n.leaf, n.ks⟩ : KNode)))
        let gh := keys.map (fun (x, n) => (x, p.segOf n.level, p.heightOf n.level))
        let made := ws.filterMap (fun (x, ob) => match ob with
          | .key n => if (s x).isSome then none else some (⟨x, n.level, false⟩ : NewNode)
          | .val _ => some ⟨x, 0, true⟩)
        let vals := ws.filterMap (fun (x, ob) => match ob with
          | .val h => some (x, h)
          | _ => none)
        let w0 : W := { nodes := nodes, gh := gh, made := made, vals := vals, next := o.next,
                        top := top, trail := o.trail }
        match o.root with
        | none => .ok (noops, w0)
        | some r' =>
          -- `Exec.newSuperRoot`: a new top node, the next ordinal, a skip pointer at each
          -- set bit of the ordinal (the old super root's of that index, or the super root).
          let zt := o.next
          let ord := if top.ord == 0 then 1 else top.ord + 1
          let skips := (List.range (topHeight ord)).filterMap (fun j =>
            if ord.testBit j then
              match top.skips.lookup j with
              | some t => some (j, t)
              | none => some (j, top.id)
            else none)
          .ok (noops, { w0 with next := zt + 2, top := ⟨zt, ord, i, r', skips⟩, newTop := true,
                                made := w0.made ++ [⟨zt, p.topLevel ord, false⟩],
                                trail := "top.new" :: w0.trail })

/-- The tree's `exec` with PE (Spec.lean's `exec`): the changes of transaction tx
at time i from P@(i-1), its touch first. An error gives no change. -/
def exec (p : Params) (tx : Tx) (i : Time) (view : View BVal) : Changes BVal :=
  let touch := touchOf p view (i - 1) tx.touch
  match runOps p tx.base tx.ops i view with
  | .ok (_, w) => { changesOf i w with touch := touch }
  | .error _ => { new := [], adds := [], touch := touch }

end SIS.Tree.Pe
