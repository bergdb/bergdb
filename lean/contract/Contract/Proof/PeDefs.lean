/-
bergdb 030-21: the definitions the proof of PE's writer is about, between the
program (Contract/PeWriter.lean), the abstract tree of lists (PeAbs.lean,
PeAbsOrder.lean, PeAbsRoot.lean: 026-24's relations `Plan`, `Sett`, `Root`)
and the contract's tree.

* `view`: a key node of the tree read as an abstract node of height h, one
  segment's tree: a segment leaf's entries are its live klongs themselves,
  (compare value, the id of a value or of the next segment's root), so that
  keys of several segments are the same recursion once more (the leaves'
  payloads are ids, and what an id holds is read off the tree).
* `Shaped`: the shape that PE keeps and needs (BalancedOK, LeftmostOK, the
  levels of segment g and height h within G and H), through every segment.
* `absV`: a planned virtual node read as an abstract node, each child as
  planned, before any cut (what `rebalance` joins); `fin`: as emit writes it,
  each child cut into its parts.
* `finalOps`: a leaf level's change as operations, one a compare value
  touched: the entry it ends with, or none.
-/
import Contract.Proof.PeAbsRoot
import Contract.Proof.Good
import Contract.PeWriter

namespace Contract.PE

open PeProof PeProof.Abs

/-! ## The parameters -/

/-- The parameters PE's proof needs: a list cut by h, by cap or by c gives
parts that fit a node (at most M - 1 entries and a time klong), and no part
is empty. Java's (`Params.withMerges`: h = c = 17 M / 30) meet them from
M = 2. -/
structure Cfg.Ok (cf : Cfg) : Prop where
  h1 : 1 ≤ cf.h
  hM : cf.h + 1 ≤ cf.M
  cap1 : 1 ≤ cf.cap
  capM : cf.cap + 1 ≤ cf.M
  c1 : 1 ≤ cf.c
  cM : cf.c + 1 ≤ cf.M

/-! ## The tree read as an abstract tree -/

/-- Key node x of the tree s read as an abstract node of height h: its live
klongs, each child read one height down; a segment leaf's entries are its
live klongs (compare value and the id they name). -/
def view : (h : Nat) → Tree → NodeId → Node h
  | 0, s, x => match s.obj x with
    | some (.key n) => live n.ks
    | _ => []
  | h + 1, s, x => match s.obj x with
    | some (.key n) => ofKids ((live n.ks).map (fun cy => (cy.1, view h s cy.2)))
    | _ => []

/-- The height of node y by its level (0 for no key node). -/
def htIn (cf : Cfg) (s : Tree) (y : NodeId) : Nat :=
  match s.obj y with
  | some (.key m) => cf.htOf m.level
  | _ => 0

/-- x is a key node of segment g at height h shaped as PE's trees are: a
segment leaf at height 0, whose long segments name roots of segment g + 1 at the
height their level gives; an inner node above, its first live klong the empty
key, each child one height down; the level of segment g and height h, within
the level bounds G and H. -/
inductive Shaped (cf : Cfg) (s : Tree) : Nat → Nat → NodeId → Prop where
  | leaf {g : Nat} {x : NodeId} {n : KNode} :
      s.obj x = some (.key n) → n.leaf = true → n.level = cf.lev g 0 → g ≤ cf.G →
      (∀ c y, (c, y) ∈ live n.ks → isLong c = true → Shaped cf s (g + 1) (htIn cf s y) y) →
      Shaped cf s g 0 x
  | inner {g h : Nat} {x : NodeId} {n : KNode} :
      s.obj x = some (.key n) → n.leaf = false → n.level = cf.lev g (h + 1) → g ≤ cf.G →
      h + 1 ≤ cf.H → (live n.ks).head?.map (·.1) = some 0 →
      (∀ c y, (c, y) ∈ live n.ks → Shaped cf s g h y) → Shaped cf s g (h + 1) x

/-! ## A planned virtual node read as an abstract node -/

/-- The id of a leaf's payload (an untouched node or value, or a value or a
next segment's root that the transaction made: always `VN.old`). -/
def VN.oid : VN → NodeId
  | .old y => y
  | _ => 0

/-- The height of a virtual node (an untouched one's is not known here: 0). -/
def VN.ht : VN → Nat
  | .old _ => 0
  | .node _ _ h _ _ _ _ => h

/-- A planned virtual node of height h read as an abstract node, each child
as planned, before any cut: an untouched node is its view. -/
def absV (s : Tree) : (h : Nat) → VN → Node h
  | 0, .old y => view 0 s y
  | 0, .node _ _ _ _ es _ _ => es.map (fun e => (e.1, e.2.oid))
  | h + 1, .old y => view (h + 1) s y
  | h + 1, .node _ _ _ _ es _ _ => ofKids (es.map (fun e => (e.1, absV s h e.2)))

/-- The entries a parent of height h + 1 gets for its child (c, v), the
child written as `fv`: one, or one for each of its k parts (k at least 2;
an inner part starts with the empty key). As `newParts` writes them. -/
def finEnts {h : Nat} (c : Nat) (v : VN) (fv : Node h) : List (Nat × Node h) :=
  match v with
  | .node _ _ _ join _ _ (.parts k) =>
    if 2 ≤ k then cutEnts (h != 0) c (cutList fv (partSizes fv.length k join)) else [(c, fv)]
  | _ => [(c, fv)]

/-- A planned virtual node of height h as emit writes it: each child written,
and cut into its parts; the first entry of an inner node the empty key. -/
def fin (s : Tree) : (h : Nat) → VN → Node h
  | 0, v => absV s 0 v
  | h + 1, .old y => view (h + 1) s y
  | h + 1, .node _ _ _ _ es _ _ =>
    ofKids (renameHead 0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2))))

/-! ## A leaf level's change as operations -/

/-- The operations, one for each compare value of T in order, that set each
to the entry it has in the list after, or delete it if it has none. -/
def finalOps (T : List Nat) (after : List (Nat × Nat)) : List Abs.Op :=
  T.map (fun c => match after.lookup c with
    | some y => Abs.Op.put c y
    | none => Abs.Op.del c)

/-- The compare values a segment's operations touch, in the order of their
first operation. -/
def touched (g : Nat) (ops : List Contract.Op) : List Nat := (ops.map (segAt g)).eraseDups

/-! ## The old tree's nodes -/

/-- The nodes reached from node y in the tree s, y first (TREE's list). -/
def R (s : Tree) (y : NodeId) : List NodeId := reachAt s (s.fuel y) y

mutual

/-- The old nodes a virtual node uses above its leaves' payloads: its base,
and every node reached from an untouched child of an inner node (a leaf's
payloads are counted apart, `pays`). -/
def Ui (s : Tree) : VN → List NodeId
  | .old y => R s y
  | .node b _ h _ es _ _ => b.toList ++ (if h == 0 then [] else UiL s es)

/-- `Ui` of a list of entries. -/
def UiL (s : Tree) : List (Nat × VN) → List NodeId
  | [] => []
  | (_, v) :: r => Ui s v ++ UiL s r

end

mutual

/-- The payloads of a virtual node's leaves: each planned leaf's entries,
(compare value, id). -/
def pays : VN → List (Nat × NodeId)
  | .old _ => []
  | .node _ _ h _ es _ _ => if h == 0 then es.map (fun e => (e.1, e.2.oid)) else paysL es

/-- `pays` of a list of entries. -/
def paysL : List (Nat × VN) → List (Nat × NodeId)
  | [] => []
  | (_, v) :: r => pays v ++ paysL r

end

/-- What emit needs of a planned virtual node of segment g at height h, at
every node of it: an untouched node is shaped as PE's trees; a planned node
has its segment and height, its decision is `mkNode`'s for its base and final
list, a base is an old node shaped at its segment and height, a new one is
within the level bounds; an inner node's children each one height down. -/
inductive EOk (cf : Cfg) (i : Time) (s : Tree) (g : Nat) : Nat → VN → Prop where
  | old {h : Nat} {y : NodeId} : Shaped cf s g h y → EOk cf i s g h (.old y)
  | node {h : Nat} {b : Option NodeId} {join : Bool} {es : List (Nat × VN)}
      {F : List (Nat × Option NodeId)} {dec : Dec} :
      dec = decideNode cf i (b.bind (getKey s)) join F →
      (∀ x, b = some x → Shaped cf s g h x) →
      (b = none → g ≤ cf.G ∧ h ≤ cf.H) →
      (∀ e ∈ es, h ≠ 0 → EOk cf i s g (h - 1) e.2) →
      EOk cf i s g h (.node b g h join es F dec)

/-- The old part of a leaf's payload (c, y): the nodes reached from the old
leaf level's entry of c (E, the old content of the segment's tree), if it had
one. -/
def oldPart (s : Tree) (E : List (Nat × NodeId)) (p : Nat × NodeId) : List NodeId :=
  match E.lookup p.1 with
  | some y0 => R s y0
  | none => []

/-! ## What the tree after holds -/

/-- The tree T holds the abstract node A of segment g at height h at node x,
as PE writes it: x is a key node of the level of segment g and height h,
within the level bounds, that meets the rules of one node (`nodeOk`: at most
M klongs, W1 to W4, every pointer to a node of T); a segment leaf's live
klongs are A; an inner node's live klongs have A's compare values, and each
names a node that holds A's child there, one height down. What a leaf's
payloads hold is not part of it. -/
inductive Holds (cf : Cfg) (T : Tree) (g : Nat) : (h : Nat) → NodeId → Node h → Prop where
  | leaf {x : NodeId} {n : KNode} {A : Node 0} :
      T.obj x = some (.key n) → n.leaf = true → n.level = cf.lev g 0 → g ≤ cf.G →
      nodeOk cf.params T n = true → live n.ks = A → Holds cf T g 0 x A
  | inner {h : Nat} {x : NodeId} {n : KNode} {A : Node (h + 1)} :
      T.obj x = some (.key n) → n.leaf = false → n.level = cf.lev g (h + 1) → g ≤ cf.G →
      h + 1 ≤ cf.H → nodeOk cf.params T n = true → (live n.ks).map (·.1) = (kids A).map (·.1) →
      (∀ p ∈ (live n.ks).zip (kids A), Holds cf T g h p.1.2 p.2.2) → Holds cf T g (h + 1) x A

end Contract.PE
