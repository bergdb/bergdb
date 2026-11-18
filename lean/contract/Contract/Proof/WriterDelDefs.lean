/-
The contract package (bergdb 030-16): the statements of the delete's steps
that a node full after a delete (`Dag.handleFullNode` with nothing to insert)
and the bitmap (`Dag.appendDeleteKlong`) are proved by.

A delete changes node x of the key access path: a bitmap that deletes a
compare value, or (LE-b, a merge's parent) pointers set; x is then V, maybe
over the node size. If V does not fit, or holds more than theta dead klongs,
the writer replaces x by its last version `last` (a time klong of i and V's
live klongs), by a time split or a space split, and the parent gets one or two
klongs in turn (`appendKlongs`, the put's recursion: `appendKlongs_spec`).

The form, as the put's (`CasPre`, WriterCascadeDefs.lean): if the state with
x set to V, x then maybe over its size, meets `PInv` and holds the keys C
(`CasPreD`), then the step, where it gives no error and leaves no key node
outside the bounds G and H, ends in a state that meets `PInv` with no node
over its size and holds the keys C (`CasPostD`). Unlike the put's, the state w
itself is given its frame, top and BalancedOK (the put reads them back from
the state with the klongs added; a pointer set is not read back so).
-/
import Contract.Proof.WriterDel

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-- Before `handleFull depth x last compact` of a delete, with x's node n of
the overlay: the path is a path of the tree, in the space root's segment tree;
the books; n is well formed and fits a node; the state w has the map's root,
the frame, the top and BalancedOK; V has x's kind, `last` is V's last version
(a time klong of i, then V's live klongs in order) of x's kind; and the map of
the state with x set to V is sound from the space root with x over its size
(`Sound`, M + 3 klongs), holds the keys C and meets BalancedOK; V starts with a
time klong and has none after i. (Restated at 20:30 from `PInv` of that state:
V need not extend x's node of before the transaction, so that a merge's parent,
which may need four klongs more than a full node, can be given by its last
version.) -/
structure CasPreD (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (w : MW)
    (depth : Nat) (x : NodeId) (n V last : MNode) (C : List (Key × Nat)) : Prop where
  look : w.nodes.lookup x = some n
  on : ∃ c0, w.path[depth]? = some (c0, x)
  path : PathOk i s w depth
  inner : PathInner w depth
  books : PutBooks p i base s w
  wf : klongsWf (ksOf n) = true
  size : n.size ≤ p.M
  wroot : (treeOf i s w).root = some w.top.rootKey
  wframe : Frame i s (dirtyOf w) (treeOf i s w)
  wtop : WTopInv i s tp w.top w.newTop
  wbal : Balanced p (treeOf i s w)
  vleaf : V.leaf = n.leaf
  lastLeaf : last.leaf = n.leaf
  lastKs : ksOf last = Klong.time i :: (live (ksOf V)).map (fun cy => Klong.key cy.1 cy.2)
  vsound : Sound p.M (some x) (treeOf i s (w.withNode x V)) w.top.rootKey C
  vbal : Balanced p (treeOf i s (w.withNode x V))
  vfirst : ∃ t rest, V.ks = SIS.Tree.Klong.time t :: rest
  vtimes : TimesLe V i

/-- After the step: if no key node is outside G and H, the state meets `PInv`
with no node over its size, holds the keys C, and `CascadePost` (from the state
with x set to V). -/
def CasPostD (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (w : MW)
    (depth : Nat) (x : NodeId) (V : MNode) (C : List (Key × Nat)) : Unit → MW → Prop :=
  fun _ w' => w'.outside = [] →
    PInv p i base s tp none C w' ∧ CascadePost i s w (w.withNode x V) w' depth

/-- What a caller of `appendDeleteKlong x depth cv` gives for the node V that
x becomes: the state with x set to V meets `PInv` with x over its size and
holds the keys C, for every V of x's kind whose live klongs are x's but those
of cv, well formed, at most two klongs longer, whose key klongs are x's, with
x's first klong, no time after i, and that extends x's node of before the
transaction by klongs after a time klong of i. -/
def DelVirt (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (w : MW)
    (x : NodeId) (n : MNode) (cv : Nat) (C : List (Key × Nat)) : Prop :=
  ∀ V : MNode, V.leaf = n.leaf → live (ksOf V) = dropCv cv (live (ksOf n)) →
    klongsWf (ksOf V) = true → V.size ≤ n.size + 2 →
    (∀ c y, Klong.key c y ∈ ksOf V → Klong.key c y ∈ ksOf n) →
    V.ks.head? = n.ks.head? → TimesLe V i →
    (∀ n0, s.obj x = some (.key n0) →
      ksOf V = n0.ks ∨ ∃ more, ksOf V = n0.ks ++ Klong.time i :: more) →
    PInv p i base s tp (some x) C (w.withNode x V)

end Contract
