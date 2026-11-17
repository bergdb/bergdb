/-
The contract package (bergdb 030-10): the statement of `handleFullWith` for
any caller: a put (`appendKlongs`: the last version of the node, and klongs
to add) and a delete (`handleFull`: a last version made by the caller, with
the delete's bitmap applied, and no klong to add).

`CasPreH` is `CasPreG` with the node that x would be (`hyp`) and the last
version that the caller gives (`last`) as they are, in place of
`addAll i n ins` and `n.lastVersion i`:

* `hyp` has n's kind and first klong and no time after i; the state with
  `hyp` for x meets `PInv` with x over its size and holds the keys C;
* `last` is a last version of the transaction's time whose key klongs `l`,
  with the klongs `ins` set, are the live klongs of `hyp`;
* the state itself (x as it is) meets the frame and BalancedOK.

For a put: `hyp = addAll i n ins`, `last = n.lastVersion i`, l the live
klongs of n. For a delete of compare value cv: `hyp` is n with the bitmap
added (or set in place), `last = n.lastVersionGivenDel i (delUnion n cv)`,
l the live klongs of n without cv's, `ins = []`.
-/
import Contract.Proof.WriterCascadeDefsG

namespace Contract

open SIS (View)
open SIS.Check (BVal)

structure CasPreH (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (w : MW)
    (depth : Nat) (x : NodeId) (n hyp last : MNode) (ins : List (Nat × NodeId))
    (C : List (Key × Nat)) : Prop where
  look : w.nodes.lookup x = some n
  on : ∃ c0, w.path[depth]? = some (c0, x)
  path : PathOk i s w depth
  nodup : ∀ e e' c c' u, e < e' → e' ≤ depth → w.path[e]? = some (c, u) →
    w.path[e']? = some (c', u) → False
  books : PutBooks p i base s w
  frame : Frame i s (dirtyOf w) (treeOf i s w)
  balanced : Balanced p (treeOf i s w)
  wf : klongsWf (ksOf n) = true
  size : n.size ≤ p.M
  hleaf : hyp.leaf = n.leaf
  hhead : hyp.ks.head? = n.ks.head?
  htimes : TimesLe hyp i
  lastLeaf : last.leaf = n.leaf
  lastKs : ∃ l : List (Nat × NodeId), l.Pairwise CvLt ∧
    ksOf last = Klong.time i :: l.map (fun cy => Klong.key cy.1 cy.2) ∧
    live (ksOf hyp) = ins.foldl (fun m cy => insertCv cy.1 cy.2 m) l ∧
    l.length + 1 ≤ n.size ∧
    ∀ a y1 b y2, ins = [(a, y1), (b, y2)] → a < b ∧ (∃ y, (a, y) ∈ l) ∧
      ∀ c' y', (c', y') ∈ l → a < c' → b < c'
  len : ins.length ≤ 2
  hyp : PInv p i base s tp (some x) C (w.withNode x hyp)

/-- After the step, as `CasPost`, from the state with `hyp` for x. -/
def CasPostH (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (w : MW)
    (depth : Nat) (x : NodeId) (hyp : MNode) (C : List (Key × Nat)) : Unit → MW → Prop :=
  fun _ w' => w'.outside = [] →
    PInv p i base s tp none C w' ∧ CascadePost i s w (w.withNode x hyp) w' depth

end Contract
