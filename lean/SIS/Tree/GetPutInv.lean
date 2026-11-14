import SIS.Tree.GetLeafBelow

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The invariant of the writer's state that the put rules take (bergdb 024-12,
TP10; `OpGetOK`): the writer's tree (`TreeOK`, cost's `WriterTreeOK`), the
klongs of every key node well formed and of no later time, the ids below the
next one and the next ones fresh in P, the links of the reachable nodes to ids
below the next one, no reachable node taken back, no key node a value, and the
search tree's order below every reachable inner node (`PutInv`). With it, a put
that splits nothing above the key's leaf changes the reading by itself alone:
into a space whose root is a leaf (`writerWP_put_leafRoot_inv`), or into a
leaf below inner nodes with room for two klongs (`writerWP_put_leafBelow_inv`). -/

/-- The search tree's order at an inner node q: the compare values of q's leaf
child L lie between q's klong k1 to L and q's next klong. -/
def LeafOrderAt (q : KNode) (k1 : Nat) (n : KNode) : Prop :=
  ∀ c' z, (c', z) ∈ n.live → k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ q.live → k1 < c'' → c' < c''

structure PutInv (c : Ctx) (base : View BVal) (w : W) : Prop where
  tree : TreeOK (wNode c.p base w) c.i w.top.rootKey
  wf : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true
  times : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i
  ids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
    (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
    (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next
  fresh : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none
  links : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
    wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next
  untaken : ∀ x, ReachS (wNode c.p base w) c.i w.top.rootKey x → w.taken.contains x = false
  keyNoValue : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none
  order : ∀ q qn L n k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
    wNode c.p base w q = some qn → qn.leaf = false → wNode c.p base w L = some n →
    n.leaf = true → (k1, L) ∈ qn.live → LeafOrderAt qn k1 n

end SIS.Tree
