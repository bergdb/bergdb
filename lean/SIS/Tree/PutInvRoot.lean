import SIS.Tree.PutInvSpace
import SIS.Tree.GetRootSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the splits of the space root, a leaf (bergdb 024-12,
TP10): the time split (a new root holds the last version with the put), the
space split (two halves under a new inner root), and the space split in place
of a root the transaction made (the root keeps the first half). Together with
the rules of `PutInvRoom.lean` and `PutInvSplit.lean`: every put of a key of
one segment into a space whose root is a leaf keeps `PutInv`
(`putInv_put_leafRoot`, the rules of `writerWP_put_leafRoot`). -/

/-- No reachable node links to the space root. -/
theorem PutInv.rootFree' {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (x : NodeId) (xn : KNode) (cc : Nat) (hx : ReachS (wNode c.p base w) c.i w.top.rootKey x)
    (hxn : wNode c.p base w x = some xn) (hc : (cc, w.top.rootKey) ∈ xn.liveAt c.i) : False :=
  hI.tree.rootFree x cc (reachS_tReach _ _ _ x hx) ⟨xn, hxn, hc⟩

/-! ## The rules -/

end SIS.Tree
