import SIS.Tree.PutInvSpace
import SIS.Tree.GetRootSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A fact of `PutInv` for the splits of the space root, a leaf (bergdb 024-12,
TP10): the time split (a new root holds the last version with the put), the
space split (two halves under a new inner root), and the space split in place
of a root the transaction made (the root keeps the first half). The theorems
that these splits, and so every put of a key of one segment into a space
whose root is a leaf, keep `PutInv`, used by no other, went in bergdb 025-02. -/

/-- No reachable node links to the space root. -/
theorem PutInv.rootFree' {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (x : NodeId) (xn : KNode) (cc : Nat) (hx : ReachS (wNode c.p base w) c.i w.top.rootKey x)
    (hxn : wNode c.p base w x = some xn) (hc : (cc, w.top.rootKey) ∈ xn.liveAt c.i) : False :=
  hI.tree.rootFree x cc (reachS_tReach _ _ _ x hx) ⟨xn, hxn, hc⟩

end SIS.Tree
